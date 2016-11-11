/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include "util/mt_task_queue.h"

#if defined(LEAN_MULTI_THREAD)
namespace lean {

LEAN_THREAD_PTR(generic_task_result_cell, g_current_task);
struct scoped_current_task {
    generic_task_result_cell * m_old;
    scoped_current_task(generic_task_result_cell * t) :
            m_old(g_current_task) {
        g_current_task = t;
    }
    ~scoped_current_task() {
        g_current_task = m_old;
    }
};

template <class T>
struct scoped_add {
    T & m_ref;
    T m_delta;
    scoped_add(T & ref, T delta) : m_ref(ref), m_delta(delta) {
        m_ref += m_delta;
    }
    ~scoped_add() {
        m_ref -= m_delta;
    }
};

mt_task_queue::mt_task_queue(unsigned num_workers) : m_required_workers(num_workers) {
    for (unsigned i = 0; i < num_workers; i++)
        spawn_worker();
}

mt_task_queue::~mt_task_queue() {
    {
        unique_lock<mutex> lock(m_mutex);
        m_queue_removed.wait(lock, [=] { return m_queue.empty(); });
        m_shutting_down = true;
        m_queue_added.notify_all();
        m_wake_up_worker.notify_all();
    }
    for (auto & w : m_workers) w->m_thread.join();
}

void mt_task_queue::spawn_worker() {
    lean_assert(!m_shutting_down);
    auto this_worker = std::make_shared<worker_info>();
    this_worker->m_thread = thread([=] {
        scope_global_task_queue scope(this);
        unique_lock<mutex> lock(m_mutex);
        scoped_add<int> dec_required(m_required_workers, -1);
        while (true) {
            if (m_shutting_down) return;
            if (m_required_workers < 0) {
                scoped_add<int> inc_required(m_required_workers, +1);
                scoped_add<unsigned> inc_sleeping(m_sleeping_workers, +1);
                m_wake_up_worker.wait(lock);
                continue;
            }
            if (m_queue.empty()) {
                m_queue_added.wait(lock);
                continue;
            }

            this_worker->m_current_task = dequeue();

            auto & t = this_worker->m_current_task;

            if (t->m_state.load() != task_result_state::QUEUED) continue;

            t->m_state = task_result_state::EXECUTING;
            bool is_ok;
            {
                scoped_current_task scope_cur_task(t.get());
                lock.unlock();
                is_ok = t->execute();
                lock.lock();
            }

            t->m_state = is_ok ? task_result_state::FINISHED : task_result_state::FAILED;
            t->m_task->m_has_finished.notify_all();

            if (t->m_state.load() == task_result_state::FINISHED) {
                for (auto & rdep : t->m_task->m_reverse_deps) {
                    if (rdep->has_evaluated()) {
                        m_waiting.erase(rdep);
                    } else {
                        if (m_waiting.count(rdep) && check_deps(rdep)) {
                            m_waiting.erase(rdep);
                            if (!rdep->has_evaluated()) {
                                enqueue(rdep);
                            }
                        }
                    }
                }
            } else {
                propagate_failure(t);
            }

            t->dealloc();
            this_worker->m_current_task.reset();
        }
    });
    m_workers.push_back(this_worker);
}

void mt_task_queue::propagate_failure(generic_task_result const & tr) {
    lean_assert(tr->m_state.load() == task_result_state::FAILED);

    if (auto t = tr->m_task) {
        tr->m_task->m_has_finished.notify_all();

        for (auto & rdep : t->m_reverse_deps) {
            if (rdep->m_state.load() != task_result_state::QUEUED) continue;
            rdep->m_ex = tr->m_ex;
            rdep->m_state = task_result_state::FAILED;
            m_waiting.erase(rdep);
            propagate_failure(rdep);
        }
    }

    tr->dealloc();
}

void mt_task_queue::submit(generic_task_result const & t) {
    unique_lock<mutex> lock(m_mutex);
    if (check_deps(t)) {
        if (!t->has_evaluated()) enqueue(t);
    } else {
        m_waiting.insert(t);
    }
}

bool mt_task_queue::check_deps(generic_task_result const & t) {
    auto deps = t->m_task->get_dependencies();
    for (auto & dep : deps) {
        if (!dep) continue;
        switch (dep->m_state.load()) {
            case task_result_state::QUEUED:
            case task_result_state::EXECUTING:
                dep->m_task->m_reverse_deps.push_back(t);
                return false;
            case task_result_state::FINISHED:
                break;
            case task_result_state::CANCELLED:
                t->m_ex = std::make_exception_ptr(exception("dependency canceled: " + dep->m_desc));
                t->m_state = task_result_state::FAILED;
                propagate_failure(t);
                return true;
            case task_result_state::FAILED:
                t->m_ex = dep->m_ex;
                t->m_state = task_result_state::FAILED;
                propagate_failure(t);
                return true;
        }
    }
    return true;
}

void mt_task_queue::wait(generic_task_result_cell * t) {
    if (!t) return;
    unique_lock<mutex> lock(m_mutex);
    while (!t->has_evaluated()) {
        if (g_current_task) {
            scoped_add<int> inc_required(m_required_workers, +1);
            if (m_sleeping_workers == 0) {
                spawn_worker();
            } else {
                m_wake_up_worker.notify_one();
            }
        }
        t->m_task->m_has_finished.wait(lock);
    }
    switch (t->m_state.load()) {
        case task_result_state::FAILED: std::rethrow_exception(t->m_ex);
        case task_result_state::FINISHED: return;
        case task_result_state::CANCELLED: throw exception("waited-for task canceled: " + t->m_desc);
        default: throw exception("invalid task state");
    }
}

void mt_task_queue::cancel(generic_task_result_cell * t) {
    if (!t) return;
    unique_lock<mutex> lock(m_mutex);
    switch (t->m_state.load()) {
        case task_result_state::QUEUED:
            t->m_state.store(task_result_state::CANCELLED);
            if (t->m_task) t->m_task->m_has_finished.notify_all();
            // TODO(gabriel): propagate eagerly
            t->dealloc();
            return;
        default: return;
    }
}

bool mt_task_queue::empty() {
    unique_lock<mutex> lock(m_mutex);
    for (auto & w : m_workers) {
        if (w->m_current_task)
            return false;
    }
    return m_queue.empty();
}

optional<generic_task_result> mt_task_queue::get_current_task() {
    unique_lock<mutex> lock(m_mutex);
    for (auto & w : m_workers) {
        if (w->m_current_task) {
            return optional<generic_task_result>(w->m_current_task);
        }
    }
    return optional<generic_task_result>();
}

generic_task_result mt_task_queue::dequeue() {
    lean_assert(!m_queue.empty());
    auto & highest_prio = m_queue.begin()->second;
    lean_assert(!highest_prio.empty());
    auto result = std::move(highest_prio.front());
    highest_prio.pop_front();
    if (highest_prio.empty()) {
        m_queue.erase(m_queue.begin());
    }
    m_queue_removed.notify_all();
    return result;
}

void mt_task_queue::enqueue(generic_task_result const & t) {
    lean_assert(t->m_state.load() == task_result_state::QUEUED);
    lean_assert(t->m_task);
    m_queue[t->m_task->m_prio.m_prio].push_back(t);
    m_queue_added.notify_one();
}

}
#endif
