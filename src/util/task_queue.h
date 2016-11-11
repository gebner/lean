/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <sstream>
#include <string>
#include <vector>
#include <unordered_set>
#include "util/thread.h"
#include "util/optional.h"

namespace lean {

struct task_priority {
    task_priority() {}
    task_priority(unsigned prio) : m_prio(prio) {}

    unsigned m_prio = static_cast<unsigned>(-1);
    optional<chrono::steady_clock::time_point> m_not_before;

    static const unsigned
        ROI_PARSING_PRIO = 10,
        ROI_PRINT_PRIO = 11,
        ROI_ELAB_PRIO = 13,
        PARSING_PRIO = 20,
        PRINT_PRIO = 21,
        ELAB_PRIO = 23;
};

enum class task_result_state { QUEUED, EXECUTING, FINISHED, CANCELLED, FAILED };

class generic_task;
class generic_task_result_cell {
    friend class task_queue;
    friend class st_task_queue;
    friend class mt_task_queue;
    template <class T> friend class task_result_cell;

    generic_task * m_task = nullptr;
    atomic<task_result_state> m_state { task_result_state::QUEUED };
    std::string m_desc;
    std::exception_ptr m_ex;

    virtual ~generic_task_result_cell() { dealloc(); }
    void dealloc();

    generic_task_result_cell(generic_task * t);
    generic_task_result_cell(std::string const & desc) :
            m_state(task_result_state::FINISHED), m_desc(desc) {}

    bool has_evaluated() const {
        auto state = m_state.load();
        return state != task_result_state::QUEUED && state != task_result_state::EXECUTING;
    }

    virtual bool execute() = 0;

public:
    std::string description() const { return m_desc; }
    void cancel();
};

using generic_task_result = std::shared_ptr<generic_task_result_cell>;

class generic_task {
    friend class task_queue;
    friend class st_task_queue;
    friend class mt_task_queue;

    task_priority m_prio;
    std::vector<generic_task_result> m_reverse_deps;
    condition_variable m_has_finished;

public:
    generic_task(task_priority const & prio) : m_prio(prio) {}
    virtual ~generic_task() {}
    virtual void description(std::ostream &) const = 0;
    std::string description() const;
    virtual std::vector<generic_task_result> get_dependencies() { return {}; }
};

template <class T>
class task : public generic_task {
public:
    typedef T result;

    task(task_priority const & prio) : generic_task(prio) {}
    virtual ~task() {}

    virtual T execute() = 0;
};

template <class T>
class task_result_cell : public generic_task_result_cell {
    friend class task_queue;

    optional<T> m_result;

    task<T> * get_ptr() { return static_cast<task<T> *>(m_task); }

    virtual bool execute() {
        try {
            m_result = { get_ptr()->execute() };
            return true;
        } catch (...) {
            m_ex = std::current_exception();
            return false;
        }
    }

public:
    task_result_cell(task<T> * t) : generic_task_result_cell(t) {}
    task_result_cell(T const & t, std::string const & desc) :
            generic_task_result_cell(desc), m_result(t) {}
    T get();

    optional<T> peek() const {
        if (m_state.load() == task_result_state::FINISHED) {
            return m_result;
        } else {
            return optional<T>();
        }
    }
};

template <class T>
using task_result = std::shared_ptr<task_result_cell<T>>;

template <typename T>
task_result<T> mk_pure_task_result(T const & t, std::string const & desc) {
    return std::make_shared<task_result_cell<T>>(t, desc);
}

class task_queue {
    virtual void submit(generic_task_result const &) = 0;

protected:
    task_queue() {}

public:
    virtual ~task_queue() {}

    virtual optional<generic_task_result> get_current_task() = 0;
    virtual bool empty() = 0;

    template <typename T, typename... As>
    task_result<typename T::result> submit(As... args) {
        task_result<typename T::result> task =
                std::make_shared<task_result_cell<typename T::result>>(
                        new T(std::forward<As>(args)...));
        submit(task);
        return task;
    }

    template <typename T>
    T get_result(task_result_cell<T> * t) {
        wait(t);
        lean_assert(t->m_result);
        return *t->m_result;
    }

    virtual void wait(generic_task_result_cell * t) = 0;
    void wait(generic_task_result const & t) { wait(t.get()); }

    virtual void cancel(generic_task_result_cell * t) = 0;
    void cancel(generic_task_result const & t) { cancel(t.get()); }
};

class scope_global_task_queue {
    task_queue * m_old_tq;
public:
    scope_global_task_queue(task_queue * tq);
    ~scope_global_task_queue();
};
task_queue & get_global_task_queue();

template <class T>
T task_result_cell<T>::get() {
    return get_global_task_queue().get_result(this);
}

inline void generic_task_result_cell::cancel() {
    get_global_task_queue().cancel(this);
}

}
