/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <deque>
#include <string>
#include <vector>
#include <unordered_set>
#include <map>
#include "util/optional.h"
#include "util/task_queue.h"

namespace lean {

#if defined(LEAN_MULTI_THREAD)
class mt_task_queue : public task_queue {
    mutex m_mutex;
    std::map<unsigned, std::deque<generic_task_result>> m_queue;
    std::unordered_set<generic_task_result> m_waiting;
    condition_variable m_queue_added, m_queue_removed;

    struct worker_info {
        thread m_thread;
        generic_task_result m_current_task;
    };
    std::vector<std::shared_ptr<worker_info>> m_workers;
    bool m_shutting_down = false;
    void spawn_worker();

    unsigned m_sleeping_workers = 0;
    int m_required_workers;
    condition_variable m_wake_up_worker;

    generic_task_result dequeue();
    void enqueue(generic_task_result const &);

    bool check_deps(generic_task_result const &);
    void propagate_failure(generic_task_result const &);
    void submit(generic_task_result const &) override;

public:
    mt_task_queue(unsigned num_workers);
    ~mt_task_queue();

    optional<generic_task_result> get_current_task() override;
    bool empty() override;

    void wait(generic_task_result_cell * t) override;
    void cancel(generic_task_result_cell * t) override;
};
#endif

}
