/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include "util/task_queue.h"

namespace lean {

std::string generic_task::description() const {
    std::ostringstream out;
    description(out);
    return out.str();
}

generic_task_result_cell::generic_task_result_cell(generic_task * t) :
        m_task(t), m_desc(t->description()) {}

void generic_task_result_cell::dealloc() {
    if (m_task) {
        delete m_task;
        m_task = nullptr;
    }
}

LEAN_THREAD_PTR(task_queue, g_tq);
scope_global_task_queue::scope_global_task_queue(task_queue * tq) {
    m_old_tq = g_tq;
    g_tq = tq;
}
scope_global_task_queue::~scope_global_task_queue() {
    g_tq = m_old_tq;
}
task_queue & get_global_task_queue() {
    return *g_tq;
}

}
