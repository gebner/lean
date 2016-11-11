/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "util/st_task_queue.h"

namespace lean {

st_task_queue::st_task_queue() {}

void st_task_queue::wait(generic_task_result_cell *) {} // NOLINT

bool st_task_queue::empty() {
    return true;
}

optional<generic_task_result> st_task_queue::get_current_task() {
    return optional<generic_task_result>();
}

void st_task_queue::submit(generic_task_result const & t) {
#if defined(LEAN_EMSCRIPTEN)
    std::cout << "running task: " << t->description() << std::endl;
#endif
    bool is_ok = t->execute();
    t->m_state = is_ok ? task_result_state::FINISHED : task_result_state::FAILED;
    t->dealloc();
}

void st_task_queue::cancel(generic_task_result_cell *) {} // NOLINT

}
