/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/head_map.h"
#include "library/explicit.h"
#include "library/typed_expr.h"

namespace lean {
head_index::head_index(expr e) {
    while (true) {
        m_num_args += get_app_num_args(e);
        e = get_app_fn(e);
        if (is_as_atomic(e))
            e = get_as_atomic_arg(e);
        else if (is_explicit(e))
            e = get_explicit_arg(e);
        else if (is_typed_expr(e))
            e = get_typed_expr_expr(e);
        else
            break;
    }
    m_kind = e.kind();
    if (is_constant(e))
        m_name = const_name(e);
    else if (is_local(e))
        m_name = mlocal_name(e);
}

int head_index::cmp::operator()(head_index const & i1, head_index const & i2) const {
    if (i1.m_kind != i2.m_kind || (i1.m_kind != expr_kind::Constant && i1.m_kind != expr_kind::Local))
        return static_cast<int>(i1.m_kind) - static_cast<int>(i2.m_kind);
    else
        return quick_cmp(i1.m_name, i2.m_name);
}

std::ostream & operator<<(std::ostream & out, head_index const & head_idx) {
    if (head_idx.m_kind == expr_kind::Constant || head_idx.m_kind == expr_kind::Local)
        out << head_idx.m_name;
    else
        out << head_idx.m_kind;
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, head_index const & head_idx) {
    return display(out, head_idx);
}
}
