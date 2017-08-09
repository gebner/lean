/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, Gabriel Ebner

Support for user-defined computation rules.
*/
#pragma once
#include "kernel/normalizer_extension.h"
#include <vector>

namespace lean {
/** \brief Normalizer extension to apply user-defined computation rules. */
class computation_normalizer_extension : public normalizer_extension {
public:
    virtual optional<expr> operator()(expr const & e, abstract_type_context & ctx) const;
    virtual optional<expr> is_stuck(expr const & e, abstract_type_context & ctx) const;
    virtual bool supports(name const & feature) const;
    virtual bool is_recursor(environment const & env, name const & n) const;
    virtual bool is_builtin(environment const & env, name const & n) const;
};

struct computation_rule {
    expr m_packed;

    computation_rule(expr const & packed) : m_packed(packed) {}
    computation_rule(buffer<expr> const & locals,
        expr const & lhs, expr const & rhs);

    void validate(environment const & env) const;
    name get_head_symbol() const;
    optional<expr> match(expr const & e) const;

    optional<unsigned> get_major_premise() const;
};

environment declare_computation_rule(environment const & env, name const & n,
    computation_rule const &);
list<name> get_computation_rules(environment const & env);
list<name> get_computation_rules_for(environment const & env, name const & head);
computation_rule get_computation_rule(environment const & env, name const & n);

void initialize_computation_module();
void finalize_computation_module();
}
