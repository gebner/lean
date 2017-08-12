/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, Gabriel Ebner

Support for user-defined computation rules.
*/
#include "kernel/computation/computation.h"
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/abstract_type_context.h"
#include "kernel/inductive/inductive.h"
#include <vector>

namespace lean {
static name * g_computation_rule_name = nullptr;

computation_rule::computation_rule(buffer<expr> const & locals,
        expr const & lhs, expr const & rhs) {
    m_packed = mk_app(mk_constant(*g_computation_rule_name), {lhs, rhs});
    for (unsigned i = locals.size(); i > 0;) {
        i--;
        m_packed = mk_pi(mlocal_pp_name(locals[i]), mlocal_type(locals[i]), m_packed);
    }
}

void computation_rule::validate(environment const & env) const {
    // TODO(gabriel)
}

static bool mtch(expr const & a, expr const & b, buffer<expr> & s, name_map<level> & ls) {
    if (is_var(a)) {
        s[var_idx(a)] = b;
        return true;
    } else if (is_app(a) && is_app(b)) {
        return mtch(app_fn(a), app_fn(b), s, ls)
            && mtch(app_arg(a), app_arg(b), s, ls);
    } else if (is_constant(a)) {
        if (!is_constant(b)) return false;
        if (const_name(a) != const_name(b)) return false;
        auto al = const_levels(a), bl = const_levels(b);
        for (; al && bl; al = tail(al), bl = tail(bl)) {
            if (!is_param(head(al))) return false;
            ls.insert(param_id(head(al)), head(bl));
        }
        return !al == !bl;
    } else {
        return false;
    }
}

static expr instantiate_univ_params(expr const & e, name_map<level> subst) {
    level_param_names ps; levels ls;
    subst.for_each([&] (name const & p, level const & l) {
        ps = cons(p, ps);
        ls = cons(l, ls);
    });
    return instantiate_univ_params(e, ps, ls);
}

optional<expr> computation_rule::match(expr const & e) const {
    buffer<expr> args;
    auto fn = get_app_args(e, args);
    return match(fn, args);
}

optional<expr> computation_rule::match(expr const & fn, buffer<expr> const & args) const {
    auto eqn = m_packed;
    unsigned num_vars = 0;
    for (; is_pi(eqn); num_vars++) eqn = binding_body(eqn);
    auto & lhs = app_arg(app_fn(eqn));
    auto & rhs = app_arg(eqn);

    buffer<expr> lhs_args;
    auto lhs_fn = get_app_args(lhs, lhs_args);

    if (args.size() < lhs_args.size()) return none_expr();

    buffer<expr> subst; subst.resize(num_vars, {});
    name_map<level> lsubst;

    if (!mtch(lhs_fn, fn, subst, lsubst)) return none_expr();
    for (unsigned i = 0; i < lhs_args.size(); i++) {
        if (!mtch(lhs_args[i], args[i], subst, lsubst)) return none_expr();
    }

    auto res = instantiate_univ_params(rhs, lsubst);
    res = instantiate(res, subst.size(), subst.data());
    for (unsigned i = lhs_args.size(); i < args.size(); i++) {
        res = mk_app(res, args[i]);
    }

    return some_expr(res);
}

optional<unsigned> computation_rule::get_major_premise() const {
    auto e = m_packed;
    while (is_pi(e)) e = binding_body(e);
    auto & lhs = app_arg(app_fn(e));
    buffer<expr> as; get_app_args(lhs, as);
    for (unsigned i = 0; i < as.size(); i++) {
        if (!is_var(as[i])) {
            return optional<unsigned>(i);
        }
    }
    return optional<unsigned>();
}

name computation_rule::get_head_symbol() const {
    auto e = m_packed;
    while (is_pi(e)) e = binding_body(e);
    return const_name(get_app_fn(app_arg(app_fn(e))));
}

static name * g_computation_extension = nullptr;

struct computation_env_ext : public environment_extension {
    name_map<list<pair<name, computation_rule>>> m_head_map;
    computation_env_ext() {}
};

/** \brief Auxiliary object for registering the environment extension */
struct computation_env_ext_reg {
    unsigned m_ext_id;
    computation_env_ext_reg() {
        m_ext_id = environment::register_extension(std::make_shared<computation_env_ext>());
    }
};

static computation_env_ext_reg * g_ext = nullptr;

/** \brief Retrieve environment extension */
static computation_env_ext const & get_extension(environment const & env) {
    return static_cast<computation_env_ext const &>(env.get_extension(g_ext->m_ext_id));
}

/** \brief Update environment extension */
static environment update(environment const & env, computation_env_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<computation_env_ext>(ext));
}

environment declare_computation_rule(environment const & env, name const & n, computation_rule const & c) {
    c.validate(env);

    computation_env_ext ext = get_extension(env);
    auto head = c.get_head_symbol();
    list<pair<name, computation_rule>> rules;
    if (auto existing = ext.m_head_map.find(head)) {
        rules = *existing;
    }
    ext.m_head_map.insert(head, cons(mk_pair(n, c), rules));

    return update(env, ext);
}

list<name> get_computation_rules(environment const & env) {
    list<name> rules;
    get_extension(env).m_head_map.for_each(
        [&] (name const &, list<pair<name, computation_rule>> rs) {
            for (auto & r : rs) {
                rules = cons(r.first, rules);
            }
        });
    return rules;
}

list<name> get_computation_rules_for(environment const & env, name const & head) {
    list<name> rules;
    if (auto rs = get_extension(env).m_head_map.find(head)) {
        for (auto & r : *rs) {
            rules = cons(r.first, rules);
        }
    }
    return rules;
}

computation_rule get_computation_rule(environment const & env, name const & n) {
    optional<computation_rule> rule;
    get_extension(env).m_head_map.for_each(
        [&] (name const &, list<pair<name, computation_rule>> rs) {
            for (auto & r : rs) {
                if (r.first == n) {
                    rule = optional<computation_rule>(r.second);
                }
            }
        });
    return *rule;
}

optional<expr> computation_normalizer_extension::operator()(expr const & e, abstract_type_context & ctx) const {
    buffer<expr> args;
    auto & fn = get_app_args(e, args);
    if (!is_constant(fn)) return none_expr();
    auto & env = ctx.env();
    if (auto rules = get_extension(env).m_head_map.find(const_name(fn))) {
        for (auto & r : *rules) {
            if (auto major = r.second.get_major_premise()) {
                args[*major] = ctx.whnf(args[*major]);
            }
            if (auto red = r.second.match(fn, args)) {
                return red;
            }
        }
    }
    return none_expr();
}

optional<expr> computation_normalizer_extension::is_stuck(expr const & e, abstract_type_context & ctx) const {
    auto & fn = get_app_fn(e);
    if (!is_constant(fn)) return none_expr();

    buffer<expr> args;
    get_app_args(e, args);
    computation_env_ext const & ext = get_extension(ctx.env());
    if (auto rules = ext.m_head_map.find(const_name(fn))) {
        for (auto & r : *rules) {
            if (auto maj = r.second.get_major_premise()) {
                if (*maj < args.size()) {
                    expr whnf_arg = ctx.whnf(args[*maj]);
                    if (auto stuck = ctx.is_stuck(whnf_arg)) {
                        return stuck;
                    }
                }
            }
        }
    }
    return none_expr();
}

bool computation_normalizer_extension::supports(name const & feature) const {
    return feature == *g_computation_extension;
}

bool computation_normalizer_extension::is_recursor(environment const & env, name const & n) const {
    return get_extension(env).m_head_map.contains(n);
}

bool computation_normalizer_extension::is_builtin(environment const &, name const &) const {
    return false;
}

void initialize_computation_module() {
    g_computation_rule_name = new name("_computation_rule");
    g_computation_extension = new name("computation_extension");
    g_ext = new computation_env_ext_reg();
}

void finalize_computation_module() {
    delete g_ext;
    delete g_computation_extension;
    delete g_computation_rule_name;
}
}
