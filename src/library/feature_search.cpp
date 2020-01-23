#include "kernel/expr_sets.h"
#include "kernel/instantiate.h"
#include "library/feature_search.h"
#include "library/tactic/tactic_state.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_list.h"
#include <cmath>
#include "library/vm/vm_float.h"
#include "kernel/free_vars.h"
#include "library/constants.h"

namespace lean {

feature_vec isect(feature_vec const & a, feature_vec const & b) {
    std::unordered_set<feature> a_set(a.begin(), a.end());
    feature_vec result;
    for (auto & x : b) if (a_set.count(x)) result.push_back(x);
    return result;
}

feature_vec union_(feature_vec const & a, feature_vec const & b) {
    std::unordered_set<feature> a_set(a.begin(), a.end());
    feature_vec result(a.begin(), a.end());
    for (auto & x : b) if (!a_set.count(x)) result.push_back(x);
    return result;
}

feature_collector::feature_collector(type_context_old & ctx) : m_ctx(ctx) {
    auto i = [&] (name const & n) { m_ignored_consts.insert(n); };
    i({"eq"});
    i({"ne"});
    i({"heq"});
    i({"Exists"});
    i({"iff"});
    i({"not"});
    i({"and"});
    i({"or"});

    auto j = [&] (name const & n) { m_ignored_preds.insert(n); };
    j({"decidable"});
    j({"decidable_eq"});
    j({"decidable_rel"});
}

struct collect_visitor {
    feature_collector & m_collector;
    std::unordered_set<feature> m_feats;
    expr_set m_visited;

    type_context_old & ctx() { return m_collector.m_ctx; }

    bool ignored(name const & n) { return !!m_collector.m_ignored_consts.count(n); }
    bool ignored_pred(name const & n) { return !!m_collector.m_ignored_preds.count(n); }

    void visit_let(expr const & e) {
        visit(let_value(e));
        visit(let_type(e));
        // type_context_old::tmp_locals locals(ctx());
        // expr local = locals.push_local_from_let(e);
        // visit(instantiate(let_body(e), local));
        visit(let_body(e));
    }

    void visit_macro(expr const & e) {
        for (unsigned i = 0; i < macro_num_args(e); i++)
            visit(macro_arg(e, i));
    }

    void visit_pi(expr const & e0) {
        // type_context_old::tmp_locals ls(ctx());
        // expr const *e = &e0;
        // while (is_pi(*e)) {
        //     expr d = instantiate_rev(binding_domain(*e), ls.size(), ls.data());
        //     visit(d);
        //     expr l = ls.push_local(binding_name(*e), d, binding_info(*e));
        //     e = &binding_body(*e);
        // }
        // visit(instantiate_rev(*e, ls.size(), ls.data()));

        if (!has_free_var(binding_body(e0), 0)) {
            // only visit lhs of implications
            visit(binding_domain(e0));
        }
        visit(binding_body(e0));
    }

    void visit_lambda(expr const & e0) {
        // type_context_old::tmp_locals ls(ctx());
        // expr const *e = &e0;
        // while (is_lambda(*e)) {
        //     expr d = instantiate_rev(binding_domain(*e), ls.size(), ls.data());
        //     visit(d);
        //     expr l = ls.push_local(binding_name(*e), d, binding_info(*e));
        //     e = &binding_body(*e);
        // }
        // visit(instantiate_rev(*e, ls.size(), ls.data()));

        visit(binding_domain(e0));
        visit(binding_body(e0));
    }

    void visit_fn(expr const & e) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        optional<name> fn_sym;
        expr fn_ty;
        switch (fn.kind()) {
            case expr_kind::Constant:
                if (ignored_pred(const_name(fn)))
                    return;
                if (!ignored(const_name(fn)))
                    m_feats.insert(feature(const_name(fn)));
                fn_sym = some(const_name(fn));
                fn_ty = ctx().env().get(const_name(fn)).get_type();
                break;
            case expr_kind::Local:
                break;
            case expr_kind::App:
                lean_unreachable();
                break;
            default:
                visit(fn);
        }
        if (args.empty()) return;
        for (size_t i = 0; i < args.size(); i++) {
            if (is_pi(fn_ty)) {
                auto bi = binding_info(fn_ty);
                auto & bd = binding_domain(fn_ty);
                fn_ty = binding_body(fn_ty);
                if (bi.is_inst_implicit()) {
                    // ignore implicit arguments
                    continue;
                }
                if (is_sort(bd) && has_free_var(fn_ty, 0)) {
                    // ignore arguments for type polymorphism
                    continue;
                }
            }
            visit(args[i]);
            if (fn_sym) {
                expr const & arg_fn_sym = get_app_fn(args[i]);
                if (is_constant(arg_fn_sym) &&
                        !ignored(*fn_sym) &&
                        !ignored(const_name(arg_fn_sym))) {
                    m_feats.insert(feature(const_name(arg_fn_sym), *fn_sym));
                }
            }
        }
    }

    void visit(expr const & e) {
        if (m_visited.find(e) != m_visited.end())
            return;
        m_visited.insert(e);
        switch (e.kind()) {
        case expr_kind::Meta:
        case expr_kind::Sort:
            break; /* do nothing */
        case expr_kind::Var:
            break;
            // lean_unreachable();  // LCOV_EXCL_LINE
        case expr_kind::Macro:
            return visit_macro(e);
        case expr_kind::Lambda:
            return visit_lambda(e);
        case expr_kind::Pi:
            return visit_pi(e);
        case expr_kind::Let:
            return visit_let(e);
        case expr_kind::Local:
        case expr_kind::App:
        case expr_kind::Constant:
            return visit_fn(e);
        }
    }

    collect_visitor(feature_collector & coll) : m_collector(coll) {}

    feature_vec to_vector() {
        return std::vector<feature>(m_feats.begin(), m_feats.end());
    }
};

feature_vec feature_collector::operator()(expr const & thm) {
    collect_visitor collector(*this);
    collector.visit(thm);
    return collector.to_vector();
}

feature_vec feature_vec_of(type_context_old & ctx, expr const & e) {
    feature_collector collector(ctx);
    return collector(e);
}

void feature_stats::add(feature_vec const & fv) {
    m_thms++;
    for (auto & feat : fv) {
        m_feature_counts[feat] += 1;
    }
}

float feature_stats::idf(feature const & f) const {
    auto it = m_feature_counts.find(f);
    unsigned num_thms = 1 + (it == m_feature_counts.end() ? 0 : it->second);
    return log(m_thms / float(num_thms));
}

float feature_stats::norm(feature_vec const & a) const {
    float sq_norm = 0;
    for (auto & f : a) {
        float idf_ = idf(f);
        sq_norm += idf_ * idf_;
    }
    return sqrt(sq_norm);
}

float feature_stats::dotp(feature_vec const & a, feature_vec const & b) const {
    float dotp = 0;
    std::unordered_set<feature> b_feats(b.begin(), b.end());
    for (auto & f : a) {
        if (b_feats.count(f)) {
            auto idf_ = idf(f);
            dotp += idf_ * idf_;
        }
    }
    return dotp;
}

float feature_stats::cosine_similarity(feature_vec const & a, feature_vec const & b) const {
    return dotp(a,b) / norm(a) / norm(b);
}

vm_obj to_obj(feature const & f) {
    if (f.m_parent) {
        return mk_vm_constructor(1, to_obj(*f.m_parent), to_obj(f.m_name));
    } else {
        return mk_vm_constructor(0, to_obj(f.m_name));
    }
}

feature to_feature(vm_obj const & o) {
    if (cidx(o) == 0) {
        return feature(to_name(cfield(o, 0)));
    } else {
        return feature(to_name(cfield(o, 1)), to_name(cfield(o, 0)));
    }
}

define_vm_external(feature_vec)

static vm_obj feature_vec_isect(vm_obj const & a_, vm_obj const & b_) {
    return to_obj(isect(to_feature_vec(a_), to_feature_vec(b_)));
}

static vm_obj feature_vec_union(vm_obj const & a_, vm_obj const & b_) {
    return to_obj(union_(to_feature_vec(a_), to_feature_vec(b_)));
}

static vm_obj feature_vec_of_expr(vm_obj const & e_, vm_obj const & s_) {
    auto & s = tactic::to_state(s_);
    type_context_old ctx = mk_type_context_for(s);
    auto & e = to_expr(e_);
    auto fv = feature_vec_of(ctx, e);
    return tactic::mk_success(to_obj(std::move(fv)), s);
}

static vm_obj feature_vec_of_exprs(vm_obj const & es_, vm_obj const & s_) {
    auto & s = tactic::to_state(s_);
    type_context_old ctx = mk_type_context_for(s);
    feature_collector collector(ctx);

    buffer<vm_obj> fvs;
    vm_obj const * iter = &es_;
    while (!is_nil(*iter)) {
        expr const & e = to_expr(cfield(*iter, 0));
        fvs.push_back(to_obj(collector(e)));
        iter = &cfield(*iter, 1);
    }

    return tactic::mk_success(to_obj(fvs), s);
}

static vm_obj feature_vec_to_list(vm_obj const & fv_) {
    auto & fv = to_feature_vec(fv_);
    buffer<vm_obj> feats;
    for (auto & f : fv) feats.push_back(to_obj(f));
    return to_obj(feats);
}

define_vm_external(feature_stats)

static vm_obj feature_stats_of_feature_vecs(vm_obj const & fvs_) {
    feature_stats stats;
    vm_obj const * iter = &fvs_;
    while (!is_nil(*iter)) {
        feature_vec const & fv = to_feature_vec(cfield(*iter, 0));
        stats.add(fv);
        iter = &cfield(*iter, 1);
    }
    return to_obj(std::move(stats));
}

static vm_obj feature_stats_idf(vm_obj const & fs_, vm_obj const & f_) {
    return to_obj(to_feature_stats(fs_).idf(to_feature(f_)));
}

static vm_obj feature_stats_dotp(vm_obj const & fs_, vm_obj const & fv1_, vm_obj const & fv2_) {
    return to_obj(to_feature_stats(fs_).dotp(to_feature_vec(fv1_), to_feature_vec(fv2_)));
}

static vm_obj feature_stats_norm(vm_obj const & fs_, vm_obj const & fv_) {
    return to_obj(to_feature_stats(fs_).norm(to_feature_vec(fv_)));
}

static vm_obj feature_stats_cosine_similarity(vm_obj const & fs_, vm_obj const & fv1_, vm_obj const & fv2_) {
    return to_obj(to_feature_stats(fs_).cosine_similarity(to_feature_vec(fv1_), to_feature_vec(fv2_)));
}

static vm_obj feature_stats_features(vm_obj const & fs_) {
    buffer<vm_obj> feats;
    auto & fs = to_feature_stats(fs_);
    for (auto & entry : fs.m_feature_counts) {
        feats.push_back(to_obj(entry.first));
    }
    return to_obj(feats);
}

void initialize_feature_search() {
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_vec", "of_expr"}), feature_vec_of_expr);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_vec", "of_exprs"}), feature_vec_of_exprs);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_vec", "to_list"}), feature_vec_to_list);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_vec", "isect"}), feature_vec_isect);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_vec", "union"}), feature_vec_union);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_stats", "of_feature_vecs"}), feature_stats_of_feature_vecs);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_stats", "idf"}), feature_stats_idf);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_stats", "dotp"}), feature_stats_dotp);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_stats", "norm"}), feature_stats_norm);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_stats", "cosine_similarity"}), feature_stats_cosine_similarity);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_stats", "features"}), feature_stats_features);
}

void finalize_feature_search() {}

}
