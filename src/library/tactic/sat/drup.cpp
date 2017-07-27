/*
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/tactic/sat/drup.h"
#include "library/util.h"
#include "library/kernel_serializer.h"
#include "library/constants.h"
#include "library/type_context.h"
#include "library/app_builder.h"
#include "util/fresh_name.h"

#define LEAN_DRUP_MACROS_TRUST_LEVEL 1024

namespace lean {

static name * g_drup_proof_name = nullptr;
static std::string * g_drup_proof_opcode = nullptr;

template <class T>
void remove_in_place(list<T> & l, T const & a) {
    l = remove(l, a);
}

template <class T>
void cons_in_place(list<T> & l, T const & a) {
    l = cons(a, l);
}

struct drup_replayer {
    drup_replayer(type_context & ctx, std::vector<expr> const & vars,
            bool proofs = true) :
        m_ctx(ctx), m_vars(vars), m_num_vars(vars.size()), m_proofs(proofs),
        m_assignment(m_num_vars+1), m_assignment_proofs(m_num_vars+1),
        m_watchers(m_num_vars+1) {}

    optional<expr> const & is_inconsistent() {
        return m_inconsistent;
    }

    void add_input_clause(sat_clause const & cls, expr const & proof) {
        unsigned cidx = m_clauses.size();
        m_clauses.push_back(cls);
        m_clause_proofs.push_back(proof);
        m_watched.push_back({0,0});
        if (propagate_clause(cidx) && cls.size() >= 2) {
            m_watched[cidx] = {cls[0], cls[1]};
            cons_in_place(m_watchers[var_of_lit(cls[0])], cidx);
            cons_in_place(m_watchers[var_of_lit(cls[1])], cidx);
        }
        propagation_loop();
    }

    void add_rup_clause(sat_clause const & cls) {
        if (m_inconsistent) return;
            
        // std::cerr << "rup:"; print_clause(cls);print_state();

        unsigned trail_base = m_trail.size();

        type_context::tmp_locals locals(m_ctx);
        for (auto lit : cls) {
            auto & var = m_vars[var_of_lit(lit)-1];
            auto local = locals.push_local("h",
                lit >= 0 ? mk_not(m_ctx, var) : var,
                binder_info());
            assign(-lit, local);
        }
        propagation_loop();
        // print_state();
        undo_trail(trail_base);

        if (!m_inconsistent) {
            lean_assert(false);
            throw exception("clause is not rup");
        }
        auto pr = *m_inconsistent;
        m_inconsistent = none_expr();

        pr = m_proofs ? locals.mk_lambda(pr) : expr();
        add_input_clause(cls, pr);
    }

private:

    type_context & m_ctx;
    bool m_proofs;
    
    std::vector<expr> const & m_vars;
    unsigned m_num_vars;

    optional<expr> m_inconsistent;

    std::vector<sat_lit> m_trail;
    unsigned m_trail_propagated = 0;

    std::vector<lbool> m_assignment;
    std::vector<expr> m_assignment_proofs;

    std::vector<sat_clause> m_clauses;
    std::vector<expr> m_clause_proofs;
    std::vector<pair<sat_lit, sat_lit>> m_watched;

    std::vector<list<unsigned>> m_watchers;

    sat_lit var_of_lit(sat_lit lit) const {
        return lit >= 0 ? lit : -lit;
    }

    lbool eval(sat_lit lit) {
        return lit >= 0 ? m_assignment[lit] : ~m_assignment[-lit];
    }

    expr expr_of_lit(sat_lit lit) const {
        return lit >= 0 ? m_vars[lit-1] :
            mk_not(m_ctx, m_vars[-lit-1]);
    }

    void undo_trail(unsigned trail_idx) {
        lean_assert(trail_idx <= m_trail.size());
        while (trail_idx < m_trail.size()) {
            m_assignment[var_of_lit(m_trail.back())] = l_undef;
            m_trail.pop_back();
        }
        m_trail_propagated = trail_idx;
    }

    expr mk_false_propagation(unsigned cidx) {
        if (!m_proofs) return expr();
        auto & cls = m_clauses[cidx];
        auto proof = m_clause_proofs[cidx];
        for (auto lit : cls) {
            lean_assert(m_assignment_proofs[var_of_lit(lit)] != expr());
            proof = mk_app(proof, m_assignment_proofs[var_of_lit(lit)]);
        }
        return proof;
    }
    expr mk_unit_propagation(unsigned cidx, sat_lit lit) {
        if (!m_proofs) return expr();
        auto & cls = m_clauses[cidx];
        auto proof = m_clause_proofs[cidx];
        for (unsigned i = 0; i < cls.size(); i++) {
            if (cls[i] == lit) {
                proof = mk_app(proof, mk_var(0));
            } else {
                lean_assert(m_assignment_proofs[var_of_lit(cls[i])] != expr());
                proof = mk_app(proof, m_assignment_proofs[var_of_lit(cls[i])]);
            }
        }
        proof = mk_lambda("h", expr_of_lit(-lit), proof);
        if (lit >= 0) {
            proof = mk_app(m_ctx, get_classical_by_contradiction_name(), {proof});
        }
        return proof;
    }

    bool propagate_clause(unsigned idx) {
        pair<sat_lit, sat_lit> watched_lits;
        auto & cls = m_clauses[idx];
        for (unsigned i = 0; i < cls.size(); i++) {
            auto val = eval(cls[i]);
            if (val == l_true) return true;
            if (val == l_undef) {
                if (watched_lits.first) {
                    watched_lits.second = cls[i];
                    break;
                } else {
                    watched_lits.first = cls[i];
                }
            }
        }
        // print_clause(cls);
        // std::cerr << watched_lits.first << " " << watched_lits.second << std::endl;
        if (!watched_lits.first) {
            m_inconsistent = mk_false_propagation(idx);
            return true;
        } else if (!watched_lits.second) {
            assign(watched_lits.first,
                mk_unit_propagation(idx, watched_lits.first));
            return true;
        } else {
            auto old_watched = m_watched[idx];
            remove_in_place(m_watchers[var_of_lit(old_watched.first)], idx);
            remove_in_place(m_watchers[var_of_lit(old_watched.second)], idx);
            cons_in_place(m_watchers[var_of_lit(watched_lits.first)], idx);
            cons_in_place(m_watchers[var_of_lit(watched_lits.second)], idx);
            m_watched[idx] = watched_lits;
            return false;
        }
    }

    void propagation_loop() {
        while (!m_inconsistent && m_trail_propagated < m_trail.size()) {
            propagate_core(m_trail[m_trail_propagated]);
            m_trail_propagated++;
        }
    }

    void assign(sat_lit lit, expr const & proof) {
        lean_assert(lit);
        lean_assert(proof);
        sat_lit var = var_of_lit(lit);
        lbool phase = lit >= 0 ? l_true : l_false;

        switch (eval(lit)) {
            case l_true: return;
            case l_false: {
                auto a = proof, b = m_assignment_proofs[var];
                lean_assert(b != expr());
                if (phase == l_true) std::swap(a, b);
                m_inconsistent = some_expr(mk_app(a, b));
                return;
            }
            case l_undef: {
                m_trail.push_back(lit);
                m_assignment[var] = phase;
                m_assignment_proofs[var] = proof;
                break;
            }
        }
    }

    void propagate_core(sat_lit lit) {
        sat_lit var = var_of_lit(lit);
        auto ws = m_watchers[var];
        for (auto cls_idx : ws) {
            // std::cerr << "propagate " << cls_idx; print_clause(m_clauses[cls_idx]);
            propagate_clause(cls_idx);
        }
    }

    void print_clause(sat_clause const & cls) const;
    void print_state() const;
};

void drup_replayer::print_clause(sat_clause const & cls) const {
    for (auto lit : cls) {
        std::cerr << " " << lit;
    }
    std::cerr << " 0\n";
}

void drup_replayer::print_state() const {
    std::cerr << "vars:\n";
    for (unsigned i = 0; i < m_num_vars; i++) {
        std::cerr << " " << i+1 << " (" << m_vars[i] << ") := " << m_assignment[i+1]
            << " " << m_watchers[i+1] << "\n";
    }
    std::cerr << std::endl;

    std::cerr << "trail:";
    for (auto l : m_trail) {
        std::cerr << " " << l;
    }
    std::cerr << "\n" << std::endl;

    std::cerr << "clauses:\n";
    for (unsigned i = 0; i < m_clauses.size(); i++) {
        auto & cls = m_clauses[i];
        auto & w = m_watched[i];
        std::cerr << "[" << w.first << "," << w.second << "] ";
        print_clause(cls);
    }
    std::cerr << std::endl;
}

static expr expand_drup_macro(expr const & e, bool create_proof);

struct drup_proof_macro_cell : public macro_definition_cell {
    unsigned m_num_vars;
    drup_proof m_refutation;

    drup_proof_macro_cell(unsigned num_vars, drup_proof && refutation) :
        m_num_vars(num_vars), m_refutation(refutation) {}

    virtual name get_name() const { return *g_drup_proof_name; }
    
    virtual expr check_type(expr const & e, abstract_type_context & ctx, bool) const {
        // TODO(gabriel)
        return mk_false();
    }

    virtual unsigned trust_level() const {
        return LEAN_DRUP_MACROS_TRUST_LEVEL;
    }

    virtual optional<expr> expand(expr const & e, abstract_type_context & ctx) const;

    virtual void write(serializer & s) const {
        s.write_string(*g_drup_proof_opcode);
        s << m_num_vars << m_refutation;
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<drup_proof_macro_cell const *>(&other)) {
            // different refutation are equal
            return m_num_vars == other_ptr->m_num_vars;
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return m_num_vars;
    }
};

expr mk_drup_proof_macro(std::vector<expr> && vars,
        std::vector<expr> && proofs_of_clauses,
        drup_proof && refutation) {
    macro_definition m(new drup_proof_macro_cell(vars.size(), std::move(refutation)));

    std::vector<expr> macro_args;
    for (auto & v : vars) macro_args.push_back(v);
    for (auto & p : proofs_of_clauses) macro_args.push_back(p);

    return mk_macro(m, macro_args.size(), macro_args.data());
}

static drup_proof_macro_cell const * get_drup_proof_macro_cell(expr const & e) {
    if (!is_macro(e)) return nullptr;
    return dynamic_cast<drup_proof_macro_cell const *>(macro_def(e).raw());
}

bool is_drup_proof_macro(expr const & e) {
    return !!get_drup_proof_macro_cell(e);
}

std::vector<expr> drup_proof_vars(expr const & e) {
    std::vector<expr> vars;
    auto cell = get_drup_proof_macro_cell(e);
    lean_assert(cell);
    unsigned num_vars = cell->m_num_vars;
    lean_assert(macro_num_args(e) >= num_vars);
    for (unsigned i = 0; i < num_vars; i++)
        vars.push_back(macro_arg(e, i));
    return vars;
}

std::vector<expr> drup_proof_clauses(expr const & e) {
    std::vector<expr> clauses;
    auto cell = get_drup_proof_macro_cell(e);
    lean_assert(cell);
    unsigned num_vars = cell->m_num_vars;
    unsigned num_args = macro_num_args(e);
    lean_assert(num_args >= num_vars);
    for (unsigned i = num_vars; i < num_args; i++)
        clauses.push_back(macro_arg(e, i));
    return clauses;
}

drup_proof const & drup_proof_refutation(expr const & e) {
    auto cell = get_drup_proof_macro_cell(e);
    lean_assert(cell);
    return cell->m_refutation;
}
    
static expr expand_drup_macro(expr const & e, bool create_proof) {
    auto vars = drup_proof_vars(e);

    std::unordered_map<expr, sat_lit, expr_hash> var2idx;
    for (unsigned i = 0; i < vars.size(); i++) {
        var2idx[vars[i]] = i + 1;
    }

    auto parse_cls = [&] (expr const & cls_proof) -> sat_clause {
        sat_clause res;
        expr cls = ctx.whnf(ctx.infer(cls_proof));
        while (is_pi(cls)) {
            auto lit = binding_domain(cls);
            cls = binding_body(cls);
            lean_assert(closed(cls));
            cls = ctx.whnf(cls);

            expr var = lit;
            if (is_not(lit, var)) {
                res.push_back(var2idx.at(var));
            } else {
                res.push_back(-var2idx.at(var));
            }
        }
        lean_assert(is_false(cls));
        return res;
    };

    type_context tc(ctx.env(), options(), create_proof);
    drup_replayer replayer(tc, vars);
    for (auto cls : drup_proof_clauses(e)) {
        replayer.add_input_clause(parse_cls(cls), cls);
    }
    for (auto cls : drup_proof_refutation(e)) {
        if (!cls.m_is_drop) {
            replayer.add_rup_clause(cls.m_cls);
        }
    }

    if (!replayer.is_inconsistent()) {
        throw exception("invalid drup proof");
    }

    return *replayer.is_inconsistent();
}

serializer & operator<<(serializer & s, drup_proof const & pr) {
    s << static_cast<unsigned>(pr.size());
    for (auto & cls : pr) {
        s << cls.m_is_drop;
        for (auto & l : cls.m_cls) {
            lean_assert(l != 0);
            s << l;
        }
        s << static_cast<sat_lit>(0);
    }
    return s;
}

deserializer & operator>>(deserializer & d, drup_proof & pr) {
    unsigned sz; d >> sz;
    pr.resize(sz);
    for (unsigned i = 0; i < sz; i++) {
        drup_proof_line & cls = pr[i];
        d >> cls.m_is_drop;

        sat_lit l;
        while (true) {
            d >> l;
            if (l == 0) {
                break;
            } else {
                cls.m_cls.push_back(l);
            }
        }
    }
    return d;
}

void initialize_drup() {
    g_drup_proof_name = new name("drup_proof");
    g_drup_proof_opcode = new std::string("DrupProof");
    register_macro_deserializer(*g_drup_proof_opcode,
        [] (deserializer & d, unsigned num, expr const * args) {
            unsigned num_vars; drup_proof refutation;
            d >> num_vars >> refutation;
            lean_assert(num_vars <= num);
            macro_definition m(new drup_proof_macro_cell(
                num_vars, std::move(refutation)));
            return mk_macro(m, num, args);
        }
    );
}
void finalize_drup() {
    delete g_drup_proof_name;
    delete g_drup_proof_opcode;
}

}