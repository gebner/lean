/*
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/tactic/sat/drup.h"
#include "library/util.h"
#include "library/kernel_serializer.h"

#define LEAN_DRUP_MACROS_TRUST_LEVEL 1024

namespace lean {

static name * g_drup_proof_name = nullptr;
static std::string * g_drup_proof_opcode = nullptr;

struct drup_replayer {
    drup_replayer(unsigned m_num_vars) :
        m_assignment(m_num_vars), m_assignment_proofs(m_num_vars) {}

    optional<expr> m_inconsistent;

    std::vector<sat_lit> m_trail;
    unsigned m_trail_propagated = 0;

    std::vector<lbool> m_assignment;
    std::vector<expr> m_assignment_proofs;

    std::vector<sat_clause> m_clauses;
    std::vector<expr> m_clause_proofs;
    std::vector<pair<sat_lit, sat_lit>> m_watched;
    std::vector<list<unsigned>> m_watchers;

    // std::vector<pair<expr, expr>> m_

    void propagate_clause(unsigned idx) {
        pair<sat_lit, sat_lit> watched_lits;
        auto & cls = m_clauses[idx];
        for (unsigned i = 0; i < cls.size(); i++) {
            if (m_assignment[cls[i]]);
        }
    }

    void assign(sat_lit lit, expr const & proof) {
        sat_lit var = std::abs(lit);
        lbool phase = lit > 0 ? l_true : l_false;

        if (m_assignment[var] == -phase) {
            auto a = proof, b = m_assignment_proofs[var];
            if (phase == l_true) std::swap(a, b);
            m_inconsistent = some_expr(mk_app(a, b));
        } else {
            m_assignment[var] = phase;
            m_assignment_proofs[var] = proof;
        }
    }

    void propagate_core(sat_lit lit) {
        sat_lit var = std::abs(lit);

        list<unsigned> ws;
        std::swap(ws, m_watchers[var]);
        for (auto cls_idx : ws) {
            propagate_clause(cls_idx);
        }
    }
};

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

    virtual optional<expr> expand(expr const & e, abstract_type_context & ctx) const {
        // TODO(gabriel)
        return none_expr();
    }

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
    for (unsigned i = 0; i < sz; i++) {
        drup_proof_line cls;
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

}