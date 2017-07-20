/*
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <vector>
#include "library/type_context.h"

namespace lean {

using sat_lit = int;
using sat_clause = std::vector<sat_lit>;

struct drup_proof_line {
    bool m_is_drop = false;
    sat_clause m_cls;
};
using drup_proof = std::vector<drup_proof_line>;

expr mk_drup_proof_macro(std::vector<expr> && vars,
    std::vector<expr> && proofs_of_clauses,
    drup_proof && refutation);
bool is_drup_proof_macro(expr const &);
std::vector<expr> drup_proof_vars(expr const &);
std::vector<expr> drup_proof_clauses(expr const &);
drup_proof const & drup_proof_refutation(expr const &);

serializer & operator<<(serializer &, drup_proof const &);
deserializer & operator>>(deserializer &, drup_proof &);

}