/*
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <memory>
#include <vector>
#include "util/rc.h"
#include "kernel/expr.h"
#include "library/tactic/sat/drup.h"

namespace Minisat {
class Solver;
}

namespace lean {

class sat_state {
    std::unique_ptr<Minisat::Solver> m_solver;
    list<expr> m_asserted_clauses;
    drup_proof m_drup_proof;

public:
    sat_state();
    ~sat_state();
};

}