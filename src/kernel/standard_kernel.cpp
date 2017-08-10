/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/inductive/inductive.h"
#include "kernel/computation/computation.h"

namespace lean {
using inductive::inductive_normalizer_extension;

/** \brief Create standard Lean environment */
environment mk_environment(unsigned trust_lvl) {
    return environment(trust_lvl,
                       /* builtin support for inductive */
                       compose(std::unique_ptr<normalizer_extension>(new inductive_normalizer_extension()),
                               std::unique_ptr<normalizer_extension>(new computation_normalizer_extension())));
}
}
