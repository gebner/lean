/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <sstream>
#include "util/test.h"
#include "util/rb_map.h"
#include "util/name.h"
#include "util/init_module.h"
using namespace lean;
typedef rb_map<int, name, int_cmp> int2name;

static void tst0() {
    int2name m1;
    m1[10] = name("t1");
    m1[20] = name("t2");
    int2name m2(m1);
    m2[10] = name("t3");
    lean_assert(m1[10] == name("t1"));
    lean_assert(m1[20] == name("t2"));
    lean_assert(m2[10] == name("t3"));
    lean_assert(m2[20] == name("t2"));
    lean_assert(m2.size() == 2);
    lean_assert(m2[100] == name());
    lean_assert(m2.size() == 3);
    lean_assert(m2[100] == name());
    lean_assert(m2.size() == 3);
}

static void tst1() {
    int2name m1, m2;
    m1[10] = name("t1");
    lean_assert(m1.size() == 1);
    lean_assert(m2.size() == 0);
    swap(m1, m2);
    lean_assert(m2.size() == 1);
    lean_assert(m1.size() == 0);
}

static void tst2() {
    int2name m1;
    m1.insert(1, name{"p", "v1"});
    m1.insert(2, name("v2"));
    m1.insert(3, name{"p", "v3"});
    m1.insert(4, name("v4"));
    auto pred = [](int, name const & v) { return !v.is_atomic() && v.get_prefix() == "p"; };
    lean_assert(*m1.find_if(pred) == name({"p", "v1"}));
    lean_assert(*m1.back_find_if(pred) == name({"p", "v3"}));
}

int main() {
    initialize_util_module();
    tst0();
    tst1();
    tst2();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
