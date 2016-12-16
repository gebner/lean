/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.fin.basic

open nat
def unsigned_sz : nat := succ 4294967295

attribute [reducible]
def unsigned := fin unsigned_sz

namespace unsigned
/- We cannot use tactic dec_trivial here because the tactic framework has not been defined yet. -/
private lemma zero_lt_unsigned_sz : 0 < unsigned_sz :=
zero_lt_succ _

def of_nat (n : nat) : unsigned :=
if h : n < unsigned_sz then fin.mk n h else fin.mk 0 zero_lt_unsigned_sz

def to_nat (c : unsigned) : nat :=
fin.val c

def succ (i : unsigned) :=
of_nat i^.to_nat^.succ

end unsigned

instance : has_zero unsigned := ⟨unsigned.of_nat 0⟩

instance : decidable_eq unsigned :=
have decidable_eq (fin unsigned_sz), from fin.decidable_eq _,
this
