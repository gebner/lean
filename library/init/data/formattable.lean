/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.string.basic init.data.bool.basic init.data.subtype.basic
import init.data.unsigned.basic init.data.prod init.data.sum.basic init.data.nat.div
import init.coe

universes u v

namespace nat

def digit_char (n : ℕ) : char :=
if n = 0 then '0' else
if n = 1 then '1' else
if n = 2 then '2' else
if n = 3 then '3' else
if n = 4 then '4' else
if n = 5 then '5' else
if n = 6 then '6' else
if n = 7 then '7' else
if n = 8 then '8' else
if n = 9 then '9' else
if n = 0xa then 'a' else
if n = 0xb then 'b' else
if n = 0xc then 'c' else
if n = 0xd then 'd' else
if n = 0xe then 'e' else
if n = 0xf then 'f' else
'*'

def digit_succ (base : ℕ) : list ℕ → list ℕ
| [] := [1]
| (d::ds) :=
    if d+1 = base then
        0 :: digit_succ ds
    else
        (d+1) :: ds

def to_digits (base : ℕ) : ℕ → list ℕ
| 0 := [0]
| (n+1) := digit_succ base (to_digits n)

protected def repr (n : ℕ) : string :=
((to_digits 10 n).map digit_char).reverse.as_string

end nat

class formattable (α : Type u) extends has_append α :=
(of_string' : string → α)
(line' : α := of_string' "\n")
(of_nat' : ℕ → α := λ i, of_string' i.repr)
(nest : ℕ → α → α := λ _, id)
(group : α → α := id)

instance : formattable string :=
{ of_string' := id, append := (++) }

namespace formattable
variables {α : Type u} [formattable α]

def of_nat (n : ℕ) : α :=
of_nat' _ n

instance lift_from_nat : has_lift ℕ α :=
⟨of_nat⟩

def of_string (s : string) : α :=
of_string' _ s

instance lift_from_string : has_lift string α :=
⟨of_string⟩

instance : inhabited α :=
⟨↑""⟩

def line : α :=
line' _

def space : α :=
↑" "

def indent (a : α) (i : ℕ) : α :=
nest i (line ++ a)

def join (xs : list α) : α :=
xs.foldl (++) ↑""

def bracket : string → string → α → α
| o c f := ↑o ++ nest (utf8_length o) f ++ ↑c

def paren (f : α) : α :=
bracket "(" ")" f

def cbrace (f : α) : α :=
bracket "{" "}" f

def sbracket (f : α) : α :=
bracket "[" "]" f

def dcbrace (f : α) : α :=
↑"⦃" ++ nest 1 f ++ ↑"⦄"

end formattable