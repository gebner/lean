/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.string.basic init.data.bool.basic init.data.subtype.basic
import init.data.unsigned.basic init.data.prod init.data.sum.basic init.data.nat.div
import init.data.repr
open sum subtype nat

universes u v w

section

class has_to_fmt (γ : Type w) (α : Type u) :=
(to_fmt : α → γ)

variables {γ : Type w} [formattable γ]

def to_fmt {α : Type u} [has_to_fmt γ α] : α → γ :=
has_to_fmt.to_fmt _

def to_string {α : Type u} [has_to_fmt string α] : α → string :=
to_fmt

instance has_to_fmt.id : has_to_fmt γ γ :=
⟨id⟩

instance : has_to_fmt γ string :=
⟨λ s, ↑s⟩

instance : has_to_fmt γ bool :=
⟨λ b, cond b ↑"tt" ↑"ff"⟩

instance {p : Prop} : has_to_fmt γ (decidable p) :=
-- Remark: type class inference will not consider local instance `b` in the new elaborator
⟨λ b : decidable p, @ite p b _ ↑"tt" ↑"ff"⟩

protected def list.to_string_aux {α : Type u} [has_to_fmt γ α] : bool → list α → γ
| b  []      := ↑""
| tt (x::xs) := to_fmt x ++ list.to_string_aux ff xs
| ff (x::xs) := ↑", " ++ to_fmt x ++ list.to_string_aux ff xs

protected def list.to_string {α : Type u} [has_to_fmt γ α] : list α → γ
| []      := ↑"[]"
| (x::xs) := ↑"[" ++ list.to_string_aux tt (x::xs) ++ ↑"]"

instance has_to_fmt_list {α : Type u} [has_to_fmt γ α] : has_to_fmt γ (list α) :=
⟨list.to_string⟩

instance : has_to_fmt γ unit :=
⟨λ u, ↑"()"⟩

instance : has_to_fmt γ nat :=
⟨λ n, formattable.of_nat n⟩

instance : has_to_fmt γ char :=
⟨λ c, ↑c.to_string⟩

instance (n : nat) : has_to_fmt γ (fin n) :=
⟨λ f, to_fmt (fin.val f)⟩

instance : has_to_fmt γ unsigned :=
⟨λ n, to_fmt (fin.val n)⟩

instance {α : Type u} [has_to_fmt γ α] : has_to_fmt γ (option α) :=
⟨λ o, match o with | none := to_fmt "none" | (some a) := to_fmt "(some " ++ to_fmt a ++ to_fmt ")" end⟩

instance {α : Type u} {β : Type v} [has_to_fmt γ α] [has_to_fmt γ β] : has_to_fmt γ (α ⊕ β) :=
⟨λ s, match s with | (inl a) := to_fmt "(inl " ++ to_fmt a ++ ↑")" | (inr b) := to_fmt "(inr " ++ to_fmt b ++ to_fmt ")" end⟩

instance {α : Type u} {β : Type v} [has_to_fmt γ α] [has_to_fmt γ β] : has_to_fmt γ (α × β) :=
⟨λ ⟨a, b⟩, to_fmt "(" ++ to_fmt a ++ ↑", " ++ to_fmt b ++ ↑")"⟩

instance {α : Type u} {β : α → Type v} [has_to_fmt γ α] [s : ∀ x, has_to_fmt γ (β x)] : has_to_fmt γ (sigma β) :=
⟨λ ⟨a, b⟩, ↑"⟨"  ++ to_fmt a ++ ↑", " ++ to_fmt b ++ ↑"⟩"⟩

instance {α : Type u} {p : α → Prop} [has_to_fmt γ α] : has_to_fmt γ (subtype p) :=
⟨λ s, to_fmt (val s)⟩

end