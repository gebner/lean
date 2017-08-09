/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Quotient types.
-/
prelude
/- We import propext here, otherwise we would need a quot.lift for propositions. -/
import init.data.sigma.basic init.logic init.propext init.data.setoid

universes u v

-- iff can now be used to do substitutions in a calculation
attribute [subst]
lemma iff_subst {a b : Prop} {p : Prop → Prop} (h₁ : a ↔ b) (h₂ : p a) : p b :=
eq.subst (propext h₁) h₂

constant quotient {α : Sort u} (s : setoid α) : Sort u
protected constant quotient.mk {α : Sort u} [s : setoid α] : α → quotient s
protected axiom quotient.sound : ∀ {α : Sort u} [s : setoid α] {a b : α}, a ≈ b → quotient.mk a = quotient.mk b
protected constant quotient.rec {α : Sort u} [s : setoid α] {β : quotient s → Sort v}
    (f : ∀ a, β (quotient.mk a)) (h : ∀ a b, ∀ hs: a ≈ b, f a == f b) : ∀ q, β q

computation_rule quotient.comp_rule {α : Sort u} (a : α) [s : setoid α] {β : quotient s → Sort v}
    (f : ∀ a, β (quotient.mk a)) (h) : quotient.rec f h (quotient.mk a) = f a

attribute [elab_as_eliminator] quotient.rec

private def quotient.impl (α : Sort u) [setoid α] : Sort u := α
private def quotient.impl.mk {α : Sort u} [setoid α] : α → quotient.impl α := id
private def quotient.impl.rec {α : Sort u} [setoid α] {β : quotient.impl α → Sort v}
    (f : ∀ a, β (quotient.impl.mk a))
    (h : ∀ a b, ∀ hs : a ≈ b, f a == f b) : ∀ q, β q := f

unsafe_make_computable quotient.mk quotient.impl.mk
unsafe_make_computable quotient.rec quotient.impl.rec

namespace quotient

notation `⟦`:max a `⟧`:0 := quotient.mk a

attribute [reducible, elab_as_eliminator]
protected def lift {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) : (∀ a b, a ≈ b → f a = f b) → quotient s → β
| h q := quotient.rec f (λ a b hs, heq_of_eq (h a b hs)) q

attribute [elab_as_eliminator]
protected lemma ind {α : Sort u} [s : setoid α] {β : quotient s → Prop} : (∀ a, β ⟦a⟧) → ∀ q, β q
| h q := quotient.rec h (λ a b hs, heq_of_eq_rec_left (quotient.sound hs) rfl) q

attribute [reducible, elab_as_eliminator]
protected def lift_on {α : Sort u} {β : Sort v} [s : setoid α] (q : quotient s) (f : α → β) (c : ∀ a b, a ≈ b → f a = f b) : β :=
quotient.lift f c q

attribute [elab_as_eliminator]
protected lemma induction_on {α : Sort u} [s : setoid α] {β : quotient s → Prop} (q : quotient s) (h : ∀ a, β ⟦a⟧) : β q :=
quotient.ind h q

lemma exists_rep {α : Sort u} [s : setoid α] (q : quotient s) : ∃ a : α, ⟦a⟧ = q :=
quotient.induction_on q (λ a, ⟨a, rfl⟩)

section
variable {α : Sort u}
variable [s : setoid α]
variable {β : quotient s → Sort v}

attribute [reducible, elab_as_eliminator]
protected def rec_on
   (q : quotient s) (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : a ≈ b), f a == f b) : β q :=
quotient.rec f h q

attribute [reducible, elab_as_eliminator]
protected def rec_on_subsingleton
   [h : ∀ a, subsingleton (β ⟦a⟧)] (q : quotient s) (f : Π a, β ⟦a⟧) : β q :=
quotient.rec_on q f (λ a b hs, subsingleton.helim (quotient.sound hs ▸ rfl) _ _)

end

section
universes u_a u_b u_c
variables {α : Sort u_a} {β : Sort u_b} {φ : Sort u_c}
variables [s₁ : setoid α] [s₂ : setoid β]
include s₁ s₂

attribute [reducible, elab_as_eliminator]
protected def lift₂
   (f : α → β → φ)(c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
   (q₁ : quotient s₁) (q₂ : quotient s₂) : φ :=
quotient.lift
  (λ (a₁ : α), quotient.lift (f a₁) (λ (a b : β), c a₁ a a₁ b (setoid.refl a₁)) q₂)
  (λ (a b : α) (h : a ≈ b),
     @quotient.ind β s₂
       (λ (a_1 : quotient _),
          (quotient.lift (f a) (λ (a_1 b : β), c a a_1 a b (setoid.refl a)) a_1)
          =
          (quotient.lift (f b) (λ (a b_1 : β), c b a b b_1 (setoid.refl b)) a_1))
       (λ (a' : β), c a a' b a' h (setoid.refl a'))
       q₂)
  q₁

attribute [reducible, elab_as_eliminator]
protected def lift_on₂
  (q₁ : quotient s₁) (q₂ : quotient s₂) (f : α → β → φ) (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) : φ :=
quotient.lift₂ f c q₁ q₂

attribute [elab_as_eliminator]
protected lemma ind₂ {φ : quotient s₁ → quotient s₂ → Prop} (h : ∀ a b, φ ⟦a⟧ ⟦b⟧) (q₁ : quotient s₁) (q₂ : quotient s₂) : φ q₁ q₂ :=
quotient.ind (λ a₁, quotient.ind (λ a₂, h a₁ a₂) q₂) q₁

attribute [elab_as_eliminator]
protected lemma induction_on₂
   {φ : quotient s₁ → quotient s₂ → Prop} (q₁ : quotient s₁) (q₂ : quotient s₂) (h : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
quotient.ind (λ a₁, quotient.ind (λ a₂, h a₁ a₂) q₂) q₁

attribute [elab_as_eliminator]
protected lemma induction_on₃
   [s₃ : setoid φ]
   {δ : quotient s₁ → quotient s₂ → quotient s₃ → Prop} (q₁ : quotient s₁) (q₂ : quotient s₂) (q₃ : quotient s₃) (h : ∀ a b c, δ ⟦a⟧ ⟦b⟧ ⟦c⟧)
   : δ q₁ q₂ q₃ :=
quotient.ind (λ a₁, quotient.ind (λ a₂, quotient.ind (λ a₃, h a₁ a₂ a₃) q₃) q₂) q₁
end

section exact
variable   {α : Sort u}
variable   [s : setoid α]
include s

private def rel (q₁ q₂ : quotient s) : Prop :=
quotient.lift_on₂ q₁ q₂
  (λ a₁ a₂, a₁ ≈ a₂)
  (λ a₁ a₂ b₁ b₂ a₁b₁ a₂b₂,
    propext (iff.intro
      (λ a₁a₂, setoid.trans (setoid.symm a₁b₁) (setoid.trans a₁a₂ a₂b₂))
      (λ b₁b₂, setoid.trans a₁b₁ (setoid.trans b₁b₂ (setoid.symm a₂b₂)))))

local infix `~` := rel

private lemma rel.refl : ∀ q : quotient s, q ~ q :=
λ q, quotient.induction_on q (λ a, setoid.refl a)

private lemma eq_imp_rel {q₁ q₂ : quotient s} : q₁ = q₂ → q₁ ~ q₂ :=
assume h, eq.rec_on h (rel.refl q₁)

lemma exact {a b : α} : ⟦a⟧ = ⟦b⟧ → a ≈ b :=
assume h, eq_imp_rel h
end exact

section
universes u_a u_b u_c
variables {α : Sort u_a} {β : Sort u_b}
variables [s₁ : setoid α] [s₂ : setoid β]
include s₁ s₂

attribute [reducible, elab_as_eliminator]
protected def rec_on_subsingleton₂
   {φ : quotient s₁ → quotient s₂ → Sort u_c} [h : ∀ a b, subsingleton (φ ⟦a⟧ ⟦b⟧)]
   (q₁ : quotient s₁) (q₂ : quotient s₂) (f : Π a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂:=
@quotient.rec_on_subsingleton _ s₁ (λ q, φ q q₂) (λ a, quotient.ind (λ b, h a b) q₂) q₁
  (λ a, quotient.rec_on_subsingleton q₂ (λ b, f a b))

end
end quotient

open decidable
instance {α : Sort u} {s : setoid α} [d : ∀ a b : α, decidable (a ≈ b)] : decidable_eq (quotient s) :=
λ q₁ q₂,
  quotient.rec_on_subsingleton₂ q₁ q₂
    (λ a₁ a₂,
      match (d a₁ a₂) with
      | (is_true h₁)  := is_true (quotient.sound h₁)
      | (is_false h₂) := is_false (λ h, h₂ (quotient.exact h))
      end)
