open quotient
variables {A : Type} {B : A → Type}

variable f : Π a : A, B a

variable [setoid (Π a, B a)]

#reduce λ x, quotient.lift_on ⟦f⟧ (λf : (Πx : A, B x), f) _ x

example (x : A) : quotient.lift_on ⟦f⟧ (λf : (Πx : A, B x), f) sorry x = f x :=
rfl
