import .clause .prover_state
open expr list monad

namespace super

meta def is_taut (c : clause) : tactic bool := do
qf ← c^.open_constn c↣num_quants,
return $ list.bor $ do
  l1 ← qf^.1^.get_lits, guard l1^.is_neg,
  l2 ← qf^.1^.get_lits, guard l2^.is_pos,
  [decidable.to_bool $ l1^.formula = l2^.formula]

open tactic
example (i : Type) (p : i → i → Type) (c : i) (h : ∀ (x : i), p x c → p x c) : true := by do
h ← get_local `h, hcls ← clause.of_classical_proof h,
taut ← is_taut hcls,
when (¬taut) failed,
to_expr `(trivial) >>= apply

meta def tautology_removal_pre : prover unit :=
preprocessing_rule $ λnew, filter (λc, lift bnot $♯ is_taut c↣c) new

meta def remove_duplicates : list derived_clause → list derived_clause
| [] := []
| (c :: cs) :=
  let (same_type, other_type) := partition (λc' : derived_clause, c'↣c↣type = c↣c↣type) cs in
  { c with sc := foldl score.min c↣sc (same_type↣for $ λc, c↣sc) } :: remove_duplicates other_type

meta def remove_duplicates_pre : prover unit :=
preprocessing_rule $ λnew,
return $ remove_duplicates new

end super
