namespace feature_search

open tactic native

@[derive decidable_eq]
meta inductive feature
| const (n : name)
| arg (p : name) (c : name)

namespace feature

protected meta def to_string : feature → string
| (const n) := n.to_string
| (arg p c) := p.to_string ++ "→" ++ c.to_string

protected meta def repr : feature → string
| (const n) := "(const `" ++ n.to_string ++ ")"
| (arg p c) := "(arg `" ++ p.to_string ++ " `" ++ c.to_string ++ ")"

meta instance : has_to_string feature := ⟨feature.to_string⟩
meta instance : has_repr feature := ⟨feature.repr⟩
meta instance : has_to_tactic_format feature := ⟨λ f, pure f.to_string⟩
meta instance : has_to_format feature := ⟨λ f, f.to_string⟩

end feature

meta constant feature_vec : Type

namespace feature_vec

meta constant of_expr (e : expr) : tactic feature_vec
meta constant of_exprs (es : list expr) : tactic (list feature_vec)

protected meta constant union (a b : feature_vec) : feature_vec
meta instance : has_union feature_vec := ⟨feature_vec.union⟩

protected meta constant isect (a b : feature_vec) : feature_vec
meta instance : has_inter feature_vec := ⟨feature_vec.isect⟩

meta def of_proof (prf : expr) : tactic feature_vec :=
infer_type prf >>= of_expr

meta def of_thm (n : name) : tactic feature_vec := do
decl ← get_decl n,
of_expr decl.type

protected meta constant to_list (fv : feature_vec) : list feature

meta instance : has_to_string feature_vec := ⟨to_string ∘ feature_vec.to_list⟩
meta instance : has_repr feature_vec := ⟨repr ∘ feature_vec.to_list⟩
meta instance : has_to_tactic_format feature_vec := ⟨pp ∘ feature_vec.to_list⟩
meta instance : has_to_format feature_vec := ⟨to_fmt ∘ feature_vec.to_list⟩

end feature_vec

meta constant feature_stats : Type

namespace feature_stats

meta constant of_feature_vecs (fvs : list feature_vec) : feature_stats
meta constant idf (fs : feature_stats) (f : feature) : float
meta constant norm (fs : feature_stats) (fv : feature_vec) : float
meta constant dotp (fs : feature_stats) (fv1 fv2 : feature_vec) : float
meta constant cosine_similarity (fs : feature_stats) (fv1 fv2 : feature_vec) : float
meta constant features (fs : feature_stats) : list feature

meta def features_with_idf (fs : feature_stats) : list (feature × float) :=
fs.features.map (λ f, (f, fs.idf f))

meta instance : has_to_string feature_stats := ⟨to_string ∘ feature_stats.features_with_idf⟩
meta instance : has_repr feature_stats := ⟨repr ∘ feature_stats.features_with_idf⟩
meta instance : has_to_tactic_format feature_stats := ⟨pp ∘ feature_stats.features_with_idf⟩
meta instance : has_to_format feature_stats := ⟨to_fmt ∘ feature_stats.features_with_idf⟩

end feature_stats

end feature_search