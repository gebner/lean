import init.meta.feature_search
open feature_search tactic

#print add_left_cancel_iff
#eval feature_vec.of_thm ``add_left_cancel_iff >>= trace

attribute [inline] bool.decidable_eq

set_option profiler true
-- set_option trace.compiler.optimize_bytecode true
#eval do
env ← get_env,
let decls := env.fold [] (::),
let defns := (do declaration.defn n _ t _ _ tt ← decls | [], [(n,t)]),
let thms := (do declaration.thm n _ t _ ← decls | [], [(n,t)]),
let axs := defns ++ thms,
trace axs.length,
-- let axs := axs.filter( λ ax, ax.2.get_weight ≤ 1000),
-- trace (axs.filter (λ ax, ax.2.get_weight > 5000))
-- trace (defns.length, thms.length),
trace axs.length,
fvs ←  timetac "of_exprs" $ (axs.map prod.fst).zip <$>  feature_vec.of_exprs (axs.map prod.snd),
-- fvs ← monad.sequence (do
--     (n,t) ← axs,
--     pure $ do
--         fv ← feature_vec.of_expr t,
--         pure (n,t)),
-- fvs ← timetac "foo" $ (axs.map prod.fst).zip <$> (axs.map prod.snd).mmap feature_vec.of_expr,
-- fvs.mmap' trace,
let fs := feature_stats.of_feature_vecs (fvs.map prod.snd),
-- trace $ fs.features_with_idf.filter (λ f, f.2 < 16),
let query : expr := `(∀ x y : ℤ,  x + 1 + y + 1 + x = y + x + x + 2),
query_fv ← feature_vec.of_expr query,
trace query_fv,
trace $ (fvs.map (λ fv : name × feature_vec,
    (fv.1, fs.cosine_similarity fv.2 query_fv))).filter (λ x, x.2 > 0.5),
pure ()
