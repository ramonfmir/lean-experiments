-- import picard_lindelof.definitions

-- open topological_space measure_theory metric

-- variable (μ : measure ℝ)

-- -- NOTE: This is meant to be ℝ^n.
-- variables {B : Type*} [normed_group B] [normed_space ℝ B] [measurable_space B]
--                        [complete_space B] [second_countable_topology B] [borel_space B]
--                        [linear_order B]

-- local infixr ` →ᵇ `:25 := bounded_continuous_function         

-- lemma P.edist_eq_Inf (x y : ℝ →ᵇ B) (h : edist (P μ x) (P y) ≠ ⊤)
-- : edist (P x) (P y) = Inf {C | 0 ≤ C ∧ ∀ (a : ℝ), edist (P x a) (P y a) ≤ C} :=
-- begin
--     let S := {C : ℝ | 0 ≤ C ∧ ∀ (a : ℝ), dist (P x a) (P y a) ≤ C},
--     have hS : S.nonempty, 
--     { use [supr (λ t, dist ((P x) t) ((P y) t))], split,
--       { eapply le_csupr_iff.mpr,
--         { rcases (P.dist_bdd_above x y) with ⟨C, hC⟩,
--           use C, rintros d ⟨a, hd⟩, rw ←hd, exact (hC a), },
--         { intros b h,
--           replace h := h (nonempty.some (by apply_instance)),
--           exact (le_trans dist_nonneg h), }, },
--       { apply le_csupr,
--         { rcases (P.dist_bdd_above x y) with ⟨C, hC⟩,
--           use C, rintros d ⟨a, hd⟩, rw ←hd, exact (hC a), }, }, },
--     have hSbdd : bdd_below S,
--     { use 0, intros x hx, exact hx.1, },
--     have h := map_cInf_of_continuous_at_of_monotone 
--         (ennreal.continuous_at_of_real (Inf S)) ennreal.monotone_of_real hS hSbdd,
--     unfold edist, unfold metric_space.edist,
--     rw h, simp only [S, set.image], dsimp, 
--     sorry,
--     -- Issue with C maybe being ⊤. But I believe that's because the sets won't
--     -- be the same, but the infimums will
    
--     -- congr, ext C, split,
--     -- { rintros ⟨c, ⟨⟨h0lec, hdist⟩, hC⟩⟩, split,
--     --   { rw ←hC, replace h0lec := ennreal.of_real_le_of_real h0lec,
--     --     rw ennreal.of_real_zero at h0lec, exact h0lec, },
--     --   { intros a, rw ←hC,
--     --     have hdista := hdist a,
--     --     erw metric_space.edist_dist,
--     --     exact (ennreal.of_real_le_of_real hdista), }, },
--     -- { rintros ⟨h0leC, hedist⟩, by_cases (C = ⊤),
--     --   {  },
--     --   { use [ennreal.to_real C], split,
--     --     { split,
--     --         { exact ennreal.to_real_nonneg, },
--     --         { intros a, have hedista := hedist a,
--     --         erw metric_space.edist_dist at hedista, sorry, }, },
--     --     { sorry, }, }, },
-- end 