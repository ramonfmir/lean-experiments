import picard_lindelof.definitions
import picard_lindelof.other.interval_integral

-- Following Imperial's MA2AA1 notes.

noncomputable theory
open metric set asymptotics filter real measure_theory 
open interval_integral topological_space uniform_space
open picard_operator
open_locale topological_space classical filter uniformity 

section picard_lindelof

local infix ` →ᵇ `:25 := bounded_continuous_function 

-- NOTE: This is meant to be ℝ^n.
variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                      [normed_space ℝ E] [complete_space E] [second_countable_topology E]

#check mul_le_of_le_one_left

lemma P.lipschitz_at (v : α → E → E) (I : IVP(v)) (x y : α →ᵇ E)
(h0 : x 0 = y 0) (t : α)
: dist (P v I x t) (P v I y t) ≤ I.K * dist x y :=
begin 
    simp, rw dist_eq_norm, rw ←h0,
    calc ∥((x 0) + ∫ s in 0..t, v s (x s)) - ((x 0) + ∫ s in 0..t, v s (y s))∥ 
        = ∥(∫ s in 0..t, v s (x s)) - (∫ s in 0..t, v s (y s))∥
        : congr_arg norm $ by abel
    ... = ∥∫ s in 0..t, (v s (x s)) - (v s (y s))∥ 
        : by rw interval_integral.integral_sub (I.hintegrable x t) (I.hintegrable y t)
    ... ≤ ∫ s in 0..t, ∥(v s (x s)) - (v s (y s))∥
        -- TODO: This sorry is for 0 ≤ t. Need to change the interval integral lemma
        -- so that that condition is not required.
        : temp.norm_integral_le_integral_norm_Ioc_of_le sorry 
    ... = ∫ s in 0..t, (dist (v s (x s)) (v s (y s)))
        : by congr; ext; exact (dist_eq_norm _ _).symm
    ... ≤ ∫ s in 0..t, I.K * dist (x s) (y s)
        : begin 
            -- TODO: Something about integrable (bounded) distances.
            apply temp.integral_mono 0 t sorry sorry,
            intros t; dsimp, 
            exact ((lipschitz_with_iff_dist_le_mul.1 (I.hlipschitz t)) (x t) (y t)),
        end
    ... ≤ ∫ s in 0..t, I.K * dist x y
        : begin 
            apply temp.integral_mono 0 t sorry sorry,
            intros t; dsimp, mono,
            { apply le_cInf,
              { exact bounded_continuous_function.dist_set_exists, },
              { intros b hb, exact (hb.2 t), }, },
            { exact dist_nonneg, },
            { exact I.K.2, },
        end
    ... = (t.1 - 0) * (I.K * dist x y) 
        : by rw interval_integral.integral_const'; 
             simp only [α.volume_Ioc, ennreal.to_real_of_real', ←neg_sub t.1];
             simp only [max_zero_sub_eq_self]; refl
    ... = t.1 * (I.K * dist x y) 
        : by simp
    ... ≤ I.K * (dist x y)
        : mul_le_of_le_one_left (mul_nonneg I.K.2 dist_nonneg) t.2.2
end

    --     : begin 
    --         have hxsys := λ s, hf s (x s) (y s),
    --         -- TODO: Factor this out. Argument about edist dist and le.
    --         have hrw : (λ s, dist (f s (x s)) (f s (y s))) ≤ (λ s, K * dist (x s) (y s)) := sorry,
    --         -- This follows from interval_integral.integral_mono.
    --         have h := interval_integral.integral_mono μ t0 t hx hy,
    --         -- TODO: We also need that dist is integrable... Arguments above
    --         -- should not be hx and hy..
    --         sorry,
    --      end
    --      -- Then we use norm_integral_le_of_norm_le_const
    --      -- Bound it above by the supremum!
    --      -- Well have something like K * (t - t0) * s ≤ K * s 
    --      -- So we play with the t-t0 and K's and we should be good.

-- lemma P.lipschitz (v : ℝ → E → E) (I : IVP(v)) (x : C(E)) : lipschitz_with I.K (P v I) :=
-- begin 
--     intros x y,
--     let S := {C | 0 ≤ C ∧ ∀ (a : ℝ), edist (P v I x a) (P v I y a) ≤ C},
--     calc edist (P v I x) (P v I y) 
--         --= Inf S : P.edist_eq_Inf v I x y sorry sorry sorry 
--         -- NOTE: Is this even useful?
--         ≤ ↑(I.K) * edist x y : sorry --supr_le (λ t, P.lipschitz_at_of_lipshitz hf t x y),
-- end 

--lemma P.edist_lt_top : Π (x : A →ᵇ B), edist x (P x) < ⊥ := sorry

-- def P.efixed_point_of_lipschitz (hf : ∀ s, lipschitz_with K (f s)) : ℝ →ᵇ B := 
-- contracting_with.efixed_point P ⟨hK, P.lipschitz_of_lipschitz hf⟩ sorry sorry

--#check contracting_with.efixed_point P

/-- There exists only one solution of an ODE \(\dot x=v(t, x)\) with
a given initial value provided that RHS is Lipschitz continuous in `x`. -/
theorem ODE_solution_unique' {v : ℝ → E → E}
  {K : nnreal} (hv : ∀ t, lipschitz_with K (v t))
  {f g : ℝ → E} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ t ∈ Ico a b, has_deriv_within_at f (v t (f t)) (Ioi t) t) -- integral_has_deriv_within_at_right
  (hg : continuous_on g (Icc a b))
  (hg' : ∀ t ∈ Ico a b, has_deriv_within_at g (v t (g t)) (Ioi t) t)
  (ha : f a = g a) :
  ∀ t ∈ Icc a b, f t = g t := 
begin
    sorry,
end

end picard_lindelof
