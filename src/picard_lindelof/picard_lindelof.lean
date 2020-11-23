import picard_lindelof.definitions

-- Following Imperial's MA2AA1 notes and Ch 2 of 'Spectral Theory and Quantum Mechanics'.

noncomputable theory
open metric set asymptotics filter real measure_theory 
open interval_integral topological_space uniform_space
open picard_operator
open_locale topological_space classical filter uniformity 

section picard_lindelof

-- NOTE: This is meant to be ℝ^n.
variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                      [normed_space ℝ E] [complete_space E] [second_countable_topology E]


lemma P.lipschitz_at_of_lipshitz (x y : C(E)) (Ix : IVP(x)) (Iy : IVP(y))
: edist (P x Ix) (P y Iy) ≤ ↑(I.K) * edist x.to_fun y.to_fun :=
begin 
    simp, unfold edist, unfold metric_space.edist,
    rw metric_space.edist_dist, cases K with K hK,
    rw ←ennreal.of_real_eq_coe_nnreal,
    rw ←ennreal.of_real_mul hK,
    apply ennreal.of_real_le_of_real,
    rw dist_eq_norm, 
    calc ∥x0 + ∫ s in t0..t, f s (x s) ∂μ - (x0 + ∫ s in t0..t, f s (y s) ∂μ)∥ 
        = ∥∫ s in t0..t, f s (x s) ∂μ - ∫ s in t0..t, f s (y s) ∂μ∥
        : by rw [sub_eq_add_neg, neg_add, add_comm x0, add_assoc, ←add_assoc x0, 
                 add_comm x0, neg_add_self, zero_add, ←sub_eq_add_neg]
    ... = ∥∫ s in t0..t, (f s (x s)) - (f s (y s)) ∂μ∥ 
        : by rw interval_integral.integral_sub hx hy
    ... ≤ ∫ s in t0..t, ∥(f s (x s)) - (f s (y s))∥ ∂μ
        : norm_integral_le_integral_norm_Ioc_of_le ht
    ... = ∫ s in t0..t, (dist (f s (x s)) (f s (y s))) ∂μ
        : by congr; ext; exact (dist_eq_norm _ _).symm
    ... ≤ ∫ s in t0..t, K * dist (x s) (y s) ∂μ
        : begin 
            have hxsys := λ s, hf s (x s) (y s),
            -- TODO: Factor this out. Argument about edist dist and le.
            have hrw : (λ s, dist (f s (x s)) (f s (y s))) ≤ (λ s, K * dist (x s) (y s)) := sorry,
            -- This follows from interval_integral.integral_mono.
            have h := interval_integral.integral_mono μ t0 t hx hy,
            -- TODO: We also need that dist is integrable... Arguments above
            -- should not be hx and hy..
            sorry,
         end
         -- Then we use norm_integral_le_of_norm_le_const
         -- Bound it above by the supremum!
         -- Well have something like K * (t - t0) * s ≤ K * s 
         -- So we play with the t-t0 and K's and we should be good.
    ... ≤ K * Inf {C | 0 ≤ C ∧ ∀ t, dist (x t) (y t) ≤ C} : sorry
end

lemma P.lipschitz_of_lipschitz (hf : ∀ s, lipschitz_with K (f s))
: lipschitz_with K P :=
begin 
    intros x y,
    let S := {C | 0 ≤ C ∧ ∀ (a : ℝ), edist (P x a) (P y a) ≤ C},
    calc edist (P x) (P y) 
        = Inf S : P.edist_eq_Inf x y sorry -- NOTE: Is this even useful?
    ... ≤ ↑K * edist x y : sorry --supr_le (λ t, P.lipschitz_at_of_lipshitz hf t x y),
end 

--lemma P.edist_lt_top : Π (x : A →ᵇ B), edist x (P x) < ⊥ := sorry

def P.efixed_point_of_lipschitz (hf : ∀ s, lipschitz_with K (f s)) : ℝ →ᵇ B := 
contracting_with.efixed_point P ⟨hK, P.lipschitz_of_lipschitz hf⟩ sorry sorry

--#check contracting_with.efixed_point P

/-- There exists only one solution of an ODE \(\dot x=v(t, x)\) with
a given initial value provided that RHS is Lipschitz continuous in `x`. -/
theorem ODE_solution_unique' {v : ℝ → B → B}
  {K : nnreal} (hv : ∀ t, lipschitz_with K (v t))
  {f g : ℝ → B} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ t ∈ Ico a b, has_deriv_within_at f (v t (f t)) (Ioi t) t)
  (hg : continuous_on g (Icc a b))
  (hg' : ∀ t ∈ Ico a b, has_deriv_within_at g (v t (g t)) (Ioi t) t)
  (ha : f a = g a) :
  ∀ t ∈ Icc a b, f t = g t := 
begin
    sorry,
end

end picard_lindelof
