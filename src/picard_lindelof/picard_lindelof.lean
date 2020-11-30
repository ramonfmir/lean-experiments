import picard_lindelof.definitions
import picard_lindelof.other.interval_integral
import picard_lindelof.other.mul_Inf

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

lemma dist_v_integrable (v : α → E → E) (I : IVP(v)) (x y : α →ᵇ E)
: integrable (λ t, dist (v t (x t)) (v t (y t))) :=
begin 
  split,
  { exact measurable.dist (I.hintegrable' x).measurable (I.hintegrable' y).measurable, },
  { unfold has_finite_integral,  
    simp only [dist_eq_norm, nnnorm_norm, ←nndist_eq_nnnorm, ←edist_nndist],
    simp only [edist_dist, dist_eq_norm],
    rcases (I.hbdd x) with ⟨Cx, hposCx, hboundCx⟩,
    rcases (I.hbdd y) with ⟨Cy, hposCy, hboundCy⟩,
    have h : ∀ a, ∥v a (x a) - v a (y a)∥ ≤ Cy + Cx,
    { intros a,
      have hd := norm_sub_le (v a (x a)) (v a (y a)),
      have hboundCxa := hboundCx a,
      have hboundCya := hboundCy a,
      linarith, },
    replace h := λ a, ennreal.of_real_le_of_real (h a),
    have hle1 : (∫⁻ (a : α), (ennreal.of_real ∥(v a (x a)) - (v a (y a))∥)) 
      ≤ (∫⁻ (a : α), (ennreal.of_real (Cy + Cx))),
    { apply lintegral_mono, exact h, },
    have hle2 : (∫⁻ (a : α), (ennreal.of_real (Cy + Cx))) < ⊤,
    { rw lintegral_const, apply ennreal.mul_lt_top,
      { exact ennreal.of_real_lt_top, },
      { have hfm : finite_measure (volume : measure α) := by apply_instance,
        refine hfm.measure_univ_lt_top, }, },
    exact lt_of_le_of_lt hle1 hle2, },
end 

lemma dist_pointwise_integrable (v : α → E → E) (I : IVP(v)) (x y : α →ᵇ E)
: integrable (λ t, dist (x t) (y t)) :=
begin 
  sorry
end 

lemma K_dist_pointwise_integrable (v : α → E → E) (I : IVP(v)) (x y : α →ᵇ E)
: integrable (λ t, I.K.1 * dist (x t) (y t)) :=
integrable.const_mul (dist_pointwise_integrable v I x y) I.K.1

--integrable (λ (a : α), ↑(I.K) * dist (⇑x a) (⇑y a)) (volume.restrict (Ioc (min 0 t) (max 0 t)))

lemma P.lipschitz_at (x₀ : E) (v : α → E → E) (I : IVP(v)) (x y : α →ᵇ E) (t : α)
: dist (P x₀ v I x t) (P x₀ v I y t) ≤ I.K * dist x y :=
begin 
    simp, rw dist_eq_norm,
    calc ∥(∫ s in 0..t, v s (x s)) - (∫ s in 0..t, v s (y s))∥
        = ∥∫ s in 0..t, (v s (x s)) - (v s (y s))∥ 
        : by rw interval_integral.integral_sub (I.hintegrable x t) (I.hintegrable y t)
    ... ≤ ∫ s in Ioc (min 0 t) (max 0 t), ∥(v s (x s)) - (v s (y s))∥
        : interval_integral.norm_integral_le_integral_norm_Ioc
    ... = ∫ s in Ioc (min 0 t) (max 0 t), (dist (v s (x s)) (v s (y s)))
        : by congr; ext; exact (dist_eq_norm _ _).symm
    ... ≤ ∫ s in Ioc (min 0 t) (max 0 t), I.K * dist (x s) (y s)
        : begin 
            apply integral_mono,
            { have hd := dist_v_integrable v I x y,
              show integrable_on (λ t, dist (v t (x t)) (v t (y t))) _,
              exact integrable_on.mono_set (integrable_on_univ.2 hd) (λ s hs, trivial), },
            { have hd := K_dist_pointwise_integrable v I x y,
              show integrable_on (λ t, I.K.1 * dist (x t) (y t)) _,
              exact integrable_on.mono_set (integrable_on_univ.2 hd) (λ s hs, trivial), },
            intros t; dsimp, 
            exact ((lipschitz_with_iff_dist_le_mul.1 (I.hlipschitz t)) (x t) (y t)),
        end
    ... ≤ ∫ s in Ioc (min 0 t) (max 0 t), I.K * dist x y
        : begin 
            apply integral_mono,
            { have hd := K_dist_pointwise_integrable v I x y,
              show integrable_on (λ t, I.K.1 * dist (x t) (y t)) _,
              exact integrable_on.mono_set (integrable_on_univ.2 hd) (λ s hs, trivial), },
            { show integrable_on (λ t, I.K.1 * dist x y) (Ioc (min 0 t) (max 0 t)) volume,
               exact integrable_on.mono_set 
                (integrable_on_univ.2 (integrable_const (I.K.1 * dist x y)))
                (λ s hs, trivial), },
            intros t; dsimp, mono,
            { apply le_cInf,
              { exact bounded_continuous_function.dist_set_exists, },
              { intros b hb, exact (hb.2 t), }, },
            { exact dist_nonneg, },
            { exact I.K.2, },
        end
    ... ≤ (abs t.1) * (I.K * dist x y) 
        : begin 
            rw [measure_theory.integral_const, measure.restrict_apply_univ],
            simp only [α.volume_Ioc, ennreal.to_real_of_real', ←neg_sub t.1],
            -- TODO: This should be simpler.
            by_cases h : 0 ≤ t,
            { erw [max_eq_right h, min_eq_left h, sub_zero t.val],
              replace h : 0 ≤ t.1 := h, rw [max_eq_left h],
              refine (mul_le_mul _ (le_refl _) _ _),
              { exact le_abs_self t.1, },
              { exact (mul_nonneg I.K.2 dist_nonneg), },
              { exact abs_nonneg t.1, }, },
            { replace h := le_of_not_le h,
              erw [max_eq_left h, min_eq_right h, zero_sub t.val],
              replace h : t.1 ≤ 0 := h, 
              have h' := neg_le_neg h,
              rw neg_zero at h', rw [max_eq_left h'],
              refine (mul_le_mul _ (le_refl _) _ _),
              { rw [abs_of_nonpos h], },
              { exact (mul_nonneg I.K.2 dist_nonneg), },
              { exact abs_nonneg t.1, }, },
          end
    ... ≤ I.K * (dist x y)
        : begin 
            have h := abs_le_abs t.2.2 (neg_le.1 t.2.1), rw abs_one at h,
            exact mul_le_of_le_one_left (mul_nonneg I.K.2 dist_nonneg) h,
          end
end

lemma P.lipschitz (x₀ : E) (v : α → E → E) (I : IVP(v)) 
: lipschitz_with I.K (P x₀ v I) :=
begin 
  intros x y, cases I, cases I_K with K hnnK,
  unfold edist, rw metric_space.edist_dist, unfold dist,
  rw metric_space.edist_dist, unfold dist, 
  rw ←ennreal.of_real_eq_coe_nnreal hnnK,
  rw ←ennreal.of_real_mul hnnK,
  apply ennreal.of_real_le_of_real,
  have h1 : ∃ (C : ℝ), 0 ≤ C ∧ ∀ (t : α), dist (x t) (y t) ≤ C := 
    bounded_continuous_function.dist_set_exists,
  have h2 : ∀ (t : α), dist (x t) (y t) ≤ Inf {C : ℝ | 0 ≤ C ∧ ∀ (s : α), dist (x s) (y s) ≤ C},
  { intros t, apply le_cInf,
    { use h1, },
    { intros b hb, exact (hb.2 t), }, },
  erw mul_Inf hnnK h1 h2, apply cInf_le_cInf,
  { use 0, intros b hb, exact hb.1, },
  { cases h1 with C hC, use [K * C, C, ⟨rfl, hC.1, hC.2⟩], },
  clear h1 h2,
  rintros C ⟨C', ⟨hC, hnnC', hC'⟩⟩, rw hC,
  refine ⟨mul_nonneg hnnK hnnC', _⟩, intros s,
  have hC's := hC' s,
  have hdxyle : dist x y ≤ C',
  { -- TODO: Factor this out.
    apply cInf_le, 
    { use 0, intros b hb, exact hb.1, },
    { exact ⟨hnnC', hC'⟩, }, },
  -- TODO: This is not very nice and will need to change when we keep only one
  -- integrability condition.
  let I' : IVP(v) := ⟨⟨K, hnnK⟩, I_hK, I_hlipschitz, I_hbdd, I_hintegrable, I_hintegrable'⟩,
  have hPsle := P.lipschitz_at x₀ v I' x y s,
  have hKdxyle : K * dist x y ≤ K * C' := mul_le_mul (le_refl _) hdxyle dist_nonneg hnnK,
  exact le_trans hPsle hKdxyle,
end

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
