import measure_theory.interval_integral
import analysis.calculus.mean_value

noncomputable theory

open measure_theory set classical filter topological_space
open interval_integral

open_locale classical topological_space filter

variables {E : Type*} [measurable_space E] [normed_group E] 
                      [second_countable_topology E] [complete_space E] 
                      [normed_space ℝ E] [borel_space E]
variables {f : ℝ → ℝ} {a b : ℝ} 
variables {f' g : ℝ → ℝ}

-- Two cts functions with the same derivative in an interval and same initial
-- value coincide in the whole interval.
theorem eq_of_deriv_eq
  (contf : continuous_on f (Icc a b)) 
  (contg : continuous_on g (Icc a b))
  (hfderiv : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x)
  (hgderiv : ∀ x ∈ Ico a b, has_deriv_within_at g (f' x) (Ioi x) x)
  (hi : f a = g a) :
  ∀ y ∈ Ico a b, f y = g y :=
begin
  have hzero : ∀ z ∈ Ico a b, has_deriv_within_at (f - g) 0 (Ioi z) z,
  { intros z hz,
    convert has_deriv_within_at.sub (hfderiv z hz) (hgderiv z hz),
    rw sub_self, },
  have hbound : ∀ z ∈ Ico a b, ∥(0 : ℝ)∥ ≤ 0 
    := λ _ _, by rw norm_le_zero_iff,
  intros y hy,
  have hnormle := norm_image_sub_le_of_norm_deriv_right_le_segment 
    (contf.sub contg) hzero hbound y (mem_Icc_of_Ico hy),
  simpa [zero_mul, norm_le_zero_iff, sub_eq_zero, sub_eq_zero.mpr hi] using hnormle,
end

-- Has derivative from the right.
lemma deriv_integral_right
  (contf' : continuous f')
  (derivf : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x) 
  (intgf' : ∀ x ∈ Icc a b, interval_integrable f' volume a x) :
  ∀ x ∈ Ico a b, 
  has_deriv_within_at (λ u, ∫ y in a..u, f' y) (f' x) (Ioi x) x :=
begin 
  intros x hx,
  have intgf'r := intgf' x (mem_Icc_of_Ico hx),
  have hderivci := @integral_has_deriv_within_at_right 
    _ _ _ _ _ _ _ _ _ _ intgf'r _ _ (FTC_filter.nhds_right x)
    (continuous.continuous_within_at contf'),
  have hderivxb := has_deriv_within_at.mono hderivci (@Icc_subset_Ici_self _ _ x b),
  refine has_deriv_within_at.nhds_within hderivxb _,
  apply Icc_mem_nhds_within_Ioi,
  exact ⟨le_refl x, hx.2⟩,
end 

-- Benjamin's lemma. We should put it and versions of it in mathlib.
lemma integral_sub_at_right 
  (a c d : ℝ) 
  (h1 : interval_integrable f' volume a d) 
  (h2 : interval_integrable f' volume a c) :
  (∫ (y : ℝ) in a..d, f' y) - ∫ (y : ℝ) in a..c, f' y = ∫ (y : ℝ) in c..d, f' y :=
by rw [integral_interval_sub_interval_comm' h1 h2
      (interval_integrable.refl (interval_integrable.measurable h1)), integral_same, sub_zero]

-- TODO: Move
lemma eventually_le_of_eq {α β : Type*} [preorder β] (l : filter α) (f g : α → β) (h : f =ᶠ[l] g)
: f ≤ᶠ[l] g := 
eventually_le.congr (eventually_le.refl _ _) (eventually_eq.refl _ _) h

-- Second part of the Fundamental Theorem of Calculus.
theorem ftc2
  (contf : continuous_on f (Icc a b)) 
  (contf' : continuous f')
  (derivf : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x)
  (intgf' : ∀ x ∈ Icc a b, interval_integrable f' volume a x) :
  ∀ x ∈ Ico a b, ∫ y in a..x, f' y = f x - f a :=
begin
    intros x hx, 
    by_cases hab : b < a, 
    { have hc := lt_of_le_of_lt hx.1 (lt_trans hx.2 hab), 
      exfalso, exact lt_irrefl _ hc, },
    -- We know a ≤ b.
    replace hab := le_of_not_lt hab,
    have hbab : b ∈ Icc a b := ⟨hab, le_refl b⟩,
    -- Needed to apply extreme value theorem.
    have hneab := nonempty_Icc.2 hab,
    have hcmpab := @compact_Icc a b,
    have hctsnorm : continuous_on (λ x, ∥f' x∥) (Icc a b),
    { apply continuous.continuous_on,
      exact continuous.norm contf', },
    have hfbdd := is_compact.exists_forall_ge hcmpab hneab hctsnorm,
    apply eq_sub_of_add_eq, symmetry,
    -- Derivative of integral of the derivative is the derivative.
    have derivint : ∀ z ∈ Ico a b, 
      has_deriv_within_at (λ u, (∫ y in a..u, f' y) + f a) (f' z) (Ioi z) z,
    { intros y hy, apply has_deriv_within_at.add_const,
      exact (deriv_integral_right contf' derivf intgf' y hy), },
    -- Ready to apply main result. Only thing missing is continuity.
    refine (eq_of_deriv_eq contf _ derivf derivint _) x hx,
    { refine continuous_on.add _ continuous_on_const,
      rcases hfbdd with ⟨z, hzab, hzbd⟩,
      by_cases hfz : ∥f' z∥ ≤ 0,
      { -- If it is nonpositive, the function is zero on [a, b] and everything follows.
        replace hfz := le_antisymm hfz (norm_nonneg (f' z)),
        have hzero : ∀ y ∈ Icc a b, f' y = 0,
        { intros y hy, apply norm_le_zero_iff.1,
          specialize hzbd y hy, dsimp at hzbd, 
          rw hfz at hzbd, exact hzbd, },
        have hrestrictint : restrict (λ x, ∫ y in a..x, f' y) (Icc a b) = λ x, 0,
        { funext v, show ∫ y in a..v.val, f' y = 0,
          have eventzero : f' =ᵐ[volume.restrict (Ioc a v.val)] 0,
          { rw eventually_eq_iff_exists_mem, use [Ioc a v.val], split,
            { simp, use univ, split,
              { show volume univᶜ = 0, rw compl_univ, simp, }, 
              { use [Ioc a v.val], split,
                { exact subset.refl _, },
                { erw [univ_inter _], exact subset.refl _, }, }, },
            { intros w hw,
              rw [hzero w ⟨le_of_lt hw.1, le_trans hw.2 v.2.2⟩], refl, }, },
          rw integral_eq_zero_iff_of_le_of_nonneg_ae v.2.1,
          { exact eventzero, },
          { apply @eventually_le.congr _ _ _ _ 0 0 0 f',
            { exact eventually_le.refl _ _, },
            { exact eventually_eq.refl _ _, },
            { exact (eventually_eq.symm eventzero), }, },
          { exact (intgf' v.1 v.2), }, },
        rw continuous_on_iff_continuous_restrict,
        erw hrestrictint, exact continuous_const, }, 
      replace hfz := lt_of_not_ge hfz,
      -- Prove from first principles...
      rw metric.continuous_on_iff, intros c hc ε hε, 
      -- Choose appropriate δ.
      let δ := ε / ∥f' z∥,
      have hδ : 0 < δ := div_pos hε hfz,
      use [δ, hδ], intros d hd hdist, rw [dist_eq_norm],
      calc ∥(∫ (y : ℝ) in a..d, f' y) - ∫ (y : ℝ) in a..c, f' y∥ 
          -- Apply subtraction lemma.
          = ∥∫ (y : ℝ) in c..d, f' y∥ 
          : begin 
              apply congr_arg norm,
              exact (integral_sub_at_right a c d (intgf' d hd) (intgf' c hc)),
            end
            -- Since the norm of f' is bounded, its integral is bounded.
      ... ≤ ∥f' z∥ * abs (d - c)
          : begin 
              apply interval_integral.norm_integral_le_of_norm_le_const,
              intros w hw, by_cases hcd : c ≤ d,
              { rw [min_eq_left hcd, max_eq_right hcd] at hw,
                have haw : a ≤ w := le_of_lt (lt_of_le_of_lt hc.1 hw.1),
                have hwb : w ≤ b := le_trans hw.2 hd.2,
                exact hzbd w ⟨haw, hwb⟩, },
              { replace hcd := le_of_not_le hcd,
                rw [min_eq_right hcd, max_eq_left hcd] at hw,
                have haw : a ≤ w := le_of_lt (lt_of_le_of_lt hd.1 hw.1),
                have hwb : w ≤ b := le_trans hw.2 hc.2,
                exact hzbd w ⟨haw, hwb⟩, },
            end
            -- abs is just dist.
      ... = ∥f' z∥ * dist d c 
          : by rw [dist_eq_norm, real.norm_eq_abs (d - c), abs_sub d c]
            -- dist is less than δ by assumption.
      ... < ∥f' z∥ * δ 
          : mul_lt_mul_of_pos_left hdist hfz
            -- and it was convenientyly chosen so that the whole thing is less than ε. 
      ... = ε
          : begin 
              erw ←mul_div_assoc,
              exact mul_div_cancel_left ε (ne_of_gt hfz), 
            end, },
    { simp only [integral_same, zero_add], },
end 
