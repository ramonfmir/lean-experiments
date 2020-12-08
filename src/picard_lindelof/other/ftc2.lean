import measure_theory.interval_integral
import analysis.calculus.mean_value

noncomputable theory

open measure_theory set classical filter topological_space
open interval_integral

open_locale classical topological_space filter

variables {E : Type*} [measurable_space E] [normed_group E] 
                      [second_countable_topology E] [complete_space E] 
                      [normed_space ℝ E] [borel_space E]
variables {f : ℝ → E} {a b : ℝ} 
variables {f' g : ℝ → E}

-- IDEA: Relax hypotheses here. Remove continuous_on and deduce.
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
  have hbound : ∀ z ∈ Ico a b, ∥(0 : E)∥ ≤ 0 
    := λ _ _, by rw norm_le_zero_iff,
  intros y hy,
  have hnormle := norm_image_sub_le_of_norm_deriv_right_le_segment 
    (contf.sub contg) hzero hbound y (mem_Icc_of_Ico hy),
  simpa [zero_mul, norm_le_zero_iff, sub_eq_zero, sub_eq_zero.mpr hi] using hnormle,
end

lemma interval_integrable_left
  (h : interval_integrable f' volume a b) :
  ∀ x ∈ Icc a b, interval_integrable f' volume x b := 
sorry

lemma interval_integrable_right
  (h : interval_integrable f' volume a b) :
  ∀ x ∈ Icc a b, interval_integrable f' volume a x := 
sorry

lemma deriv_integral_right
  (contf' : continuous f')
  (derivf : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x) 
  (intgf' : interval_integrable f' volume a b) :
  ∀ x ∈ Ico a b, 
  has_deriv_within_at (λ u, ∫ y in a..u, f' y) (f' x) (Ioi x) x :=
begin 
  intros x hx,
  have intgf'r := interval_integrable_right intgf' x (mem_Icc_of_Ico hx),
  have hderivci := @integral_has_deriv_within_at_right 
    _ _ _ _ _ _ _ _ _ _ intgf'r _ _ (FTC_filter.nhds_right x)
    (continuous.continuous_within_at contf'),
  have hderivxb := has_deriv_within_at.mono hderivci (@Icc_subset_Ici_self _ _ x b),
  refine has_deriv_within_at.nhds_within hderivxb _,
  apply Icc_mem_nhds_within_Ioi,
  exact ⟨le_refl x, hx.2⟩,
end 

lemma deriv_integral_left
  (contf' : continuous f')
  (derivf : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x) 
  (intgf' : interval_integrable f' volume a b) :
  ∀ x ∈ Ioc a b, 
  has_deriv_within_at (λ u, ∫ y in u..b, f' y) (-f' x) (Iio x) x :=
begin 
  intros x hx,
  have intgf'l := interval_integrable_left intgf' x (mem_Icc_of_Ioc hx),
  have hderivci := @integral_has_deriv_within_at_left 
    _ _ _ _ _ _ _ _ _ _ intgf'l _ _ (FTC_filter.nhds_left x)
    (continuous.continuous_within_at contf'),
  have hderivax := has_deriv_within_at.mono hderivci (@Icc_subset_Iic_self _ _ a x),
  refine has_deriv_within_at.nhds_within hderivax _,
  apply Icc_mem_nhds_within_Iio,
  exact ⟨hx.1, le_refl x⟩,
end 

#check compact_Icc 
#check nonempty_Icc
#check is_compact.exists_forall_ge
#check continuous.norm

theorem ftc2
  (contf : continuous_on f (Icc a b)) 
  (contf' : continuous f')
  (derivf : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x)
  (intgf' : interval_integrable f' volume a b) :
  ∀ x ∈ Ico a b, ∫ y in a..x, f' y = f x - f a :=
begin
    intros x hx, 
    by_cases hab : b < a, 
    { have hc := lt_of_le_of_lt hx.1 (lt_trans hx.2 hab), 
      exfalso, exact lt_irrefl _ hc, },
    replace hab := le_of_not_lt hab,
    have hneab := nonempty_Icc.2 hab,
    have hcmpab := @compact_Icc a b,
    have hctsnorm : continuous_on (λ x, ∥f' x∥) (Icc a b) := sorry,
    have hfbdd := is_compact.exists_forall_ge hcmpab hneab hctsnorm,
    apply eq_sub_of_add_eq, symmetry,
    have derivint : ∀ z ∈ Ico a b, 
      has_deriv_within_at (λ u, (∫ y in a..u, f' y) + f a) (f' z) (Ioi z) z,
    { intros y hy, apply has_deriv_within_at.add_const,
      exact (deriv_integral_right contf' derivf intgf' y hy), },
    refine (eq_of_deriv_eq contf _ derivf derivint _) x hx,
    { refine continuous_on.add _ continuous_on_const,
      rw metric.continuous_on_iff, 
      rcases hfbdd with ⟨z, hzab, hzbd⟩,
      by_cases hfz : ∥f' z∥ = 0,
      { -- If it is zero, the whole function is zero and everything follows.
        sorry, }, 
      intros c hc ε hε, 
      let δ := ε / ∥f' z∥,
      have hδ : 0 < δ,
      { -- Follows from hfz and norm_nonneg.
        sorry, },
      use [δ, hδ], 
      intros d hd hdist, 
      rw [dist_eq_norm], 
      -- ∥(∫ (y : ℝ) in a..d, f' y) - ∫ (y : ℝ) in a..c, f' y∥ < ε
      -- ∥∫ (y : ℝ) in c..d, f' y∥ < ε
      -- ∥∫ (y : ℝ) in c..d, f' y∥ ≤ dist c d * ∥f' z∥
      --                          < (ε / ∥f' z∥) * ∥f' z∥
      --                          < ε
      
      sorry,
      -- intros z hz, 
      -- by_cases hab : b ≤ a, { rw Ico_eq_empty hab at hx, cases hx, },
      -- replace hab := lt_of_not_ge hab,
      -- by_cases hzb : z < b,
      -- { have derivinta := derivint z ⟨hz.1, hzb⟩,
      --   have hctsoi := has_deriv_within_at.continuous_within_at derivinta,
      --   have hctsoc := continuous_within_at.mono hctsoi (@Ioc_subset_Ioi_self _ _ z b),
      --   -- Plan:
      --   -- 1. deriv left. 
      --   -- 2. [a, b] = [a, z) ∪ {z} ∪ (z, b] 
      --   -- 3. Split on union:
      --   --     * first corresponds to left, 
      --   --     * middle corresponds to continuous_within_at_singleton,
      --   --     * last corresponds to right.

      --   --rw ←Ioc_union_left (le_of_lt hab),
      --   --refine continuous_within_at_union.2 ⟨_, _⟩,
      --   --convert hctsoc,
      --   --{ exact hctsoc, },
      --   --{ exact continuous_within_at_singleton, }, 
      --   sorry,
      -- },
      -- { sorry, },
      },
    { simp only [integral_same, zero_add], },
end 
