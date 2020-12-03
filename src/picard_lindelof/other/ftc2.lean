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

-- theorem constant_of_right_deriv_zero
--   (hcont : continuous_on f (Icc a b))
--   (hderiv : ∀ x ∈ Ico a b, has_deriv_within_at f 0 (Ioi x) x) :
--   ∀ x ∈ Icc a b, f x = f a :=
-- by simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using
--   λ x hx, norm_image_sub_le_of_norm_deriv_right_le_segment
--     hcont hderiv (λ y hy, by rw norm_le_zero_iff) x hx

-- theorem constant_of_deriv_zero
--   (hdiff : differentiable_on ℝ f (Icc a b))
--   (hderiv : ∀ x ∈ Ico a b, deriv_within f (Icc a b) x = 0) :
--   ∀ x ∈ Icc a b, f x = f a :=
-- begin
--   have H : ∀ x ∈ Ico a b, ∥deriv_within f (Icc a b) x∥ ≤ 0 :=
--     by simpa only [norm_le_zero_iff] using λ x hx, hderiv x hx,
--   simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using
--     λ x hx, norm_image_sub_le_of_norm_deriv_le_segment hdiff H x hx,
-- end

variables {f' g : ℝ → E}

-- theorem eq_of_right_deriv_eq
--   (derivf : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ici x) x)
--   (derivg : ∀ x ∈ Ico a b, has_deriv_within_at g (f' x) (Ici x) x)
--   (fcont : continuous_on f (Icc a b)) 
--   (gcont : continuous_on g (Icc a b))
--   (hi : f a = g a) :
--   ∀ y ∈ Ico a b, f y = g y :=
-- begin
--   have H : ∀ x ∈ Ico a b, has_deriv_within_at (f - g) 0 (Ioi x) x,
--   { intros x hx,
--     have hderivf := has_deriv_within_at.mono (derivf x hx) (Ioi_subset_Ici_self),
--     have hderivg := has_deriv_within_at.mono (derivg x hx) (Ioi_subset_Ici_self),
--     convert has_deriv_within_at.sub hderivf hderivg,
--     rw sub_self, },
--   intros y hy,
--   have hnormle := norm_image_sub_le_of_norm_deriv_right_le_segment
--     (fcont.sub gcont) H (λ z hz, by rw norm_le_zero_iff) y (mem_Icc_of_Ico hy),
--   simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero, sub_eq_zero.mpr hi] using hnormle,
-- end

-- theorem eq_of_deriv_eq
--   (hu : ∀ s : set ℝ, ∀ c ∈ s, unique_diff_within_at ℝ s c)
--   (fdiff : differentiable_on ℝ f (Icc a b))
--   (gdiff : differentiable_on ℝ g (Icc a b))
--   (hderiv : ∀ x ∈ Ico a b, deriv_within f (Icc a b) x = deriv_within g (Icc a b) x)
--   (hi : f a = g a) :
--   ∀ y ∈ Icc a b, f y = g y :=
-- begin
--   have H : ∀ y ∈ Ico a b, ∥deriv_within (f - g) (Icc a b) y∥ ≤ 0,
--   { intros y hy,
--     have hf := fdiff y (mem_Icc_of_Ico hy),
--     have hg := gdiff y (mem_Icc_of_Ico hy),
--     have hsub := deriv_within_sub (hu _ _ (mem_Icc_of_Ico hy)) hf hg,
--     erw [hsub, hderiv y hy, sub_self, norm_le_zero_iff], },
--   simpa only [zero_mul, sub_eq_zero.mpr hi, norm_le_zero_iff, sub_eq_zero] using
--     λ y hy, norm_image_sub_le_of_norm_deriv_le_segment (fdiff.sub gdiff) H y hy,
-- end

theorem eq_of_deriv_eq
  (hfderiv : ∀ x ∈ Icc a b, has_deriv_within_at f (f' x) (Icc a b) x)
  (hgderiv : ∀ x ∈ Icc a b, has_deriv_within_at g (f' x) (Icc a b) x)
  (hi : f a = g a) :
  ∀ y ∈ Icc a b, f y = g y :=
begin
  have hzero : ∀ z ∈ Icc a b, has_deriv_within_at (f - g) 0 (Icc a b) z,
  { intros z hz,
    convert has_deriv_within_at.sub (hfderiv z hz) (hgderiv z hz),
    rw sub_self, },
  have hbound : ∀ z ∈ Ico a b, ∥(0 : E)∥ ≤ 0 
    := λ _ _, by rw norm_le_zero_iff,
  intros y hy,
  have hnormle := norm_image_sub_le_of_norm_deriv_le_segment' hzero hbound y hy,
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

lemma deriv_integral 
  (contf' : continuous f')
  (derivf : ∀ x ∈ Icc a b, has_deriv_within_at f (f' x) (Icc a b) x) 
  (intgf' : interval_integrable f' volume a b) :
  ∀ x ∈ Icc a b, 
  has_deriv_within_at (λ u, ∫ y in a..u, f' y) (f' x) (Icc a b) x :=
begin 
  intros x hx,
  have intgf'l := interval_integrable_left intgf' x hx,
  have intgf'r := interval_integrable_right intgf' x hx,

  --have h := @integral_has_deriv_within_at_right, 
    --_ _ _ _ _ _ _ _ _ _ intgf', --_ (Ioi a) _
    --(continuous.continuous_within_at contf'),

  have hderivci := @integral_has_deriv_within_at_right 
    _ _ _ _ _ _ _ _ _ _ intgf'r _ _ (FTC_filter.nhds_right x)
    (continuous.continuous_within_at contf'),
  have hderivic := @integral_has_deriv_within_at_left 
    _ _ _ _ _ _ _ _ _ _ intgf'l _ _ (FTC_filter.nhds_left x)
    (continuous.continuous_within_at contf'),
  have hderivxb := has_deriv_within_at.mono hderivci (@Icc_subset_Ici_self _ _ x b),
  have hderivax := has_deriv_within_at.mono hderivic (@Icc_subset_Iic_self _ _ a x),
  
  --refine has_deriv_within_at.nhds_within hderivxb _,

  sorry,
end 

theorem ftc2
  (contf : continuous_on f (Icc a b)) 
  (contf' : continuous f')
  (derivf : ∀ x ∈ Icc a b, has_deriv_within_at f (f' x) (Icc a b) x)
  (intgf' : interval_integrable f' volume a b) :
  ∀ x ∈ Icc a b, ∫ y in a..x, f' y = f x - f a :=
begin
    intros x hx, 
    apply eq_sub_of_add_eq, symmetry,
    refine (eq_of_deriv_eq derivf _ _) x hx,
    { intros y hy, apply has_deriv_within_at.add_const,
      exact (deriv_integral contf' derivf intgf' y hy), },
    { simp only [integral_same, zero_add], },
end 



-- theorem ftc2' 
--   (ha : a ∈ Ico a b)
--   (contf : continuous_on f (Icc a b)) 
--   (derivf : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ici x) x)
--   (contf' : continuous f') 
--   (intgf' : ∀ x ∈ Ico a b, interval_integrable f' volume a x) :
--   ∀ x ∈ Ico a b, ∫ y in a..x, f' y = f x - f a :=
-- begin 
--     intros x hx, apply eq_sub_of_add_eq, symmetry,
--     have hderiv := λ y hy, @integral_has_deriv_within_at_right 
--         _ _ _ _ _ _ _ _ _ _ (intgf' y hy) _ (Ioi y) (FTC_filter.nhds_right y) 
--         (continuous.continuous_within_at contf'),
--     refine (eq_of_right_deriv_eq derivf _ contf _  _) x hx,
--     { intros y hy, apply has_deriv_within_at.add_const,
--       exact (hderiv y hy), },
--     { refine continuous_on.add _ continuous_on_const,
--       intros z hz, 
--       apply has_deriv_within_at.continuous_within_at,
--        swap, 
--       exact (f' z),
--       have := hderiv a ha, sorry, },
--     { simp only [integral_same, zero_add], },
-- end 

-- theorem has_deriv_within_at_right_integrable
--   (contf : continuous_on f (Icc a b))
--   (derivf : ∀ x ∈ Ico a b, has_deriv_within_at f (f' x) (Ioi x) x)
--   (contf' : ∀ x ∈ Ico a b, continuous_within_at f' (Ioi x) x)
--   (intgf' : ∀ x ∈ Ico a b, interval_integrable f' volume a x) :
--   ∫ y in a..x, f' y = f x - f a :=
-- begin
--   --have hcts : continuous_on ((f a) + (∫ y in a..x, f' y)) (Icc a b) := sorry,
--   have := eq_of_right_deriv_eq derivf
--         ((integral_has_deriv_within_at_right intgf' contf').const_add (f a))
--           contf,
end