import measure_theory.interval_integral
import measure_theory.integration
import topology.basic

import picard_lindelof.domain

open set measure_theory topological_space interval_integral

variables {E : Type*} 
    [normed_field E] [normed_space ℝ E] [second_countable_topology E] 
    [measurable_space E] [linear_order E] [complete_space E] [borel_space E]

lemma temp.norm_integral_le_integral_norm_Ioc_of_le
{a b : α} {f : α → E} {μ : measure α} (h : a ≤ b)
: ∥∫ x in a..b, f x ∂μ∥ ≤ ∫ x in a..b, ∥f x∥ ∂μ :=
begin 
    rw [integral_of_le h, integral_of_le h],
    have hle := @norm_integral_le_integral_norm_Ioc α E _ _ _ _ _ _ _ _ a b f μ,
    rw [integral_of_le h, max_eq_right h, min_eq_left h] at hle,
    exact hle,
end 

--TODO: Move. 
lemma temp.norm_integral_le_of_norm_le_const_ae {a b : α} {C : ℝ} {f : α → E}
  (h : filter.eventually (λ x, x ∈ Ioc (min a b) (max a b) → ∥f x∥ ≤ C) volume.ae) :
  ∥∫ x in a..b, f x∥ ≤ C * abs (b.val - a.val) :=
begin 
  rw [norm_integral_eq_norm_integral_Ioc],
  have hrw : ∀ {a b : α}, volume (Ioc a b) = ennreal.of_real (b.1 - a.1) := λ a b, α.volume_Ioc,
  convert norm_set_integral_le_of_norm_le_const_ae'' _ is_measurable_Ioc h,
  { have hmax : (max a b).val = max a.val b.val := by unfold max; split_ifs; refl,
    have hmin : (min a b).val = min a.val b.val := by unfold min; split_ifs; refl,
    rw [hrw, hmax, hmin, max_sub_min_eq_abs, ennreal.to_real_of_real (abs_nonneg _)], },
  { simp only [hrw, ennreal.of_real_lt_top], }
end

lemma temp.norm_integral_le_of_norm_le_const {a b : α} {C : ℝ} {f : α → E}
  (h : ∀ x ∈ Ioc (min a b) (max a b), ∥f x∥ ≤ C) :
  ∥∫ x in a..b, f x∥ ≤ C * abs (b.val - a.val) :=
temp.norm_integral_le_of_norm_le_const_ae (filter.eventually_of_forall h)

-- TODO: Move
variables {α : Type*} [measurable_space α] 
variables {μ : measure α}

#check has_finite_integral_iff_of_real
#check @ennreal.exists_inv_nat_lt 
#check @measure_theory.integral_eq_zero_of_ae
#print normed_space
#check le_integral

lemma integral_eq_zero_iff_of_nonneg_ae' {f : α → E} (hf : 0 ≤ᵐ[μ] f) (hfi : integrable f μ) :
  ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
begin 
  split, 
  { intros h,
    have : ∀n:ℕ, ∀ᵐ a ∂μ, f a < n⁻¹,
    { intros n, rw [ae_iff, ←le_zero_iff_eq], 
      simp only [not_lt],
      sorry, },
    refine (ae_all_iff.2 this).mono (λ a ha, _),
    by_contradiction h, sorry, },
  { intros h, convert integral_eq_zero_of_ae h, },
end

-- @[simp] lemma lintegral_eq_zero_iff {f : α → ennreal} (hf : measurable f) :
--   ∫⁻ a, f a ∂μ = 0 ↔ (f =ᵐ[μ] 0) :=
-- begin
--   refine iff.intro (assume h, _) (assume h, _),
--   { have : ∀n:ℕ, ∀ᵐ a ∂μ, f a < n⁻¹,
--     { assume n,
--       rw [ae_iff, ← le_zero_iff_eq, ← @ennreal.zero_div n⁻¹,
--         ennreal.le_div_iff_mul_le, mul_comm],
--       simp only [not_lt],
--       -- TODO: why `rw ← h` fails with "not an equality or an iff"?
--       exacts [h ▸ mul_meas_ge_le_lintegral hf n⁻¹,
--         or.inl (ennreal.inv_ne_zero.2 ennreal.coe_nat_ne_top),
--         or.inr ennreal.zero_ne_top] },
--     refine (ae_all_iff.2 this).mono (λ a ha, _),
--     by_contradiction h,
--     rcases ennreal.exists_inv_nat_lt h with ⟨n, hn⟩,
--     exact (lt_irrefl _ $ lt_trans hn $ ha n).elim },
--   { calc ∫⁻ a, f a ∂μ = ∫⁻ a, 0 ∂μ : lintegral_congr_ae h
--       ... = 0 : lintegral_zero }
-- end

--integral_eq_zero_iff_of_nonneg_ae

lemma integral_eq_zero_iff_of_le_of_nonneg_ae' {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
  (hf : 0 ≤ᵐ[volume.restrict (Ioc a b)] f) (hfi : interval_integrable f volume a b) :
  ∫ x in a..b, f x = 0 ↔ f =ᵐ[volume.restrict (Ioc a b)] 0 :=
by rw [integral_of_le hab, integral_eq_zero_iff_of_nonneg_ae' hf hfi.1] 

-- lemma temp.integral_mono_ae {f g : α → E} (a b : α)
-- (hf : interval_integrable f volume a b) (hg : interval_integrable g volume a b) (h : f ≤ᵐ[volume] g)
-- : ∫ t in a..b, f t ≤ ∫ t in a..b, g t := sorry

-- lemma temp.integral_mono {f g : α → E} (a b : α)
-- (hf : interval_integrable f volume a b) (hg : interval_integrable g volume a b) (h : f ≤ g)
-- : ∫ t in a..b, f t ≤ ∫ t in a..b, g t := sorry
