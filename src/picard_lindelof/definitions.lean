import topology.bounded_continuous_function
import measure_theory.interval_integral

-- import picard_lindelof.other.interval_integral

-- Following Imperial's MA2AA1 notes.
-- Another useful resource: Oxford DE1 notes.

noncomputable theory
open nat metric real set measure_theory interval_integral topological_space filter
open_locale topological_space filter

namespace picard_operator

local infix ` →ᵇ `:25 := bounded_continuous_function 

def α : Type := subtype (Icc (-1 : ℝ) (1 : ℝ))

instance : has_zero α := ⟨⟨0, ⟨by linarith, by linarith⟩⟩⟩
instance : nonempty α := ⟨0⟩
instance : linear_order α := by unfold α; apply_instance
instance : topological_space α := by unfold α; apply_instance
instance : measurable_space α := by unfold α; apply_instance
instance : metric_space α := by unfold α; apply_instance
instance : opens_measurable_space α := subtype.opens_measurable_space _
instance : order_closed_topology α := {
  is_closed_le' := begin 
    -- TODO: Same technique can be used to prove a general statement about subtypes.
    apply is_open_prod_iff.mpr, rintros a b hab,
    replace hab : ¬ a ≤ b := hab,
    replace hab := lt_of_not_ge hab,
    cases a with a hIa, cases b with b hIb, simp at hab, 
    obtain ⟨u, v, hu, hv, hbu, hav, h⟩ := order_separated hab,
    use [{x : α | x.1 ∈ v}, {x : α | x.1 ∈ u}],
    refine ⟨_, _, _, _, _⟩,
    { rw is_open_iff at hv ⊢, intros x hx,
      rcases (hv x.val hx) with ⟨ε, H, hε⟩,
      use [ε, H], intros y hy, exact (hε hy), },
    { rw is_open_iff at hu ⊢, intros x hx,
      rcases (hu x.val hx) with ⟨ε, H, hε⟩,
      use [ε, H], intros y hy, exact (hε hy), },
    { exact hav, },
    { exact hbu, },
    { rintros ⟨x, y⟩ hxy, cases hxy with hx hy,
      dsimp at hx hy, simp, exact (h y.val hy x.val hx), },
  end
}

-- TODO: Move
lemma bdd_below_Icc {a b : ℝ} : bdd_below (Icc a b) := ⟨a, λ _, and.left⟩

-- TODO: Better compact_space α.
lemma compact_univ : is_compact (⊤ : set α) :=
begin
  erw compact_iff_compact_in_subtype, simp,
  rw compact_iff_closed_bounded, split,
  { exact is_closed_Icc, },
  { exact (bounded_iff_bdd_below_bdd_above.2 ⟨bdd_below_Icc, bdd_above_Icc⟩), },
end

instance : compact_space α := begin
  have hcompact := compact_univ,
  erw ←compact_iff_compact_univ at hcompact,
  exact compact_iff_compact_space.1 hcompact,
end

lemma dist_le_2 (a b : α) : dist a b ≤ 2 := begin
  obtain ⟨halb, haub⟩ := a.2, obtain ⟨hblb, hbub⟩ := b.2,
  erw [dist_eq_norm, norm_eq_abs], by_cases h : 0 ≤ a.val - b.val,
  { erw abs_of_nonneg h, linarith, },
  { erw abs_of_neg (lt_of_not_ge h), linarith, } 
end

instance : has_lift_t α ℝ := ⟨λ t, t.1⟩

-- Canonical measure. Hopefully not really needed.
def α.volume : measure α := begin 
  let v : measure ℝ := volume,
  let m : set α → ennreal := λ s, v.to_outer_measure.measure_of (coe '' s),
  apply measure.of_measurable (λ s _, m s),
  { dsimp [m], simp, },
  { dsimp [m], intros f hm hpw, 
    have h := v.m_Union, 
    -- Doable playing around with coe and so on.
    sorry, },
end

variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                      [normed_space ℝ E] [complete_space E] [second_countable_topology E]

-- Our 'nice' initial value problem. Quite strong, doesn't depend on x.
structure initial_value_problem (μ : measure α) (v : α → E → E) :=
(K : nnreal) (hK : K < 1) 
(hlipschitz : ∀ s, lipschitz_with K (v s))
(hbdd : ∀ y : α →ᵇ E, ∃ C, 0 < C ∧ ∀ t, ∥v t (y t)∥ ≤ C)
(hintegrable : ∀ y : α →ᵇ E, ∀ t, interval_integrable (λ s, v s (y s)) μ 0 t)

notation `IVP(` μ, v `)` := initial_value_problem μ v

open bounded_continuous_function

-- The Picard operator as a function.
def P.to_fun (μ : measure α) (v : α → E → E) (x : α →ᵇ E) : α → E := 
λ t, (x 0) + ∫ s in 0..t, v s (x s) ∂μ

-- Characterisation of distance between applications of P.
def P.to_fun.dist_eq (μ : measure α) (v : α → E → E) (I : IVP(μ, v)) (x : α →ᵇ E) (a b : α)
: dist (P.to_fun μ v x a) (P.to_fun μ v x b) = ∥∫ s in a..b, v s (x s) ∂μ∥ :=
begin 
    rw dist_eq_norm, simp only [P.to_fun],
    have hrw1 : 
        (x 0) + (∫ s in 0..a, v s (x s) ∂μ) - ((x 0) + ∫ s in 0..b, v s (x s) ∂μ) =
        (∫ s in 0..a, v s (x s) ∂μ) - (∫ s in 0..b, v s (x s) ∂μ) := by abel,
    rw hrw1, clear hrw1,
    rw [interval_integral.integral_symm a 0],
    have hrw2 :
        -(∫ s in a..0, v s (x s) ∂μ) - (∫ s in 0..b, v s (x s) ∂μ) =
        -((∫ s in a..0, v s (x s) ∂μ) + (∫ s in 0..b, v s (x s) ∂μ)) := by abel,
    rw hrw2, clear hrw2,
    have hadd :
        (∫ s in a..0, v s (x s) ∂μ) + (∫ s in 0..b, v s (x s) ∂μ) =
        ∫ s in a..b, v s (x s) ∂μ, 
    { -- These can be proved from hintegrable and integrable_on.mono.
      have hleft : interval_integrable (λ s, v s (x s)) μ a 0,
      { apply interval_integrable.symm, exact (I.hintegrable x a), },
      have hright : interval_integrable (λ s, v s (x s)) μ 0 b,
      { exact (I.hintegrable x b), },
      exact (integral_add_adjacent_intervals hleft hright), },
    rw [hadd, norm_neg],
end

--TODO: Move. This is not mathlib material though.
private lemma temp.norm_integral_le_of_norm_le_const_ae (μ : measure α) {a b : α} {C : ℝ} {f : α → E}
  (h : filter.eventually (λ x, x ∈ Ioc (min a b) (max a b) → ∥f x∥ ≤ C) μ.ae) :
  ∥∫ x in a..b, f x ∂μ∥ ≤ C * abs (b.val - a.val) :=
begin 
  rw [norm_integral_eq_norm_integral_Ioc],
  -- We can assume that our measure has this property. Or, preferably, define
  -- the canonical measure on α in terms of the canonical measure on ℝ.
  have hrw : ∀ {a b : α}, μ (Ioc a b) = ennreal.of_real (b.1 - a.1) := sorry,
  convert norm_set_integral_le_of_norm_le_const_ae'' _ is_measurable_Ioc h,
  { have hmax : (max a b).val = max a.val b.val := by unfold max; split_ifs; refl,
    have hmin : (min a b).val = min a.val b.val := by unfold min; split_ifs; refl,
    rw [hrw, hmax, hmin, max_sub_min_eq_abs, ennreal.to_real_of_real (abs_nonneg _)], },
  { simp only [hrw, ennreal.of_real_lt_top], }
end

private lemma temp.norm_integral_le_of_norm_le_const (μ : measure α) {a b : α} {C : ℝ} {f : α → E}
  (h : ∀ x ∈ Ioc (min a b) (max a b), ∥f x∥ ≤ C) :
  ∥∫ x in a..b, f x ∂μ∥ ≤ C * abs (b.val - a.val) :=
temp.norm_integral_le_of_norm_le_const_ae μ (filter.eventually_of_forall h)

-- The Picard operator is continuous!
lemma P.to_fun.continuous (μ : measure α) (v : α → E → E) (I : IVP(μ, v)) (x : α →ᵇ E) 
: continuous (P.to_fun μ v x) :=
begin
    rcases (I.hbdd x) with ⟨C, ⟨hCpos, hC⟩⟩,
    rw metric.continuous_iff,
    intros a ε hε, use [ε/C, div_pos hε hCpos],
    intros b hab, rw [P.to_fun.dist_eq μ v I x],
    have hboundab : ∀ s, s ∈ Ioc (min b a) (max b a) → ∥v s (x s)∥ ≤ C,
    { by_cases (a ≤ b),
      { rw [min_eq_right h, max_eq_left h], 
        intros s hs, apply (hC s), },
      { rw [min_eq_left (le_of_not_le h), max_eq_right (le_of_not_le h)], 
        intros s hs, apply (hC s), }, },
    have hbound := temp.norm_integral_le_of_norm_le_const μ hboundab,
    erw [dist_eq_norm, norm_eq_abs] at hab,
    replace hab := mul_lt_mul_of_pos_left hab hCpos,
    rw [←mul_div_assoc, mul_div_cancel_left ε (ne_of_lt hCpos).symm, abs_sub] at hab,
    exact lt_of_le_of_lt hbound hab,
end

-- The Picard operator is bounded.
lemma P.to_fun.bounded (μ : measure α) (v : α → E → E) (I : IVP(μ, v)) (x : α →ᵇ E) 
: ∃ C, ∀ a b, dist (P.to_fun μ v x a) (P.to_fun μ v x b) ≤ C := 
begin 
  rcases (I.hbdd x) with ⟨C, ⟨hCpos, hC⟩⟩, use [C * 2],
  intros a b, rw [P.to_fun.dist_eq μ v I x],
  -- Note that this is the same as for continuity. Generalise.
  have hboundab : ∀ s, s ∈ Ioc (min a b) (max a b) → ∥v s (x s)∥ ≤ C,
  { by_cases (b ≤ a),
    { rw [min_eq_right h, max_eq_left h], 
      intros s hs, apply (hC s), },
    { rw [min_eq_left (le_of_not_le h), max_eq_right (le_of_not_le h)], 
      intros s hs, apply (hC s), }, },
  have hbound := temp.norm_integral_le_of_norm_le_const μ hboundab,
  suffices hsuff : abs (b.val - a.val) ≤ 2,
  { have hC2 := (mul_le_mul_left hCpos).2 hsuff, 
    exact (le_trans hbound hC2), },
  rw [←norm_eq_abs, ←dist_eq_norm],
  exact dist_le_2 b a,
end

-- Picard operator.
def P (μ : measure α) (v : α → E → E) (I : IVP(μ, v)) : (α →ᵇ E) → (α →ᵇ E) :=
λ x, ⟨P.to_fun μ v x, ⟨P.to_fun.continuous μ v I x, P.to_fun.bounded μ v I x⟩⟩

-- Definition of application.
@[simp] lemma P.def (μ : measure α) (v : α → E → E) (I : IVP(μ, v)) (x : α →ᵇ E) (t : α)
: P μ v I x t = (x 0) + ∫ s in 0..t, v s (x s) ∂μ := rfl

end picard_operator

namespace picard_operator_recursive

open nat picard_operator

variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                      [normed_space ℝ E] [complete_space E] [second_countable_topology E]

noncomputable def P.recursive (v : ℝ → E → E) (x₀ : E) : ℕ → (ℝ → E)
| 0     := λ t, x₀
| (n+1) := λ t, x₀ + (∫ s in (0 : ℝ)..(t : ℝ), v s (P.recursive n s))

end picard_operator_recursive
