import topology.bounded_continuous_function
import measure_theory.interval_integral

import picard_lindelof.domain
import picard_lindelof.other.interval_integral

-- Following Imperial's MA2AA1 notes.
-- Another useful resource: Oxford DE1 notes.

noncomputable theory
open nat metric real set measure_theory interval_integral topological_space filter
open_locale topological_space filter

namespace picard_operator

local infix ` →ᵇ `:25 := bounded_continuous_function 

variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                      [normed_space ℝ E] [complete_space E] [second_countable_topology E]

-- Our 'nice' initial value problem. Quite strong, doesn't depend on x.
structure initial_value_problem (v : α → E → E) :=
(K : nnreal) (hK : K < 1) 
(hlipschitz : ∀ s, lipschitz_with K (v s))
(hbdd : ∀ y : α →ᵇ E, ∃ C, 0 < C ∧ ∀ t, ∥v t (y t)∥ ≤ C)
(hintegrable : ∀ y : α →ᵇ E, ∀ t, interval_integrable (λ s, v s (y s)) volume 0 t)

notation `IVP(` v `)` := initial_value_problem v

open bounded_continuous_function

-- The Picard operator as a function.
def P.to_fun (x₀ : E) (v : α → E → E) (x : α →ᵇ E) : α → E := 
λ t, x₀ + ∫ s in 0..t, v s (x s)

-- Characterisation of distance between applications of P.
def P.to_fun.dist_eq (x₀ : E) (v : α → E → E) (I : IVP(v)) (x : α →ᵇ E) (a b : α)
: dist (P.to_fun x₀ v x a) (P.to_fun x₀ v x b) = ∥∫ s in a..b, v s (x s)∥ :=
begin 
    rw dist_eq_norm, simp only [P.to_fun],
    have hrw1 : 
        x₀ + (∫ s in 0..a, v s (x s)) - (x₀ + ∫ s in 0..b, v s (x s)) =
        (∫ s in 0..a, v s (x s)) - (∫ s in 0..b, v s (x s)) := by abel,
    rw hrw1, clear hrw1,
    rw [interval_integral.integral_symm a 0],
    have hrw2 :
        -(∫ s in a..0, v s (x s)) - (∫ s in 0..b, v s (x s)) =
        -((∫ s in a..0, v s (x s)) + (∫ s in 0..b, v s (x s))) := by abel,
    rw hrw2, clear hrw2,
    have hadd :
        (∫ s in a..0, v s (x s)) + (∫ s in 0..b, v s (x s)) =
        ∫ s in a..b, v s (x s), 
    { -- These can be proved from hintegrable and integrable_on.mono.
      have hleft : interval_integrable (λ s, v s (x s)) volume a 0,
      { apply interval_integrable.symm, exact (I.hintegrable x a), },
      have hright : interval_integrable (λ s, v s (x s)) volume 0 b,
      { exact (I.hintegrable x b), },
      exact (integral_add_adjacent_intervals hleft hright), },
    rw [hadd, norm_neg],
end

-- The Picard operator is continuous!
lemma P.to_fun.continuous (x₀ : E) (v : α → E → E) (I : IVP(v)) (x : α →ᵇ E) 
: continuous (P.to_fun x₀ v x) :=
begin
    rcases (I.hbdd x) with ⟨C, ⟨hCpos, hC⟩⟩,
    rw metric.continuous_iff,
    intros a ε hε, use [ε/C, div_pos hε hCpos],
    intros b hab, rw [P.to_fun.dist_eq x₀ v I x],
    have hboundab : ∀ s, s ∈ Ioc (min b a) (max b a) → ∥v s (x s)∥ ≤ C,
    { by_cases (a ≤ b),
      { rw [min_eq_right h, max_eq_left h], 
        intros s hs, apply (hC s), },
      { rw [min_eq_left (le_of_not_le h), max_eq_right (le_of_not_le h)], 
        intros s hs, apply (hC s), }, },
    have hbound := temp.norm_integral_le_of_norm_le_const hboundab,
    erw [dist_eq_norm, norm_eq_abs] at hab,
    replace hab := mul_lt_mul_of_pos_left hab hCpos,
    rw [←mul_div_assoc, mul_div_cancel_left ε (ne_of_lt hCpos).symm, abs_sub] at hab,
    exact lt_of_le_of_lt hbound hab,
end

-- The Picard operator is bounded.
lemma P.to_fun.bounded (x₀ : E) (v : α → E → E) (I : IVP(v)) (x : α →ᵇ E) 
: ∃ C, ∀ a b, dist (P.to_fun x₀ v x a) (P.to_fun x₀ v x b) ≤ C := 
begin 
  rcases (I.hbdd x) with ⟨C, ⟨hCpos, hC⟩⟩, use [C * 2],
  intros a b, rw [P.to_fun.dist_eq x₀ v I x],
  -- Note that this is the same as for continuity. Generalise.
  have hboundab : ∀ s, s ∈ Ioc (min a b) (max a b) → ∥v s (x s)∥ ≤ C,
  { by_cases (b ≤ a),
    { rw [min_eq_right h, max_eq_left h], 
      intros s hs, apply (hC s), },
    { rw [min_eq_left (le_of_not_le h), max_eq_right (le_of_not_le h)], 
      intros s hs, apply (hC s), }, },
  have hbound := temp.norm_integral_le_of_norm_le_const hboundab,
  suffices hsuff : abs (b.val - a.val) ≤ 2,
  { have hC2 := (mul_le_mul_left hCpos).2 hsuff, 
    exact (le_trans hbound hC2), },
  rw [←norm_eq_abs, ←dist_eq_norm],
  exact dist_le_2 b a,
end

-- Picard operator.
def P (x₀ : E) (v : α → E → E) (I : IVP(v)) : (α →ᵇ E) → (α →ᵇ E) :=
λ x, ⟨P.to_fun x₀ v x, ⟨P.to_fun.continuous x₀ v I x, P.to_fun.bounded x₀ v I x⟩⟩

-- Definition of application.
@[simp] lemma P.def (x₀ : E) (v : α → E → E) (I : IVP(v)) (x : α →ᵇ E) (t : α)
: P x₀ v I x t = x₀ + ∫ s in 0..t, v s (x s) := rfl

end picard_operator

namespace picard_operator_recursive

open nat picard_operator

variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                      [normed_space ℝ E] [complete_space E] [second_countable_topology E]

noncomputable def P.recursive (v : ℝ → E → E) (x₀ : E) : ℕ → (ℝ → E)
| 0     := λ t, x₀
| (n+1) := λ t, x₀ + (∫ s in 0..t, v s (P.recursive n s))

end picard_operator_recursive
