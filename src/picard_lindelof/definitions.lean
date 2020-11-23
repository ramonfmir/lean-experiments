import measure_theory.interval_integral
import topology.bounded_continuous_function

import picard_lindelof.other.interval_integral

-- Following Imperial's MA2AA1 notes and Ch 2 of 'Spectral Theory and Quantum Mechanics'.

noncomputable theory
open metric real set measure_theory interval_integral topological_space
open_locale topological_space  

section picard_operator

local infixr ` →ᵇ `:25 := bounded_continuous_function

-- NOTE: This is meant to be ℝ^n.
parameters {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                       [normed_space ℝ E] [complete_space E] [second_countable_topology E]

-- Initial value problem.
parameters (t₀ t₁ : ℝ) (x₀ : E) (v : ℝ → E → E) (x : ℝ →ᵇ E) 
           (hx₀ : x t₀ = x₀) (ht : t₀ ≤ t₁)
           (hx_cts : continuous_on x (Icc t₀ t₁))
           (hx_deriv : ∀ t ∈ Ioc t₀ t₁, has_deriv_within_at x (v t (x t)) (Ioi t) t)
           (hv_integrable : interval_integrable (λ t, v t (x t)) volume t₀ t₁)

-- Assume v is globally Lipshitz and bounded.
parameters (K : nnreal) (hK : K < 1)
           (hv_lipschitz : ∀ s, lipschitz_with K (v s))
           (hv_bdd : ∃ C, 0 < C ∧ ∀ t ∈ Ioc t₀ t₁, ∥v t (x t)∥ ≤ C)

open bounded_continuous_function

-- The Picard operator as a function.
def P.to_fun : ℝ → E := λ t, x₀ + ∫ s in t₀..t, v s (x s)

def P.to_fun.dist_eq (a b : ℝ)
: dist (P.to_fun a) (P.to_fun b) = ∥∫ s in a..b, v s (x s)∥ :=
begin 
    rw dist_eq_norm, simp only [P.to_fun],
    have hrw1 : 
        x₀ + (∫ s in t₀..a, v s (x s)) - (x₀ + ∫ s in t₀..b, v s (x s)) =
        (∫ s in t₀..a, v s (x s)) - (∫ s in t₀..b, v s (x s)) := by abel,
    rw hrw1, clear hrw1,
    rw [interval_integral.integral_symm a t₀],
    have hrw2 :
        -(∫ s in a..t₀, v s (x s)) - (∫ s in t₀..b, v s (x s)) =
        -((∫ s in a..t₀, v s (x s)) + (∫ s in t₀..b, v s (x s))) := by abel,
    rw hrw2, clear hrw2,
    have hadd :
        (∫ s in a..t₀, v s (x s)) + (∫ s in t₀..b, v s (x s)) =
        ∫ s in a..b, v s (x s), 
    { -- These can be proved from hv_integrable and integrable_on.mono.
      have hleft : interval_integrable (λ s, v s (x s)) volume a t₀ := sorry,
      have hright : interval_integrable (λ s, v s (x s)) volume t₀ b := sorry,
      exact (integral_add_adjacent_intervals hleft hright), },
    rw [hadd, norm_neg],
end

include ht hv_bdd

-- The Picard operator is continuous.
lemma P.to_fun.continuous_on 
: continuous_on P.to_fun (Icc t₀ t₁) :=
begin
    rcases hv_bdd with ⟨C, ⟨hCpos, hC⟩⟩,
    rw metric.continuous_on_iff,
    intros a ha ε hε, use [ε/C, div_pos hε hCpos],
    intros b hb hab, erw [P.to_fun.dist_eq a b],
    have hboundab : ∀ s, s ∈ Ioc (min b a) (max b a) → ∥v s (x s)∥ ≤ C,
    { by_cases (a ≤ b),
      { rw [min_eq_right h, max_eq_left h], intros s hs, apply (hC s), },
      { rw [min_eq_left h, max_eq_right h], intros s hs, sorry, }, },
    have hbound := interval_integral.norm_integral_le_of_norm_le_const hboundab,
    rw [dist_eq_norm, norm_eq_abs] at hab,
    replace hab := mul_lt_mul_of_pos_left hab hCpos,
    rw [←mul_div_assoc, mul_div_cancel_left ε (ne_of_lt hCpos).symm, abs_sub] at hab,
    exact lt_of_le_of_lt hbound hab,
end

lemma P.to_fun.continuous : continuous P.to_fun := sorry -- This is not true.

-- The Picard operator is bounded.
lemma P.to_fun.bounded : ∃ C, ∀ (a b : ℝ), dist (P.to_fun a) (P.to_fun b) ≤ C := 
begin
    sorry,
end

-- Picard operator.
def P : (ℝ →ᵇ E) → (ℝ →ᵇ E) :=
λ x, ⟨P.to_fun x, ⟨P.to_fun.continuous x, P.to_fun.bounded x⟩⟩ 

@[simp] lemma P.def (x : ℝ →ᵇ E) (t : ℝ) 
: P x t = x₀ + ∫ s in t₀..t, v s (x s) ∂μ := rfl

end picard_operator
