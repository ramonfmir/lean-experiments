import measure_theory.interval_integral
import topology.bounded_continuous_function

-- Following Imperial's MA2AA1 notes and Ch 2 of 'Spectral Theory and Quantum Mechanics'.

noncomputable theory
open metric real set measure_theory interval_integral topological_space
open_locale topological_space  

section picard_operator

parameter (μ : measure ℝ)

-- NOTE: This is meant to be ℝ^n.
parameters {E : Type*} [measurable_space E] [normed_group E] [borel_space E]
                       [normed_space ℝ E] [complete_space E] [second_countable_topology E]

-- Initial value problem.
parameters (t₀ t₁ : ℝ) (x₀ : E) (v : ℝ → E → E) (x : ℝ → E) 
           (hx₀ : x t₀ = x₀) 
           (hx_cts : continuous_on x (Icc t₀ t₁))
           (hx_deriv : ∀ t ∈ Ico t₀ t₁, has_deriv_within_at x (v t (x t)) (Ioi t) t)
           (hv_integrable : interval_integrable (λ t, v t (x t)) μ t₀ t₁)

-- Assume v is globally Lipshitz and bounded.
parameters (K : nnreal) (hK : K < 1)
           (hv_lipschitz : ∀ s, lipschitz_with K (v s))
           (hv_bdd : ∃ C, ∀ t ∈ Ico t₀ t₁, ∥v t (x t)∥ ≤ C)

local infixr ` →ᵇ `:25 := bounded_continuous_function

open bounded_continuous_function

-- The Picard operator as a function.
def P.to_fun (x : ℝ →ᵇ E) : ℝ → E := λ t, x₀ + ∫ s in t₀..t, v s (x s) ∂μ

def P.to_fun.dist_eq (x : ℝ →ᵇ E) (a b : ℝ) (h : b ≤ a) 
: dist (P.to_fun x a) (P.to_fun x b) = ∥∫ s in a..b, v s (x s) ∂μ∥ :=
begin 
    rw dist_eq_norm, simp only [P.to_fun],
    have hrw1 : 
        x₀ + ∫ s in t₀..a, v s (x s) ∂μ - (x₀ + ∫ s in t₀..b, v s (x s) ∂μ) =
        ∫ s in t₀..a, v s (x s) ∂μ - ∫ s in t₀..b, v s (x s) ∂μ := by abel,
    rw hrw1, clear hrw1,
    rw [interval_integral.integral_symm a t₀],
    have hrw2 :
        -∫ s in a..t₀, v s (x s) ∂μ - ∫ s in t₀..b, v s (x s) ∂μ =
        -(∫ s in a..t₀, v s (x s) ∂μ + ∫ s in t₀..b, v s (x s) ∂μ) := by abel,
    rw hrw2, clear hrw2,
    have hadd :
        (∫ s in a..t₀, v s (x s) ∂μ) + (∫ s in t₀..b, v s (x s) ∂μ) =
        ∫ s in a..b, v s (x s) ∂μ, 
    { -- These can be proved from hv_integrable and integrable_on.mono.
      have hleft : interval_integrable (λ s, v s (x s)) μ a t₀ := sorry,
      have hright : interval_integrable (λ s, v s (x s)) μ t₀ b := sorry,
      exact (integral_add_adjacent_intervals hleft hright), },
    rw [hadd, norm_neg],
end

-- The Picard operator is continuous.
lemma P.to_fun.continuous 
: ∀ (x : ℝ →ᵇ E), continuous (P.to_fun x) :=
begin
    intros x, apply (@continuous_iff ℝ E _ _ (P.to_fun x)).2,
    intros a ε hε, use [ε, hε],
    intros b hab, rw dist_eq_norm, simp only [P.to_fun],

end

-- The Picard operator is bounded.
lemma P.to_fun.bounded 
: ∀ (x : ℝ →ᵇ E), ∃ C, ∀ (a b : ℝ), dist (P.to_fun x a) (P.to_fun x b) ≤ C := 
begin
    intros x, sorry,
end

-- Picard operator.
def P : (ℝ →ᵇ E) → (ℝ →ᵇ E) :=
λ x, ⟨P.to_fun x, ⟨P.to_fun.continuous x, P.to_fun.bounded x⟩⟩ 

@[simp] lemma P.def (x : ℝ →ᵇ E) (t : ℝ) 
: P x t = x₀ + ∫ s in t₀..t, v s (x s) ∂μ := rfl

end picard_operator
