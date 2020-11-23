import measure_theory.interval_integral
import topology.bounded_continuous_function

-- Following Imperial's MA2AA1 notes and Ch 2 of 'Spectral Theory and Quantum Mechanics'.

noncomputable theory
open metric real set measure_theory interval_integral topological_space
open_locale topological_space  

section picard_operator

parameter (μ : measure ℝ)

-- NOTE: This is meant to be ℝ^n.
parameters {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E]
                       [complete_space E] [second_countable_topology E] [borel_space E]
                       [linear_order E] [metric_space E] -- Maybe

-- Initial value problem.
parameters (t₀ t₁ : ℝ) (x₀ : E) (v : ℝ → E → E) (x : ℝ → E) 
           (hx₀ : x t₀ = x₀) 
           (hx_cts : continuous_on x (Icc t₀ t₁))
           (hx_deriv : ∀ t ∈ Ico t₀ t₁, has_deriv_within_at x (v t (x t)) (Ioi t) t)

-- Assume v is globally lipshitz and bounded.
parameters (K : nnreal) (hK : K < 1)
           (hv_lipschitz : ∀ s, lipschitz_with K (v s))
           (hv_bdd : ∃ C, ∀ t ∈ Ico t₀ t₁, ∥v t (x t)∥ ≤ C)

local infixr ` →ᵇ `:25 := bounded_continuous_function

open bounded_continuous_function

-- The Picard operator as a function.
def P.to_fun (x : ℝ →ᵇ E) : ℝ → E := λ t, x₀ + ∫ s in t₀..t, v s (x s) ∂μ

-- lemma f.bounded : ∀ (a : ℝ), ∀ (x : ℝ →ᵇ B), ∃ C, ∀ s ∈ Icc , ∥f s (x s)∥ ≤ C :=
-- begin
--     -- let ε := 0,
--     -- intros a x, use ε, rintros s ⟨hslb, hsub⟩,
--     -- suffices hsuff : ∥((f s (x s)) - (f s (x a))) + (f s (x a))∥ ≤ ε,
--     -- { simp only [sub_add_cancel] at hsuff, exact hsuff, },
--     -- apply le_trans (norm_add_le _ (f s (x a))), rw ←dist_eq_norm, sorry,
--     -- I need something like continuous and on [a,b] then bounded.
--     intros a x, sorry,
-- end 

#print continuous_iff

-- The Picard operator is continuous.
lemma P.to_fun.continuous 
: ∀ (x : ℝ →ᵇ E), continuous (P.to_fun x) :=
begin 
    have hf' := λ s, lipschitz_with.continuous (hf_lipschitz s),
    intros x, 
    apply (@continuous_iff ℝ B _ _ (P.to_fun x)).2,
    intros a ε hε, 
    use [ε, hε],
    intros b hab,
    sorry,
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
