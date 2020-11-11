import analysis.calculus.mean_value
import measure_theory.interval_integral

-- Banach fixed point theorem:
-- https://github.com/leanprover-community/mathlib/blob/f25340175631cdc85ad768a262433f968d0d6450/src/topology/metric_space/lipschitz.lean#L110

noncomputable theory
open metric set asymptotics filter real measure_theory interval_integral topological_space
open_locale topological_space classical filter

section picard_operator

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          [second_countable_topology E]
          [complete_space E] [measurable_space E]
          [borel_space E]

-- 
variables {t0 : ℝ} {f : ℝ → E → E}

def picard_operator (x : C(ℝ, E)) :=
λ t, (x t0) + ∫ s in t0..t, f s (x s)

--instance : has_edist C(ℝ, E) :=
--⟨λ x y, ∣(x 0) - (y 0)∣⟩

instance : emetric_space C(ℝ, E) := sorry

variables (K : nnreal) (hK : K < 1)

lemma picard_operator_lischitz 
: ∀ t, lipschitz_with K (λ x, @picard_operator E _ _ _ _ _ _ t0 f x t)


end picard_operator
