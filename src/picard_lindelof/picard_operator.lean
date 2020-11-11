import analysis.calculus.mean_value
import topology.continuous_map
import measure_theory.interval_integral

-- Banach fixed point theorem:
-- https://github.com/leanprover-community/mathlib/blob/f25340175631cdc85ad768a262433f968d0d6450/src/topology/metric_space/lipschitz.lean#L110

-- Following Imperial's MA2AA1 notes.

noncomputable theory
open metric set asymptotics filter real measure_theory interval_integral topological_space
open_locale topological_space classical filter

section picard_operator

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          [second_countable_topology E]
          [complete_space E] [measurable_space E]
          [borel_space E]

-- TODO: Should probably be from Icc a b. 
variables {t0 : ℝ} {f : ℝ → E → E}

def picard_operator_raw (x : C(ℝ, E)) :=
λ t, (x t0) + ∫ s in t0..t, (f s (x s))

lemma picard_operator_raw_continuous 
: ∀ (x : C(ℝ, E)), continuous (@picard_operator_raw E _ _ _ _ _ _ t0 f x) :=
sorry

def picard_operator : C(ℝ, E) → C(ℝ, E) :=
λ x, ⟨picard_operator_raw x, @picard_operator_raw_continuous E _ _ _ _ _ _ t0 f x⟩

instance : has_edist C(ℝ, E) := sorry
--⟨λ x y, supr (λ t, ∥(x t) - (y t)∥)⟩

instance : metric_space C(ℝ, E) := sorry

-- Ideally, we can show that it is a Banach space.
--instance : normed_group C(Icc a b, E) := sorry
--instance : normed_space ℝ C(Icc a b, E) := sorry
--instance : complete_space ℝ C(Icc a b, E) := sorry

variables (K : nnreal) (hK : K < 1)

lemma picard_operator_lischitz 
: lipschitz_with K (@picard_operator E _ _ _ _ _ _ t0 f) :=
sorry 

end picard_operator
