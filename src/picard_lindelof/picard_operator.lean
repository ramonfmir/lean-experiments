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

-- NOTE: This is meant to be [a, b].
variables {A : Type*} [linear_order A] [measurable_space A]
          [topological_space A] [compact_space A]

variables (μ : measure A)

-- NOTE: This is meant to be ℝ^n.
variables {B : Type*} [normed_group B] [normed_space ℝ B]
          [second_countable_topology B]
          [complete_space B] [measurable_space B]
          [borel_space B]

variables (t0 : A) (f : A → B → B)

def picard_operator_raw (x : C(A, B)) :=
λ t, (x t0) + ∫ s in t0..t, (f s (x s)) ∂μ

#check nhds_basis_ball.tendsto_iff
#check nhds_basis_ball.tendsto_iff nhds_basis_closed_ball

lemma picard_operator_raw_continuous 
: ∀ (x : C(A, B)), continuous (picard_operator_raw μ t0 f x) :=
begin 
    intros x,
    rw continuous_iff_continuous_at,
    intros a,
    unfold continuous_at,
    sorry,
end 

def picard_operator : C(A, B) → C(A, B) :=
λ x, ⟨picard_operator_raw μ t0 f x, picard_operator_raw_continuous μ t0 f x⟩

instance : has_edist C(A, B) := sorry
--⟨λ x y, supr (λ t, ∥(x t) - (y t)∥)⟩

instance : metric_space C(A, B) := sorry

-- Ideally, we can show that it is a Banach space.
--instance : normed_group C(Icc a b, E) := sorry
--instance : normed_space ℝ C(Icc a b, E) := sorry
--instance : complete_space ℝ C(Icc a b, E) := sorry

variables (K : nnreal) (hK : K < 1)

lemma picard_operator_lipschitz 
: lipschitz_with K (picard_operator μ t0 f) :=
sorry 

end picard_operator
