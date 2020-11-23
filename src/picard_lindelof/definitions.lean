import measure_theory.interval_integral
import topology.bounded_continuous_function

-- Following Imperial's MA2AA1 notes and Ch 2 of 'Spectral Theory and Quantum Mechanics'.

noncomputable theory
open metric real measure_theory interval_integral topological_space
open_locale topological_space  

section picard_operator

-- NOTE: This is meant to be [a, b].
parameters {A : Type*} [linear_order A] [measurable_space A]
           [metric_space A] [compact_space A] [nonempty A]

parameter (μ : measure A)

-- NOTE: This is meant to be ℝ^n.
parameters {B : Type*} [normed_group B] [normed_space ℝ B] [measurable_space B]
                       [complete_space B] [second_countable_topology B] [borel_space B]
                       [linear_order B] [metric_space B] -- Maybe
          

parameters (t0 : A) (x0 : B) (f : A → B → B)

parameters (K : nnreal) (hK : K < 1)

parameter (hf : ∀ s, lipschitz_with K (f s))

local infixr ` →ᵇ `:25 := bounded_continuous_function

open bounded_continuous_function

-- Picard operator as a function.
def P_raw (x : A →ᵇ B) : A → B := λ t, x0 + ∫ s in t0..t, (f s (x s)) ∂μ

include hf

#check @continuous_iff

set_option pp.private_names true

-- bounded_range_iff.1 $ bounded_of_compact $ compact_range hf
#check bounded_range_iff
#check bounded_of_compact
#check @compact_range
#check lipschitz_with.continuous

lemma P_raw.continuous 
: ∀ (x : A →ᵇ B), continuous (P_raw x) :=
begin 
    have hf' := λ s, lipschitz_with.continuous (hf s),
    intros x, 
    apply continuous_iff.2,
    intros a ε hε, 
    use [ε, hε],
    intros b hab,
    sorry,
end 

lemma P_raw.bounded 
: ∀ (x : ℝ →ᵇ B), ∃ C, ∀ (a b : ℝ), dist (P_raw x a) (P_raw x b) ≤ C := 
begin
    intros x,
end

def P : (ℝ →ᵇ B) → (ℝ →ᵇ B) :=
λ x, ⟨P_raw x, ⟨P_raw.continuous x, P_raw.bounded x⟩⟩ 

@[simp] lemma P_fn (x : ℝ →ᵇ B) (t : ℝ) 
: P x t = x0 + ∫ s in t0..t, (f s (x s)) ∂μ := rfl

end picard_operator
