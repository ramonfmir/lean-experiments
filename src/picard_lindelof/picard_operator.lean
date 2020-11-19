import analysis.calculus.mean_value
import topology.continuous_map
import measure_theory.interval_integral
import topology.metric_space.contracting
import topology.metric_space.cau_seq_filter
import topology.bounded_continuous_function


-- Following Imperial's MA2AA1 notes and Ch 2 of 'Spectral Theory and Quantum Mechanics'.

noncomputable theory
open metric set asymptotics filter real measure_theory 
open interval_integral topological_space uniform_space
open_locale topological_space classical filter uniformity 

section picard_operator

-- NOTE: This is meant to be [a, b].
parameters {A : Type*} [topological_space A] [measurable_space A] [linear_order A]

parameter (μ : measure A)

-- NOTE: This is meant to be ℝ^n.
parameters {B : Type*} [normed_group B] [normed_space ℝ B] [measurable_space B]
                      [complete_space B] [second_countable_topology B] [borel_space B]
          

parameters (t0 : A) (f : A → B → B)

local infixr ` →ᵇ `:25 := bounded_continuous_function

-- Picard operator as a function.
def P_raw (x : A →ᵇ B) : A → B :=
λ t, (x t0) + ∫ s in t0..t, (f s (x s)) ∂μ

lemma P_raw.continuous 
: ∀ (x : A →ᵇ B), continuous (P_raw x) :=
begin 
    intros x, rw continuous_iff_continuous_at,
    intros a, unfold continuous_at,
    sorry, 
    -- Perhaps just deduce this from Lipschitz.
end 

lemma P_raw.bounded 
: ∀ (x : A →ᵇ B), ∃ C, ∀ (s t : A), dist (P_raw x s) (P_raw x t) ≤ C := 
sorry

def P : (A →ᵇ B) → (A →ᵇ B) :=
λ x, ⟨P_raw x, ⟨P_raw.continuous x, P_raw.bounded x⟩⟩ 

parameters (K : nnreal) (hK : K < 1)

lemma P.lipschitz : lipschitz_with K P :=
begin 
    sorry,
end 

def P.efixed_point : A →ᵇ B := 
contracting_with.efixed_point P ⟨hK, P.lipschitz⟩ sorry sorry

#check contracting_with.efixed_point

end picard_operator
