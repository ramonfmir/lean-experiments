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
def P_raw (x : A →ᵇ B) : A → B := λ t, (x t0) + ∫ s in t0..t, (f s (x s)) ∂μ

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

-- TODO: Move.
private lemma ennreal.of_real_supr 
{ι : Type*} [nonempty ι] (f : ι → ℝ) (hbdd : bdd_above (range f))
: ennreal.of_real (supr f) = supr (λ t, ennreal.of_real (f t)) := 
begin
    have hcts : continuous_at ennreal.of_real (supr f),
    { exact (continuous_iff_continuous_at.1 ennreal.continuous_of_real _), },
    have hmono : monotone ennreal.of_real,
    { intros a b, exact ennreal.of_real_le_of_real, },
    exact (map_csupr_of_continuous_at_of_monotone hcts hmono hbdd),
end 

open bounded_continuous_function

lemma P.edist_eq_supr (x y : A →ᵇ B) 
: edist (P x) (P y) = supr (λ t, edist (P x t) (P y t)) :=
begin
    --unfold edist, unfold metric_space.edist, 
    apply le_antisymm,
    { have := λ t, @dist_coe_le_dist A B _ _ x y t, },
    { sorry, },
end 

parameters (K : nnreal) (hK : K < 1)

lemma P.lipschitz_at_of_lipshitz (hf : ∀ s, lipschitz_with K (f s)) (t : A)
: lipschitz_with K (λ x, P x t) :=
begin 
    intros x y, simp, sorry,
end

lemma P.lipschitz_of_lipschitz (hf : ∀ s, lipschitz_with K (f s))
: lipschitz_with K P :=
begin 
    intros x y,
    calc edist (P x) (P y) 
        = supr (λ t, edist (P x t) (P y t)) : P.edist_eq_supr x y
    ... ≤ ↑K * edist x y : supr_le (λ t, P.lipschitz_at_of_lipshitz hf t x y),
end 

def P.efixed_point : A →ᵇ B := 
contracting_with.efixed_point P ⟨hK, P.lipschitz⟩ sorry sorry

#check contracting_with.efixed_point

end picard_operator
