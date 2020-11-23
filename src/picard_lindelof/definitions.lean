import measure_theory.interval_integral
import topology.bounded_continuous_function

-- Following Imperial's MA2AA1 notes and Ch 2 of 'Spectral Theory and Quantum Mechanics'.

noncomputable theory
open metric real set measure_theory interval_integral topological_space
open_locale topological_space  

section picard_operator

parameter (μ : measure ℝ)

-- NOTE: This is meant to be ℝ^n.
parameters {B : Type*} [normed_group B] [normed_space ℝ B] [measurable_space B]
                       [complete_space B] [second_countable_topology B] [borel_space B]
                       [linear_order B] [metric_space B] -- Maybe
          

parameters (t0 : ℝ) (x0 : B) (f : ℝ → B → B)

parameters (K : nnreal) (hK : K < 1)

parameter (hf : ∀ s, lipschitz_with K (f s))

local infixr ` →ᵇ `:25 := bounded_continuous_function

open bounded_continuous_function

-- Picard operator as a function.
def P_raw (x : ℝ →ᵇ B) : ℝ → B := λ t, x0 + ∫ s in t0..t, (f s (x s)) ∂μ

include hf

#check @continuous_iff

set_option pp.private_names true

-- bounded_range_iff.1 $ bounded_of_compact $ compact_range hf
#check bounded_range_iff
#check @bounded_of_compact
#check @compact_range
#print bounded
#check @compact_range
#print interval_integral.norm_integral_le_of_norm_le_const
#check lipschitz_with
#print norm_add_le

lemma f.bounded : ∀ (a : ℝ), ∀ (x : ℝ →ᵇ B), ∃ C, ∀ s ∈ Icc t0 a, ∥f s (x s)∥ ≤ C :=
begin
    -- let ε := 0,
    -- intros a x, use ε, rintros s ⟨hslb, hsub⟩,
    -- suffices hsuff : ∥((f s (x s)) - (f s (x a))) + (f s (x a))∥ ≤ ε,
    -- { simp only [sub_add_cancel] at hsuff, exact hsuff, },
    -- apply le_trans (norm_add_le _ (f s (x a))), rw ←dist_eq_norm, sorry,
    -- I need something like continuous and on [a,b] then bounded.
    intros a x, have := bounded_of_compact,
end 

#print continuous_iff

lemma P_raw.continuous 
: ∀ (x : ℝ →ᵇ B), continuous (P_raw x) :=
begin 
    have hf' := λ s, lipschitz_with.continuous (hf s),
    intros x, 
    apply (@continuous_iff ℝ B _ _ (P_raw x)).2,
    intros a ε hε, 
    use [ε, hε],
    intros b hab,
    sorry,
end 

lemma P_raw.bounded 
: ∀ (x : ℝ →ᵇ B), ∃ C, ∀ (a b : ℝ), dist (P_raw x a) (P_raw x b) ≤ C := 
begin
    intros x, sorry,
end

def P : (ℝ →ᵇ B) → (ℝ →ᵇ B) :=
λ x, ⟨P_raw x, ⟨P_raw.continuous x, P_raw.bounded x⟩⟩ 

@[simp] lemma P_fn (x : ℝ →ᵇ B) (t : ℝ) 
: P x t = x0 + ∫ s in t0..t, (f s (x s)) ∂μ := rfl

end picard_operator
