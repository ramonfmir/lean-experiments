import topology.bounded_continuous_function
import measure_theory.interval_integral

-- import picard_lindelof.other.interval_integral

-- Following Imperial's MA2AA1 notes.
-- Another useful resource: Oxford DE1 notes.

noncomputable theory
open nat metric real set measure_theory interval_integral topological_space
open_locale topological_space  

notation `C(` A `)` := bounded_continuous_function ℝ A

-- P : C(A) -> C(A)

namespace picard_operator

variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                      [normed_space ℝ E] [complete_space E] [second_countable_topology E]

variable (v : ℝ → E → E)

-- Our 'nice' initial value problem. Quite strong, doesn't depend on x.
structure initial_value_problem (v : ℝ → E → E) :=
(K : nnreal) (hK : K < 1) 
(hlipschitz : ∀ s, lipschitz_with K (v s))
(hbdd : ∀ y : C(E), ∃ C, 0 < C ∧ ∀ t ∈ Ioc (0 : ℝ) (1 : ℝ), ∥v t (y t)∥ ≤ C)
(hintegrable : ∀ y : C(E), ∀ t ∈ Ioc (0 : ℝ) (1 : ℝ), interval_integrable (λ s, v s (y s)) volume 0 t)

notation `IVP(` v `)` := initial_value_problem v

open bounded_continuous_function

-- The Picard operator as a function.
def P.to_fun (v : ℝ → E → E) (x : C(E)) : ℝ → E := 
λ t, (x 0) + ∫ s in 0..t, v s (x s)

-- Characterisation of distance between applications of P.
def P.to_fun.dist_eq (v : ℝ → E → E) (x : C(E)) (a b : ℝ)
: dist (P.to_fun v x a) (P.to_fun v x b) = ∥∫ s in a..b, v s (x s)∥ :=
begin 
    rw dist_eq_norm, simp only [P.to_fun],
    have hrw1 : 
        (x 0) + (∫ s in 0..a, v s (x s)) - ((x 0) + ∫ s in 0..b, v s (x s)) =
        (∫ s in 0..a, v s (x s)) - (∫ s in 0..b, v s (x s)) := by abel,
    rw hrw1, clear hrw1,
    rw [interval_integral.integral_symm a 0],
    have hrw2 :
        -(∫ s in a..0, v s (x s)) - (∫ s in 0..b, v s (x s)) =
        -((∫ s in a..0, v s (x s)) + (∫ s in 0..b, v s (x s))) := by abel,
    rw hrw2, clear hrw2,
    have hadd :
        (∫ s in a..0, v s (x s)) + (∫ s in 0..b, v s (x s)) =
        ∫ s in a..b, v s (x s), 
    { -- These can be proved from hintegrable and integrable_on.mono.
      have hleft : interval_integrable (λ s, v s (x s)) volume a 0 := sorry,
      have hright : interval_integrable (λ s, v s (x s)) volume 0 b := sorry,
      exact (integral_add_adjacent_intervals hleft hright), },
    rw [hadd, norm_neg],
end

-- The Picard operator is continuous on [0, 1].
lemma P.to_fun.continuous_on (v : ℝ → E → E) (I : IVP(v)) (x : C(E)) 
: continuous_on (P.to_fun v x) (Icc 0 1) :=
begin
    rcases (I.hbdd x) with ⟨C, ⟨hCpos, hC⟩⟩,
    rw metric.continuous_on_iff,
    intros a ha ε hε, use [ε/C, div_pos hε hCpos],
    intros b hb hab, rw [P.to_fun.dist_eq v x],
    have hboundab : ∀ s, s ∈ Ioc (min b a) (max b a) → ∥v s (x s)∥ ≤ C,
    { by_cases (a ≤ b),
      { rw [min_eq_right h, max_eq_left h], 
        intros s hs, apply (hC s), 
        have hlb := lt_of_le_of_lt ha.1 hs.1,
        have hub := le_trans hs.2 hb.2,
        exact ⟨hlb, hub⟩, },
      { rw [min_eq_left (le_of_not_le h), max_eq_right (le_of_not_le h)], 
        intros s hs, apply (hC s),
        replace h := le_of_not_le h,
        have hlb := lt_of_le_of_lt hb.1 hs.1,
        have hub := le_trans hs.2 ha.2,
        exact ⟨hlb, hub⟩, }, },
    have hbound := interval_integral.norm_integral_le_of_norm_le_const hboundab,
    rw [dist_eq_norm, norm_eq_abs] at hab,
    replace hab := mul_lt_mul_of_pos_left hab hCpos,
    rw [←mul_div_assoc, mul_div_cancel_left ε (ne_of_lt hCpos).symm, abs_sub] at hab,
    exact lt_of_le_of_lt hbound hab,
end

-- The Picard operator is continuous.
lemma P.to_fun.continuous (v : ℝ → E → E) (I : IVP(v)) (x : C(E)) 
: continuous (P.to_fun v x) := sorry -- This is false?

-- The Picard operator is bounded.
lemma P.to_fun.bounded (v : ℝ → E → E) (I : IVP(v)) (x : C(E)) 
: ∃ C, ∀ (a b : ℝ), dist (P.to_fun v x a) (P.to_fun v x b) ≤ C := sorry
-- IDEA: If we assume function.suport x ⊆ [0, 1], a lot of this might work. 

-- Picard operator.
def P (v : ℝ → E → E) (I : IVP(v)) : C(E) → C(E) :=
λ x, ⟨P.to_fun v x, ⟨P.to_fun.continuous v I x, P.to_fun.bounded v I x⟩⟩

-- Simplification lemma
@[simp] lemma P.def (v : ℝ → E → E) (I : IVP(v)) (x : C(E)) (t : ℝ)
: P v I x t = (x 0) + ∫ s in 0..t, v s (x s) := rfl

end picard_operator

namespace picard_operator_recursive

open nat picard_operator

variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                      [normed_space ℝ E] [complete_space E] [second_countable_topology E]

noncomputable def P.recursive (v : ℝ → E → E) (x₀ : E) : ℕ → (ℝ → E)
| 0     := λ t, x₀
| (n+1) := λ t, x₀ + (∫ s in (0 : ℝ)..(t : ℝ), v s (P.recursive n s))

end picard_operator_recursive
