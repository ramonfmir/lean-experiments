import measure_theory.interval_integral

import picard_lindelof.other.interval_integral

-- Following Imperial's MA2AA1 notes and Ch 2 of 'Spectral Theory and Quantum Mechanics'.

noncomputable theory
open metric real set measure_theory interval_integral topological_space
open_locale topological_space  

-- NOTE: A is meant to be ℝ^n. Think of these as functions [t₀, t₁] → ℝ^n.
structure locally_bounded_real_continuous_function (A : Type*) 
[measurable_space A] [normed_group A] [borel_space A] [linear_order A]
[normed_space ℝ A] [complete_space A] [second_countable_topology A] :=
(to_fun : ℝ → A)
(t₀ t₁ : ℝ) (ht : t₀ ≤ t₁)
--(hdom : function.support to_fun ⊆ Icc t₀ t₁)
(hcts : continuous_on to_fun (Icc t₀ t₁))
-- Should it be bounded?

namespace picard_operator

notation `C(` A `)` := locally_bounded_real_continuous_function A

variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                      [normed_space ℝ E] [complete_space E] [second_countable_topology E]

instance : has_coe_to_fun C(E) := ⟨_, locally_bounded_real_continuous_function.to_fun⟩

structure initial_value_problem (x : C(E)) :=
(x₀ : E) (v : ℝ → E → E)
(K : nnreal) (hK : K < 1)
(hlipschitz : ∀ s, lipschitz_with K (v s))
(hbdd : ∃ C, 0 < C ∧ ∀ t ∈ Ioc x.t₀ x.t₁, ∥v t (x t)∥ ≤ C)
(hintegrable : interval_integrable (λ s, v s (x s)) volume x.t₀ x.t₁)

notation `IVP(` x `)` := initial_value_problem x

open bounded_continuous_function

-- The Picard operator as a function.
def P.to_fun (x : C(E)) (I : IVP(x)) : ℝ → E := λ t, I.x₀ + ∫ s in x.t₀..t, I.v s (x s)

def P.to_fun.dist_eq (x : C(E)) (I : IVP(x)) (a b : ℝ)
: dist (P.to_fun x I a) (P.to_fun x I b) = ∥∫ s in a..b, I.v s (x s)∥ :=
begin 
    rw dist_eq_norm, simp only [P.to_fun],
    have hrw1 : 
        I.x₀ + (∫ s in x.t₀..a, I.v s (x s)) - (I.x₀ + ∫ s in x.t₀..b, I.v s (x s)) =
        (∫ s in x.t₀..a, I.v s (x s)) - (∫ s in x.t₀..b, I.v s (x s)) := by abel,
    rw hrw1, clear hrw1,
    rw [interval_integral.integral_symm a x.t₀],
    have hrw2 :
        -(∫ s in a..x.t₀, I.v s (x s)) - (∫ s in x.t₀..b, I.v s (x s)) =
        -((∫ s in a..x.t₀, I.v s (x s)) + (∫ s in x.t₀..b, I.v s (x s))) := by abel,
    rw hrw2, clear hrw2,
    have hadd :
        (∫ s in a..x.t₀, I.v s (x s)) + (∫ s in x.t₀..b, I.v s (x s)) =
        ∫ s in a..b, I.v s (x s), 
    { -- These can be proved from hintegrable and integrable_on.mono.
      have hleft : interval_integrable (λ s, I.v s (x s)) volume a x.t₀ := sorry,
      have hright : interval_integrable (λ s, I.v s (x s)) volume x.t₀ b := sorry,
      exact (integral_add_adjacent_intervals hleft hright), },
    rw [hadd, norm_neg],
end

-- The Picard operator is continuous.
lemma P.to_fun.continuous_on (x : C(E)) (I : IVP(x))
: continuous_on (P.to_fun x I) (Icc x.t₀ x.t₁) :=
begin
    rcases I.hbdd with ⟨C, ⟨hCpos, hC⟩⟩,
    rw metric.continuous_on_iff,
    intros a ha ε hε, use [ε/C, div_pos hε hCpos],
    intros b hb hab, rw [P.to_fun.dist_eq x I],
    have hboundab : ∀ s, s ∈ Ioc (min b a) (max b a) → ∥I.v s (x s)∥ ≤ C,
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

-- The Picard operator is bounded.
lemma P.to_fun.bounded (x : C(E)) (I : IVP(x))
: ∃ C, ∀ (a b : ℝ), dist (P.to_fun x I a) (P.to_fun x I b) ≤ C := 
begin
    sorry,
end

-- Picard operator.
def P (x : C(E)) (I : IVP(x)) : C(E) := {
    to_fun := P.to_fun x I,
    t₀ := x.t₀,
    t₁ := x.t₁,
    ht := x.ht,
    hcts := P.to_fun.continuous_on x I,
}

@[simp] lemma P.def (x : C(E)) (I : IVP(x)) (t : ℝ)
: P x I t = I.x₀ + ∫ s in x.t₀..t, I.v s (x s) := rfl

-- Initial value problem.
parameters (x : locally_bounded_continuous_function)
           (hx₀ : x t₀ = x₀) 
           (hx_deriv : ∀ t ∈ Ioc t₀ t₁, has_deriv_within_at x (v t (x t)) (Ioi t) t)
           (hv_integrable : interval_integrable (λ t, v t (x t)) volume t₀ t₁)
           (hv_bdd : ∃ C, 0 < C ∧ ∀ t ∈ Ioc t₀ t₁, ∥v t (x t)∥ ≤ C)

end picard_operator
