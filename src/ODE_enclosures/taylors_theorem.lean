import analysis.calculus.mean_value
import analysis.calculus.times_cont_diff
import analysis.calculus.iterated_deriv
import measure_theory.measurable_space
import measure_theory.borel_space
import topology.basic

open nat finset topological_space

open_locale big_operators

variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                      [normed_space ℝ E] [complete_space E] [second_countable_topology E]

@[reducible] noncomputable def R (n : ℕ) (f : ℝ → ℝ) (a : ℝ) : ℝ → ℝ := 
λ x, (iterated_deriv (n + 1) f a) * (x - a)^(n + 1) / factorial (n + 1)

@[reducible] noncomputable def taylor (n : ℕ) (f : ℝ → ℝ) (a : ℝ) : ℝ → ℝ := 
λ x, ∑ i in range (n + 1), (iterated_deriv i f a) * (x - a)^i / factorial i

lemma taylor_zero (f : ℝ → ℝ) (a : ℝ) : taylor 0 f a = λ _, f a := 
by simp [taylor]

lemma taylor_succ (f : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ)
: taylor (n + 1) f a x = 
taylor n f a x + iterated_deriv (n + 1) f a * (x - a) ^ (n + 1) / factorial (n + 1) := 
sorry

lemma deriv_taylor_eq
  (f : ℝ → ℝ) (n : ℕ) (a : ℝ) (x : ℝ) :
  deriv (taylor (n + 1) f a) x = taylor n (deriv f) a x :=
begin 
  induction n with n hn generalizing a x,
  { simp [taylor_zero, finset.sum_range_succ], },
  { simp [taylor_succ], 
    rw [←hn a x, finset.sum_range_succ', ←iterated_deriv_succ'],
    simp only [factorial_succ], simp, 
    sorry, },
end 

theorem taylor_left 
  (f : ℝ → ℝ) (a : ℝ) (n : ℕ)
  (hdiff : times_cont_diff_at ℝ (n + 1) f a) :
  ∀ x, a < x → 
  ∃ c, a ≤ c ∧ c ≤ x ∧
       f x = taylor n f a x + R n f c x :=
begin 
  intros x hx,
  sorry,
end
