import analysis.calculus.mean_value
import analysis.calculus.times_cont_diff
import analysis.calculus.iterated_deriv

open nat finset

open_locale big_operators

@[reducible] noncomputable def R (n : ℕ) (f : ℝ → ℝ) (a : ℝ) : ℝ → ℝ := 
λ x, (iterated_deriv (n + 1) f a) * (x - a)^(n + 1) / factorial (n + 1)

@[reducible] noncomputable def taylor (n : ℕ) (f : ℝ → ℝ) (a : ℝ) : ℝ → ℝ := 
λ x, ∑ i in range n, (iterated_deriv i f a) * (x - a)^i / factorial i

lemma taylor_zero (f : ℝ → ℝ) (a : ℝ) : taylor 0 f a = λ _, 0 := 
by simp [taylor]

lemma taylor_one (f : ℝ → ℝ) (a : ℝ) : taylor 1 f a = λ _, f a := 
by simp [taylor]

lemma taylor_succ (f : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ)
: taylor (n + 1) f a x = taylor n f a x + iterated_deriv n f a * (x - a) ^ n / n.factorial := 
by simp [taylor, finset.sum_range_succ, add_comm]

lemma deriv_taylor_eq
  (f : ℝ → ℝ) (n : ℕ) (a : ℝ) (x : ℝ) :
  deriv (taylor n f a) x = taylor n (deriv f) a x :=
begin 
  induction n with n hn generalizing a x,
  { simp [taylor_zero], },
  { simp [taylor_succ], 
    rw [←hn a x, finset.sum_range_succ', ←iterated_deriv_succ'],
    simp only [factorial_succ], simp, 
    have h1 : (x - a) ^ n = (x - a) ^ ((n + 1) - 1) := by congr,
    have h2 : n.factorial = ((n + 1) - 1).factorial := by congr,
    rw [h1, h2, add_comm], sorry, },
end 

theorem taylor_left 
  (f : ℝ → ℝ) (a : ℝ) (n : ℕ)
  (hdiff : times_cont_diff_at ℝ (n + 1) f a) :
  ∀ x, a < x → 
  ∃ c, a ≤ c ∧ c ≤ x ∧
       f x = taylor n f a x + R n f c x :=
begin 
  intros x hx,
end
