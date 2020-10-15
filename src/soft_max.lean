-- Diversion from LTL_Diff. What if we prove that the standard smooth maximum
-- actually approximates the maximum.

-- Second attempt using fin n → ℝ.

import data.real.basic
import data.list.min_max
import data.complex.exponential
import analysis.complex.basic
import analysis.special_functions.exp_log
import analysis.calculus.times_cont_diff
import algebra.big_operators

noncomputable theory

open real classical topological_space
open_locale big_operators

-- Definition of soft_max.
section soft_max 

variables (n : ℕ)

def soft_max.num (α : ℝ) : (fin (n + 1) → ℝ) → ℝ := 
λ v, ∑ i, (v i) * exp (α * (v i))

@[simp] lemma soft_max.num_zero (α : ℝ) : soft_max.num 0 α = λ v, (v 0) * exp (α * (v 0)) := 
begin
    ext v, 
    unfold soft_max.num, -- How do I get rid of this ?
    rw [fin.sum_univ_succ, fin.sum_univ_zero, add_zero],
end

--@[simp] lemma soft_max.num_succ (α : ℝ) (v : fin n.succ → ℝ) : 
--soft_max.num n.succ α v = (soft_max.num n α (λ i, v i)) + (v n) * exp (α * (v n)) :=

def soft_max.den (α : ℝ) : (fin (n + 1) → ℝ) → ℝ := 
λ v, ∑ i, exp (α * (v i))

@[simp] lemma soft_max.den_zero (α : ℝ) : soft_max.den 0 α = λ v, exp (α * (v 0)) := 
begin
    ext v, 
    unfold soft_max.den, -- How do I get rid of this ?
    rw [fin.sum_univ_succ, fin.sum_univ_zero, add_zero],
end

def soft_max (α : ℝ) : (fin (n + 1) → ℝ) → ℝ := 
λ v, (soft_max.num n α v) / (soft_max.den n α v)

namespace soft_max

-- #check continuous_at.add
-- #print filter.tendsto
-- #print nhds
-- #print filter.principal
-- #check fin.sum_univ_zero
-- #check continuous_equiv_fun_basis
-- #check continuous.lim_eq
-- #print continuous_iff_is_closed
-- #print continuous_pi
-- #print Pi.uniform_continuous_proj
-- #check continuous_apply
-- #check exp_sum
-- #check exp_list_sum
-- #check continuous_exp
-- #check exp_nat_mul
-- #eval (2 : ℝ) ^ (3 : ℝ) -- fails, no has_pow ℝ ℝ ...
#check filter.mem_sets_of_superset
#print complex.abs_exp_sub_one_sub_id_le

lemma has_deriv_at_exp_mul (α : ℝ) (x : ℝ) : has_deriv_at (λ y, exp (α * y)) (α * (exp (α * x))) x :=
begin
  rw has_deriv_at_iff_is_o_nhds_zero,
  have : (1 : ℕ) < 2 := by norm_num,
  refine (asymptotics.is_O.of_bound (∥α * (exp (α * x))∥) _).trans_is_o (asymptotics.is_o_pow_id this),
  -- This should be 1/α and we should assume α > 0.
  have : metric.ball (0 : ℝ) 1 ∈ nhds (0 : ℝ) := metric.ball_mem_nhds 0 zero_lt_one,
  apply filter.mem_sets_of_superset this (λz hz, _),
  simp only [metric.mem_ball, dist_zero_right] at hz,
  simp only [exp_zero, mul_one, one_mul, add_comm, normed_field.norm_pow, zero_add, set.mem_set_of_eq],
  calc ∥exp (α * (x + z)) - exp (α * x) - z * (α * exp (α * x))∥
        = ∥exp (α * x + α * z) - exp (α * x) - z * (α * exp (α * x))∥ : by rw [mul_add]
    ... = ∥exp (α * x) * exp (α * z) - exp (α * x) - z * (α * exp (α * x))∥ : by rw [exp_add]
    ... = ∥exp (α * x) * exp (α * z) - exp (α * x) - α * (exp (α * x) * z)∥ : by rw [mul_comm z, mul_assoc α]
    ... = ∥exp (α * x) * exp (α * z) - exp (α * x) - exp (α * x) * (z * α)∥ : by rw [mul_comm α (_ * _), mul_assoc _ z α]
    ... = ∥exp (α * x) * (exp (α * z) - 1 - (z * α))∥ : by ring
    ... ≤ ∥α * exp (α * x)∥ * ∥z∥ ^ 2 : by sorry,
  --calc ∥exp (x + z) - exp x - z * exp x∥
  --  = ∥exp x * (exp z - 1 - z)∥ : by { congr, rw [exp_add], ring }
  --  ... = ∥exp x∥ * ∥exp z - 1 - z∥ : normed_field.norm_mul _ _
  --  ... ≤ ∥exp x∥ * ∥z∥^2 :
  --    mul_le_mul_of_nonneg_left (abs_exp_sub_one_sub_id_le (le_of_lt hz)) (norm_nonneg _)
end

-- Lemma 1.a: soft_max.num is continuous everywhere.
lemma num.continuity_at : ∀ α v, continuous_at (soft_max.num n α) v := 
begin
    intros α v,
    induction n with m hm,
    { rw soft_max.num_zero,
      apply continuous_at.mul,
      { apply continuous_iff_continuous_at.1,
        apply continuous_apply, },
      { sorry, }, },
    { sorry, },
end

-- Lemma 1.b: soft_max.den is continuous everywhere.
lemma den.continuity_at : ∀ α v, continuous_at (soft_max.den n α) v := sorry

-- Lemma 1.b: soft_max.den is non-zero.
lemma den.nonzero : ∀ α v, soft_max.den n α v ≠ 0 := sorry

-- Lemma 1: soft_max is continuous.
lemma continuity : ∀ α, continuous (soft_max n α) :=
begin
    intro α,
    rw continuous_iff_continuous_at,
    intro v,
    apply continuous_at.div,
    { exact num.continuity_at n α v, },
    { exact den.continuity_at n α v, },
    { exact den.nonzero n α v, },
end

-- Lemma 2: soft_max is smooth.
lemma smoothness : ∀ α, times_cont_diff ℝ ⊤ (soft_max n α) :=
begin
    intro α,
    rw times_cont_diff_top,
    intro m,
    induction m,
    { erw times_cont_diff_zero,
      exact continuity n α, },
    { sorry }
end

end soft_max

end soft_max