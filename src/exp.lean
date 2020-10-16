-- Some results about exp that should probably go to mathlib:
-- analysis/special_functions/exp_log.lean

import data.real.basic
import data.complex.exponential
import analysis.complex.basic
import analysis.special_functions.exp_log
import analysis.calculus.times_cont_diff

noncomputable theory

open real classical topological_space

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

-- No need!
lemma has_deriv_at_exp_mul (a : ℂ) (x : ℂ) : 
has_deriv_at (λ y, complex.exp (a * y)) (a * (complex.exp (a * x))) x :=
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