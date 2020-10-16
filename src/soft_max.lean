-- Diversion from LTL_Diff. What if we prove that the standard smooth maximum
-- actually approximates the maximum.

-- Second attempt using fin n → ℝ.

import data.real.basic
import data.list.min_max
import data.complex.exponential
import analysis.complex.basic
import analysis.special_functions.pow
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

lemma soft_max.num_succ_aux (α : ℝ) (v : fin (n + 1).succ → ℝ) : 
soft_max.num n.succ α v = (soft_max.num n α (λ i, v i)) + (v (n + 1)) * exp (α * (v (n + 1))) :=
begin
  unfold soft_max.num,
  rw fin.sum_univ_cast_succ,
  congr,
  { simp, },
  { rw ←fin.coe_nat_eq_last; refl, },
  { rw ←fin.coe_nat_eq_last; refl, }
end

@[simp] lemma soft_max.num_succ (α : ℝ) : 
soft_max.num n.succ α = λ (v : fin (n + 1).succ → ℝ), 
  (soft_max.num n α (λ i, v i)) + (v (n + 1)) * exp (α * (v (n + 1))) :=
by ext v; exact soft_max.num_succ_aux n α v

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

-- TEMP
#check continuous.prod_map
#check fin.cast_succ 0

-- Lemma 1.a: soft_max.num is continuous everywhere.
lemma num.continuity_at : ∀ α v, continuous_at (soft_max.num n α) v := 
begin
  intros α v,
  induction n with m hm,
  { rw soft_max.num_zero,
    apply continuous_at.mul,
    { apply continuous_iff_continuous_at.1,
      apply continuous_apply, },
    { have hexp : (λ (x : fin 1 → ℝ), exp (α * x 0)) = (λ (x : fin 1 → ℝ), (exp (x 0)) ^ α),
        ext x,
        rw [mul_comm α (x 0), exp_mul],
      rw hexp,
      apply continuous_iff_continuous_at.1,
      apply continuous_rpow,
      { intros v',
        left,
        exact exp_ne_zero (v' 0), },
      { show continuous (exp ∘ (λ (a : fin 1 → ℝ), a 0)),
        refine continuous.comp continuous_exp _,
        apply continuous_apply, },
      { apply continuous_const, }, }, },
  { rw soft_max.num_succ m,
    apply continuous_at.add,
    { show continuous_at ((num m α) ∘ (λ (x : fin (m.succ + 1) → ℝ), (λ (i : fin (m + 1)), x ↑i))) v,
      apply continuous_at.comp,
      { apply hm, },
      { -- Some rearranging.
        suffices hsuff : continuous_at (λ (x : fin (m.succ + 1) → ℝ) (i : fin m.succ), x (fin.cast_succ i)) v,
        { suffices hsuff2 : 
            (λ (x : fin (m.succ + 1) → ℝ) (i : fin m.succ), x (fin.cast_succ i)) =
            (λ (x : fin (m.succ + 1) → ℝ) (i : fin (m + 1)), x ↑i),
            { rw ←hsuff2,
              exact hsuff, }, 
          ext x i,
          simp, },
        -- Continue.
        sorry,
        } }, 
    { -- This we have already proved, so factor that out and re-use.
      sorry,}, },
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