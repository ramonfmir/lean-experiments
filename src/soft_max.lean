-- Diversion from LTL_Diff. What if we prove that the standard smooth maximum
-- actually approximates the maximum.

import data.real.basic
import data.list.min_max
import data.complex.exponential
import analysis.complex.basic
import analysis.special_functions.exp_log
import analysis.calculus.times_cont_diff

noncomputable theory

open real classical

section soft_max 

variable (n : ℕ)

def soft_max (α : ℝ) : vector ℝ n → ℝ :=
λ v,
let num := (list.map (λ x, x * exp (α * x)) v.val).sum in
let den := (list.map (λ x, exp (α * x)) v.val).sum in
num / den

def Rn_norm : vector ℝ n → ℝ :=
λ v, sqrt (list.map (λ x, x ^ 2) v.val).sum 

instance : has_norm (vector ℝ n) := ⟨Rn_norm n⟩

instance : add_comm_group (vector ℝ n) := {
    zero := ⟨list.repeat 0 n, by simp⟩,
    add := λ v₁ v₂, ⟨(list.map (λ i, vector.nth v₁ i + vector.nth v₂ i) (list.fin_range n)), by simp⟩,
    -- The proof of property should probably be by simp.
    neg := λ v, ⟨list.map (λ x, -x) v.val, by rw list.length_map _ _; exact v.property⟩, 
    add_zero := λ v, sorry,
    zero_add := λ v, sorry,
    add_left_neg := sorry,
    add_comm := sorry,
    add_assoc := sorry,
}

instance : metric_space (vector ℝ n) := {
    dist_self := sorry,
    eq_of_dist_eq_zero := sorry,
    dist_comm := sorry,
    dist_triangle := sorry,
}

instance : normed_group (vector ℝ n) := {
    dist_eq := sorry,
}

instance : normed_space ℝ (vector ℝ n) := sorry

-- Lemma 1: soft_max is smooth.
lemma smoothness : ∀ α, times_cont_diff ℝ ⊤ (soft_max n α) :=
sorry

end soft_max 
