import data.real.basic
import data.fp.basic
import tactic.omega.main

-- Idea: prove that float is a metric space. Not very promising.

section fp_topology

open real fp

variable [C : float_cfg]
include C

def dist : float → float → with_top ℝ
| (float.inf b₁)                (float.inf b₂)                := if b₁ = b₂ then 0 else ⊤
| (float.inf _)                 _                             := ⊤
| _                             (float.inf _)                 := ⊤
| float.nan                     _                             := ⊤
| _                             float.nan                     := ⊤
| x₁@(float.finite s₁ e₁ m₁ f₁) x₂@(float.finite s₂ e₂ m₂ f₂) := 
    real.of_rat (@abs ℚ _ ((to_rat x₁ rfl) - (to_rat x₂ rfl)))

lemma int.shift2_eq_mk_nat_eq (a₁ a₂ : ℕ) (x₁ x₂ : ℤ) 
: int.shift2 a₁ 1 x₁ = int.shift2 a₂ 1 x₂ → 
    rat.mk_nat (int.shift2 a₁ 1 x₁).1 (int.shift2 a₁ 1 x₁).2 
  = rat.mk_nat (int.shift2 a₂ 1 x₂).1 (int.shift2 a₂ 1 x₂).2 :=
begin
    intros h,
    cases x₁; cases x₂; unfold int.shift2 at *; dsimp; injection h with hfst hsnd,
    { rw [hfst, hsnd], },
    { -- No tactic works for this case...
      rw [nat.shiftl_eq_mul_pow, one_mul] at hsnd, exfalso,
      have h := @nat.pow_lt_pow_succ 2 (by norm_num) x₂,
      rw [←hsnd] at h,
      cases x₂,
      { rw [pow_zero] at h, 
        exact (lt_irrefl _ h), },
      { have h' := @nat.pow_lt_pow_of_lt_left 1 2 (by norm_num) x₂.succ (by norm_num),
        rw [one_pow] at h',
        exact (lt_irrefl _ (lt_trans h h')), }, },
    { -- Same as above.
      rw [nat.shiftl_eq_mul_pow, one_mul] at hsnd, exfalso,
      sorry, },
    { iterate 2 { rw [nat.shiftl_eq_mul_pow, one_mul] at hsnd, },
      rw [hfst, nat.succ_injective (@nat.pow_right_injective 2 (by norm_num) _ _ hsnd)], },
end 

lemma to_rat_inj (x y : float) (hx : x.is_finite) (hy : y.is_finite) 
: to_rat x hx = to_rat y hy → x = y :=
begin
    intros h,
    cases x; cases y; try { cases hx, }; try { cases hy, },
    unfold to_rat at h, 
    --split_ifs at h,
    --cases x_a; cases y_a; unfold to_rat at h,
    sorry,
end

lemma dist_eq_zero_iff (x y : float) : dist x y = 0 ↔ x = y :=
begin
    split,
    { intros h,
      cases x; cases y; unfold dist at h; try { cases h, },
      { split_ifs at h,
        { congr', },
        { cases h, }, },
      { replace h := with_top.coe_eq_zero.mp h,
        rw of_rat_eq_cast at h,
        replace h := rat.cast_eq_zero.mp h,
        rw [abs_eq_zero, sub_eq_zero] at h,
        sorry, }, },
    { sorry, }
end

lemma dist_triangle_inequlity (x y z : float) : dist x y ≤ dist x z + dist z y :=
begin
    sorry,
end

end fp_topology
