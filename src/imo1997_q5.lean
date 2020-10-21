import data.nat.basic
import data.rat.basic
import data.real.basic
import analysis.special_functions.exp_log 
import analysis.special_functions.pow

set_option eqn_compiler.zeta true

#check ge_iff_le.1

--http://sms.math.nus.edu.sg/Simo/IMO_Problems/97.pdf
lemma IMO1997Q5_aux :
∀ (a t : ℕ), a > 1 ∧ t ≥ 1 → ¬ (a ^ (2 * t) = a * t) :=
sorry

--lemma IMO1997Q5_aux2 :
--∀ (a p q : ℕ), nat.coprime p q → 
--(((a : ℝ) ^ ((rat.mk p q) : ℝ)) : ℚ).denom = 1 →
--(((a : ℝ) ^ ((rat.mk 1 q) : ℝ)) : ℚ).denom = 1

lemma IMO1997Q5 : 
∀ (a b : ℕ), 
a ≥ 1 ∧ b ≥ 1 ∧ a ^ (b ^ 2) = b ^ a → 
(a = 1 ∧ b = 1) ∨ (a = 27 ∧ b = 3) ∨ (a = 16 ∧ b = 2) :=
begin
    rintros a b ⟨ha, hb, h⟩,
    replace ha := eq_or_lt_of_le ha,
    replace hb := eq_or_lt_of_le hb,
    cases ha with h1eqa h1lta; 
    cases hb with h1eqb h1ltb,
    -- Easy cases if a = 1 or b = 1.
    { left,
      exact ⟨h1eqa.symm, h1eqb.symm⟩, },
    { left,
      rw [←h1eqa, one_pow, pow_one] at h,
      exact ⟨h1eqa.symm, h.symm⟩, },
    { left,
      rw [←h1eqb, one_pow, pow_one, one_pow] at h,
      exact ⟨h, h1eqb.symm⟩, },
    -- Otherwise, a, b > 1.
    { right,
      have haneq0 : (a : ℝ) ≠ 0,
      { intros hc, 
        replace hc := nat.cast_eq_zero.1 hc,
        rw [hc] at h1lta,
        cases h1lta, }, 
      have h0lea : 0 < (a : ℝ) := nat.cast_lt.2 (nat.lt_trans nat.zero_lt_one h1lta),
      have h0leb : 0 < (b : ℝ) := nat.cast_lt.2 (nat.lt_trans nat.zero_lt_one h1ltb),
      let t := ((b : ℝ) ^ 2) / (a : ℝ),
      have hb2 : (b : ℝ) ^ 2 = (a : ℝ) * t,
      { rw [←mul_div_assoc, div_eq_mul_inv, mul_comm _ ((↑a)⁻¹), ←mul_assoc],
        rw [inv_mul_cancel haneq0, one_mul], },
      have hb : (b : ℝ) = (a : ℝ) ^ (t : ℝ),
      { have hlog := congr_arg real.log (congr_arg coe h),
        iterate 2 { rw [nat.cast_pow] at hlog, },
        rw [←real.rpow_nat_cast a, ←real.rpow_nat_cast b a] at hlog,
        rw [real.rpow_def_of_pos h0lea, real.rpow_def_of_pos h0leb] at hlog,
        iterate 2 { rw [real.log_exp] at hlog, },
        replace hlog := congr_arg (λ x, x / ↑a) hlog; simp at hlog,
        rw [mul_comm _ ↑a, mul_div_cancel_left _ haneq0, mul_div_assoc] at hlog,
        replace hlog := congr_arg real.exp hlog,
        rw [real.exp_log h0leb, ←real.rpow_def_of_pos h0lea] at hlog,
        rw ←hlog, },
      have hat : (a : ℝ) ^ (2 * t) = (a : ℝ) * t,
      { rw [mul_comm _ t, real.rpow_mul (le_of_lt h0lea)],
        rw [←hb, ←hb2, ←real.rpow_nat_cast],
        norm_num, },
      let tpq : ℚ := rat.mk (b ^ 2) a,
      have ht : (tpq : ℝ) = t,
      { rw rat.cast_mk,
        norm_num, },
      have hq : 1 < tpq.denom,
      { have hqle1 := nat.add_one_le_iff.2 tpq.pos,
        rw zero_add at hqle1, 
        suffices hsuff : tpq.denom ≠ 1,
        { rw ←not_le,
          intros hc,
          apply hsuff,
          exact (le_antisymm hc hqle1), }, 
        intros hq1,
        rw [←ht] at hat,
        rw [←(rat.denom_eq_one_iff tpq).1 hq1] at hat,
        have hpgt1 : tpq.num.to_nat ≥ 1,
        { sorry, },
        apply (IMO1997Q5_aux a (int.to_nat tpq.num) ⟨h1lta, hpgt1⟩),
        rw [←(@nat.cast_inj ℝ _ _ _), nat.cast_pow, nat.cast_mul],
        simp at hat,
        --rw [←nat.cast_mul] at hat,
        --rw real.rpow_nat_cast at hat,
        --have H := int.to_nat_of_nonneg (le_trans (le_of_lt int.zero_lt_one) (ge_iff_le.1 hpgt1)),
        sorry,
        },
      },
end
