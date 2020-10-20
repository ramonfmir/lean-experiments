import data.nat.basic
import data.rat.basic
import data.real.basic
import analysis.special_functions.exp_log 
import analysis.special_functions.pow

set_option eqn_compiler.zeta true

#check real.log

--http://sms.math.nus.edu.sg/Simo/IMO_Problems/97.pdf
lemma IMO1997Q5 : 
∀ (a b : ℕ), a ≥ 1 ∧ b ≥ 1 ∧ a ^ (b ^ 2) = b ^ a → 
(a = 1 ∧ b = 1) ∨ (a = 27 ∧ b = 3) ∨ (a = 16 ∧ b = 2) :=
begin
    rintros a b ⟨ha, hb, h⟩,
    have haneq0 : (a : ℚ) ≠ 0,
    { intros hc, 
      sorry, }, 
    let t := ((b : ℚ) ^ 2) / (a : ℚ),
    have hb2 : (b : ℚ) ^ 2 = (a : ℚ) * t,
    { rw [←mul_div_assoc, div_eq_mul_inv, mul_comm _ ((↑a)⁻¹), ←mul_assoc],
      rw [inv_mul_cancel haneq0, one_mul], },
    have hb : (b : ℝ) = (a : ℝ) ^ (t : ℝ),
    { --have hlog := congr_arg real.log h,
      sorry, }

    -- OLD:
    -- split,
    -- { -- Show that a = 1.
    --   apply le_antisymm _ ha,
    --   apply le_of_not_lt, 
    --   -- Assume a > 1.
    --   intros h1a,
    --   cases (lt_or_eq_of_le (ge_iff_le.1 hb)) with h1gtb h1eqb,
    --   { -- Assume b > 1.
    --     sorry, },
    --   { -- Assume b = 1.
    --     rw ←h1eqb at h,
    --     iterate 2 { rw one_pow at h, },
    --     rw pow_one at h,
    --     rw h at h1a,
    --     exact (lt_irrefl _ h1a), } },
    -- { sorry, },
end