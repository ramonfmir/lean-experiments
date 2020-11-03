import data.fp.basic

open fp

variable [C : float_cfg]
include C

theorem float.one.valid : valid_finite emin 1 :=
⟨begin
  -- Can we make linarith work here?
  rw add_sub_assoc,
  apply le_add_of_nonneg_right,
  apply sub_nonneg_of_le,
  apply int.coe_nat_le_coe_nat_of_le,
  exact C.prec_pos,
end,
begin
   suffices hsuff : prec ≤ 2 * emax,
   { rw ←int.coe_nat_le at hsuff,
     rw ←sub_nonneg at *,
     simp only [emin, emax] at *,
     ring,
     assumption, },
    exact (le_trans C.prec_max (nat.le_mul_of_pos_left dec_trivial)),
end,
begin
    rw max_eq_right,
    simp [sub_eq_add_neg, add_comm],
    exact (int.coe_nat_le_coe_nat_of_le C.prec_pos),
end⟩ 

def float.one (s : bool) : float :=
float.finite s emin 1 float.one.valid