import data.real.basic
import data.real.nnreal
import tactic.ring

open real

-- https://sms.math.nus.edu.sg/Simo/IMO_Problems/00.pdf

lemma AM_GM_inequality (x y : ℝ) (hnnx : 0 ≤ x) (hnny : 0 ≤ y) 
: sqrt (x * y) ≤ (x + y) / 2 :=
begin
    have h : 0 ≤ (sqrt x - sqrt y) * (sqrt x - sqrt y) := mul_self_nonneg _,
    rw [mul_sub] at h, 
    iterate 2 { rw [sub_mul, ←sqrt_mul hnnx, ←sqrt_mul hnny] at h, },
    rw [sqrt_mul_self hnnx, sqrt_mul_self hnny, mul_comm] at h,
    linarith,
end

#check lt_irrefl

-- Note this didnt work with nnreals..
lemma IMO2000Q2_aux (x y z : ℝ) (hposx : 0 < x) (hposy : 0 < y) (hposz : 0 < z) 
: (x - y + z) * (y - z + x) * (z - x + y) ≤ x * y * z :=
begin
    set u := x - y + z with hu,
    set v := y - z + x with hv,
    set w := z - x + y with hw,
    have hx : x = (u + v) / 2 := by rw [hu, hv]; ring, 
    have hy : y = (v + w) / 2 := by rw [hv, hw]; ring, 
    have hz : z = (w + u) / 2 := by rw [hw, hu]; ring, 
    have hnnx := le_of_lt hposx,
    have hnny := le_of_lt hposy,
    have hnnz := le_of_lt hposz,
    have hnnxyz : 0 ≤ x * y * z := mul_nonneg (mul_nonneg hnnx hnny) hnnz,
    by_cases hnnu : 0 ≤ u; by_cases hnnv : 0 ≤ v; by_cases hnnw : 0 ≤ w,
    { -- u, v, w ≥ 0
      rw [hx, hy, hz],
      have huv := AM_GM_inequality u v hnnu hnnv,
      have hvw := AM_GM_inequality v w hnnv hnnw,
      have hwu := AM_GM_inequality w u hnnw hnnu,
      have hnnamuv : 0 ≤ (u + v) / 2 := div_nonneg (add_nonneg hnnu hnnv) (by linarith),
      have hnnamvw : 0 ≤ (v + w) / 2 := div_nonneg (add_nonneg hnnv hnnw) (by linarith),
      have hnnamwu : 0 ≤ (w + u) / 2 := div_nonneg (add_nonneg hnnw hnnu) (by linarith),
      have hnnuu := mul_nonneg hnnu hnnu,
      have hnnvv := mul_nonneg hnnv hnnv,
      have hnnww := mul_nonneg hnnw hnnw,
      have hnnsquv : 0 ≤ sqrt (u * v) := sqrt_nonneg _,
      have hnnsqvw : 0 ≤ sqrt (v * w) := sqrt_nonneg _,
      have hnnsqwu : 0 ≤ sqrt (w * u) := sqrt_nonneg _,
      have hnnuv := mul_nonneg hnnu hnnv,
      have hnnvw := mul_nonneg hnnv hnnw,
      have hnnwu := mul_nonneg hnnw hnnu,
      have h := mul_le_mul (mul_le_mul huv hvw hnnsqvw hnnamuv) hwu hnnsqwu (mul_nonneg hnnamuv hnnamvw),
      calc u * v * w = sqrt (u ^ 2) * sqrt (v ^ 2) * sqrt (w ^ 2)    : by rw [sqrt_sqr hnnu, sqrt_sqr hnnv, sqrt_sqr hnnw]
                 ... = sqrt (u * u) * (sqrt (v * v) * sqrt (w * w))  : by rw [pow_two u, pow_two v, pow_two w, mul_assoc]
                 ... = sqrt (u * u * (v * v * (w * w)))              : by rw [←sqrt_mul hnnvv, ←sqrt_mul hnnuu]
                 ... = sqrt ((u * v) * ((v * w) * (w * u)))          : by ring
                 ... = sqrt (u * v) * sqrt (v * w) * sqrt (w * u)    : by rw [sqrt_mul hnnuv, sqrt_mul hnnvw, mul_assoc]
                 ... ≤ ((u + v) / 2) * ((v + w) / 2) * ((w + u) / 2) : by exact h, },
    { -- v < 0.
      have h := mul_nonpos_iff.mpr (or.inl ⟨hnnv, le_of_not_le hnnw⟩),
      replace h := mul_nonpos_iff.mpr (or.inl ⟨hnnu, h⟩),
      rw [←mul_assoc] at h,
      exact le_trans h hnnxyz, },
    { -- w < 0.
      have h := mul_nonpos_iff.mpr (or.inl ⟨hnnu, le_of_not_le hnnv⟩),
      replace h := mul_nonpos_iff.mpr (or.inl ⟨hnnw, h⟩),
      rw [mul_comm w _] at h,
      exact le_trans h hnnxyz, },
    { -- v, w < 0, contradiction.
      exfalso,
      suffices hsuff : x < 0,
      { exact lt_irrefl x (lt_trans hsuff hposx), },
      replace hnnv := lt_of_not_ge hnnv,
      replace hnnw := lt_of_not_ge hnnw,
      have h := add_lt_add hnnv hnnw,
      rw [hv, hw] at h,
      linarith [h], },
    { -- u < 0.
      have h := mul_nonpos_iff.mpr (or.inl ⟨hnnv, le_of_not_le hnnu⟩),
      replace h := mul_nonpos_iff.mpr (or.inl ⟨hnnw, h⟩),
      rw [mul_comm w _, mul_comm v u] at h,
      exact le_trans h hnnxyz, },
    { -- u, w < 0, contradiction.
      exfalso,
      suffices hsuff : z < 0,
      { exact lt_irrefl z (lt_trans hsuff hposz), },
      replace hnnu := lt_of_not_ge hnnu,
      replace hnnw := lt_of_not_ge hnnw,
      have h := add_lt_add hnnu hnnw,
      rw [hu, hw] at h,
      linarith [h], },
    { -- u, v < 0, contradiction.
      exfalso,
      suffices hsuff : y < 0,
      { exact lt_irrefl y (lt_trans hsuff hposy), },
      replace hnnu := lt_of_not_ge hnnu,
      replace hnnv := lt_of_not_ge hnnv,
      have h := add_lt_add hnnu hnnv,
      rw [hu, hv] at h,
      linarith [h], },
    { -- u, v, w < 0, contradiction.
      exfalso,
      suffices hsuff : y < 0,
      { exact lt_irrefl y (lt_trans hsuff hposy), },
      replace hnnu := lt_of_not_ge hnnu,
      replace hnnv := lt_of_not_ge hnnv,
      have h := add_lt_add hnnu hnnv,
      rw [hu, hv] at h,
      linarith [h], },
end

lemma IMO2000Q2 (a b c : nnreal) (h : a * b * c = 1) :
(a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 :=
begin
    have han0 : a ≠ 0 := sorry, -- Easy.
    have hbn0 : b ≠ 0 := sorry, -- Easy.
    set! x := a * b with hx,
    set! y := b with hy,
    set! z := a * b * c with hz,
    have hxn0 : x ≠ 0 := sorry, -- Easy.
    have hyn0 : y ≠ 0 := sorry, -- Easy.
    have hzn0 : z ≠ 0 := sorry, -- Easy.
    have hxyzgt0 : x * y * z > 0 := sorry, -- Easy.
    have ha : a = x / y,
    { rw [hx, hy, mul_comm, mul_div_cancel_left _ hbn0], },
    have hb : b = y / z, 
    { rw [hy, hz, h, div_one], },
    have hc : c = z / x,
    { rw [hz, hx, mul_div_cancel_left _ (mul_ne_zero han0 hbn0)], },
    rw [ha, hb, hc],
    iterate 3 { rw one_div_div, },
    apply (le_of_mul_le_mul_left _ hxyzgt0),
    rw mul_one,
    calc  x * y * z * ((x / y - 1 + z / y) * (y / z - 1 + x / z) * (z / x - 1 + y / x))
        = (y * (x / y - 1 + z / y)) * (z * (y / z - 1 + x / z)) * (x * (z / x - 1 + y / x)) : by ring
    ... = (y * x / y - y + y * z / y) * (z * y / z - z + z * x / z) * (x * z / x - x + x * y / x) : sorry -- by ring doesn't work
    ... = (x - y + z) * (y - z + x) * (z - x + y) : sorry -- repeated rewriting mul_div_cancel_left
    ... ≤ x * y * z : sorry,
end
