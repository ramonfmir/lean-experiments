import data.real.basic
import data.real.nnreal
import tactic.ring

open real

lemma AG_GM_inequality (x y : nnreal) : sqrt (x * y) ≤ (x + y) / 2 :=
begin
    have h : 0 ≤ (sqrt x - sqrt y) * (sqrt x - sqrt y) := mul_self_nonneg _,
    rw [mul_sub, sub_mul, sub_mul] at h, 
    iterate 2 { erw [←sqrt_mul (nnreal.coe_nonneg x), ←sqrt_mul (nnreal.coe_nonneg y)] at h, },
    erw [sqrt_mul_self (nnreal.coe_nonneg x), sqrt_mul_self (nnreal.coe_nonneg y), mul_comm] at h,
    linarith,
end

-- Note this didnt work with nnreals..
lemma IMO2000Q2_aux (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) :
(x - y + z) * (y - z + x) * (z - x + y) ≤ x * y * z :=
begin
    set u := x - y + z with hu,
    set v := y - z + x with hv,
    set w := z - x + y with hw,
    have hx : x = (u + v) / 2 := by rw [hu, hv]; ring, 
    have hy : y = (v + w) / 2 := by rw [hv, hw]; ring, 
    have hz : z = (w + u) / 2 := by rw [hw, hu]; ring, 
    rw [hx, hy, hz],
    --apply mul_le_mul,
    sorry,
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
