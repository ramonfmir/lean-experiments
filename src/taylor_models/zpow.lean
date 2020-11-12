import data.int.basic

def zpow (x : ℤ) (y : ℤ) : ℤ := x ^ int.to_nat y

instance : has_pow ℤ ℤ := ⟨zpow⟩

@[simp] lemma zpow_eq_pow (x y : ℤ) : zpow x y = x ^ y := rfl

lemma zpow_def (x y : ℤ) : x ^ y = x ^ int.to_nat y := rfl

@[simp] lemma zpow_zero (x : ℤ) : x ^ (0 : ℤ) = 1 := 
by simp [zpow_def, int.to_nat_zero]

-- TODO: Move.
lemma int.to_nat_nonneg (x : ℤ) : 0 ≤ int.to_nat x := by simp

@[simp] lemma zpow_eq_zero_iff (x y : ℤ) : x ^ y = 0 ↔ x = 0 ∧ 0 < y :=
begin 
    simp only [zpow_def],
    split,
    { intros h, refine ⟨_, _⟩,
      exact (pow_eq_zero h),
      cases y,
      { erw int.to_nat_coe_nat at h,
        cases y,
        { rw pow_zero at h, cases h, },
        { have hy := int.lt_add_succ 0 y,
          rw zero_add at hy,
          exact hy, } },
      { rw [int.to_nat_zero_of_neg (int.neg_succ_lt_zero y)] at h,
        rw pow_zero at h, cases h, }, },
    { rintros ⟨hx, hy⟩,
      have hy' : 0 < int.to_nat y := int.to_nat_zero ▸ (int.to_nat_lt_to_nat hy).2 hy,
      rw [hx, zero_pow hy'], },
end

@[simp] lemma zero_zpow {x : ℤ} (h : x > 0) : (0 : ℤ) ^ x = 0 := 
(zpow_eq_zero_iff 0 x).mpr ⟨rfl, h⟩

@[simp] lemma zpow_one (x : ℤ) : x ^ (1 : ℤ) = x := 
by simp only [zpow_def, int.to_nat_one]; exact pow_one x

@[simp] lemma one_zpow (x : ℤ) : (1 : ℤ) ^ x = 1 := 
by simp only [zpow_def]; exact one_pow (int.to_nat x)

lemma zpow_add {x : ℤ} (y z : ℤ) (hy : 0 ≤ y) (hz : 0 ≤ z) 
: x ^ (y + z) = x ^ y * x ^ z := 
by simp only [zpow_def, int.to_nat_add hy hz]; exact (pow_add _ _ _)

-- TODO: Move.
lemma int.to_nat_mul {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
  (a * b).to_nat = a.to_nat * b.to_nat :=
begin
  lift a to ℕ using ha,
  lift b to ℕ using hb,
  norm_cast,
end

lemma zpow_mul {x y : ℤ} (z : ℤ) (hy : 0 ≤ y) (hz : 0 ≤ z) 
: x ^ (y * z) = (x ^ y) ^ z := 
by simp only [zpow_def, int.to_nat_mul hy hz]; exact (pow_mul x _ _)

@[simp] lemma zpow_nat_cast (x : ℤ) : ∀ (n : ℕ), x ^ (n : ℤ) = x ^ n := 
λ n, by simp only [zpow_def]; rw int.to_nat_coe_nat
