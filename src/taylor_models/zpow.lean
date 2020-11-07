import data.int.basic

def zpow (x : ℤ) (y : ℤ) : ℤ := x ^ int.to_nat y

instance : has_pow ℤ ℤ := ⟨zpow⟩

@[simp] lemma zpow_eq_pow (x y : ℤ) : zpow x y = x ^ y := rfl

lemma zpow_def (x y : ℤ) : x ^ y = x ^ int.to_nat y := rfl

@[simp] lemma zpow_zero (x : ℤ) : x ^ (0 : ℤ) = 1 := 
by simp [zpow_def, int.to_nat_zero]

#check int.to_nat_eq_max

@[simp] lemma zpow_eq_zero_iff (x y : ℤ) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
begin 
    simp only [zpow_def],
    sorry,
end

@[simp] lemma zero_zpow {x : ℤ} (h : x ≠ 0) : (0 : ℤ) ^ x = 0 := sorry

@[simp] lemma zpow_one (x : ℤ) : x ^ (1 : ℤ) = x := sorry

@[simp] lemma one_zpow (x : ℤ) : (1 : ℤ) ^ x = 1 := sorry

lemma zpow_add {x : ℤ} (y z : ℤ) (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := sorry

lemma zpow_mul {x y : ℤ} (z : ℤ) : x ^ (y * z) = (x ^ y) ^ z := sorry

@[simp] lemma zpow_nat_cast (x : ℤ) : ∀ (n : ℕ), x ^ (n : ℤ) = x ^ n := sorry
