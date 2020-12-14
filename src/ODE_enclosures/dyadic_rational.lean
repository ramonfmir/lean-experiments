import data.int.basic
import data.rat.basic
import data.real.basic
import data.buffer.parser
import tactic.find
import analysis.special_functions.pow

import ODE_enclosures.zpow

-- https://isabelle.in.tum.de/website-Isabelle2013/dist/library/HOL/HOL-Library/Float.html

open parser zpow function

structure dyadic_rational := (m : ℤ) (e : ℤ)

local notation `𝔽` := dyadic_rational

namespace dyadic_rational

meta instance : has_to_format 𝔽 :=
⟨λ f, (to_fmt f.m) ++ (to_fmt " * 2^") ++ (to_fmt f.e)⟩

@[reducible] def to_rat (x : 𝔽) : ℚ :=
x.m * (2 ^ x.e)

@[reducible] noncomputable def to_real (x : 𝔽) : ℝ :=
x.m * (2 ^ x.e)

@[simp] lemma to_rat_mk {m e : ℤ} : to_rat ⟨m, e⟩ = m * (2 ^ e) := rfl

@[simp] lemma to_real_mk {m e : ℤ} : to_real ⟨m, e⟩ = m * (2 ^ e) := rfl

-- Basic operations.

@[reducible] def zero : 𝔽 := ⟨0, 0⟩

lemma zero_spec : to_rat zero = 0 := by simp

@[reducible] def one : 𝔽 := ⟨1, 0⟩

lemma one_spec : to_rat one = 1 := by simp

@[reducible] def align (x y : 𝔽) : ℤ × ℤ × ℤ :=
if x.e ≤ y.e then ⟨x.m, y.m * 2 ^ (y.e - x.e), x.e⟩ else ⟨x.m * 2 ^ (x.e - y.e), y.m, y.e⟩ 

@[simp] lemma align_le {x y : 𝔽} (h : x.e ≤ y.e) 
: align x y = ⟨x.m, y.m * 2 ^ (y.e - x.e), x.e⟩ := 
by simp only [align]; split_ifs; refl

@[simp] lemma align_le.mx {x y : 𝔽} (h : x.e ≤ y.e) 
: (align x y).1 = x.m := 
by simp [align_le h]

@[simp] lemma align_le.my {x y : 𝔽} (h : x.e ≤ y.e) 
: (align x y).2.1 = y.m * 2 ^ (y.e - x.e) := 
by simp [align_le h]

@[simp] lemma align_le.e {x y : 𝔽} (h : x.e ≤ y.e) 
: (align x y).2.2 = x.e := 
by simp [align_le h]

@[simp] lemma align_not_le {x y : 𝔽} (h : ¬ (x.e ≤ y.e)) 
: align x y = ⟨x.m * 2 ^ (x.e - y.e), y.m, y.e⟩ := 
by simp only [align]; split_ifs; refl

@[simp] lemma align_not_le.mx {x y : 𝔽} (h : ¬ (x.e ≤ y.e)) 
: (align x y).1 = x.m * 2 ^ (x.e - y.e) :=
by simp [align_not_le h]

@[simp] lemma align_not_le.my {x y : 𝔽} (h : ¬ (x.e ≤ y.e)) 
: (align x y).2.1 = y.m :=
by simp [align_not_le h]

@[simp] lemma align_not_le.e {x y : 𝔽} (h : ¬ (x.e ≤ y.e)) 
: (align x y).2.2 = y.e :=
by simp [align_not_le h]

-- TODO: Move
lemma zpow_rat_cast (x y : ℤ) (hy : 0 ≤ y) : ((zpow x y) : ℚ) = (x : ℚ) ^ (y : ℤ) :=
begin
  simp only [zpow_eq_pow, zpow_def],
  lift y to ℕ using hy,
  rw [int.to_nat_coe_nat], norm_num,
end 

lemma align_spec (x y : 𝔽) : 
let a := align x y in
to_rat x = to_rat ⟨a.1, a.2.2⟩ ∧ to_rat y = to_rat ⟨a.2.1, a.2.2⟩ :=
begin 
  intros a,
  have h2 : ((2 : ℤ) : ℚ) = (2 : ℚ) := by norm_num,
  split; by_cases (x.e ≤ y.e); simp*;
  try { erw [zpow_rat_cast _ _ (sub_nonneg.2 (le_of_not_le h))], };
  try { erw [zpow_rat_cast _ _ (sub_nonneg.2 h)], };
  erw [mul_assoc, h2, ←fpow_add];
  simp; norm_num,
end

lemma align_semi_comm (x y : 𝔽) 
: (align x y).1 = (align y x).2.1 
∧ (align x y).2.1 = (align y x).1 
∧ (align x y).2.2 = (align y x).2.2 :=
begin 
  cases (lt_trichotomy x.e y.e),
  { have h' := not_le_of_lt h, replace h := le_of_lt h,
    simp [align_le h, align_not_le h'], },
  { cases h,
    { simp [align_le (le_of_eq h), align_le (ge_of_eq h), h], },
    { have h' := not_le_of_lt h, replace h := le_of_lt h,
      simp [align_le h, align_not_le h'], }, }
end 

-- Operations. 

def neg (x : 𝔽) : 𝔽 :=
⟨-x.m, x.e⟩

@[simp] lemma neg.m (x : 𝔽) : (neg x).m = -x.m := by simp [neg]

@[simp] lemma meg.e (x : 𝔽) : (neg x).e = x.e := by simp [neg]

def add (x y : 𝔽) : 𝔽 :=
let ⟨mx, my, e⟩ := align x y in ⟨mx + my, e⟩

lemma add.def (x y : 𝔽) : add x y = ⟨(align x y).1 + (align x y).2.1, (align x y).2.2⟩ := 
begin 
  unfold add, by_cases (x.e ≤ y.e),
  { simp only [align_le.mx h, align_le.my h, align_le.e h],
    unfold align, split_ifs, refl, },
  { simp only [align_not_le.mx h, align_not_le.my h, align_not_le.e h],
    unfold align, split_ifs, refl, }
end 

@[simp] lemma add.m (x y : 𝔽) : (add x y).m = (align x y).1 + (align x y).2.1 :=
by rw [add.def]; refl

@[simp] lemma add.e (x y : 𝔽) : (add x y).e = (align x y).2.2 :=
by rw [add.def]; refl

def mul (x y : 𝔽) : 𝔽 :=
⟨x.m * y.m, x.e + y.e⟩

@[simp] lemma mul.m (x y : 𝔽) : (mul x y).m = x.m * y.m := by simp [mul]

@[simp] lemma mul.e (x y : 𝔽) : (mul x y).e = x.e + y.e := by simp [mul]

-- Properties of to_rat. 

lemma to_rat.neg {x y : 𝔽} (h : to_rat x = to_rat y) : to_rat (neg x) = to_rat (neg y) :=
begin 
    simp only [neg, to_rat_mk] at *,
    iterate 2 { rw [int.cast_neg, ←neg_mul_eq_neg_mul], }, rw h,
end

lemma to_rat.add {x y x' y' : 𝔽} (h : to_rat x = to_rat y) (h' : to_rat x' = to_rat y')
: to_rat (add x x') = to_rat (add y y') :=
begin 
    have h2 : ((2 : ℤ) : ℚ) = (2 : ℚ) := by norm_num, -- TODO: I hate this.
    simp only [to_rat_mk, add.m, add.e] at *,
    by_cases (x.e ≤ x'.e); replace hx := h; clear h;
    by_cases (y.e ≤ y'.e); replace hy := h; clear h;
    try { simp only [align_le.mx hx, align_le.my hx, align_le.e hx], };
    try { simp only [align_le.mx hy, align_le.my hy, align_le.e hy], };
    try { simp only [align_not_le.mx hx, align_not_le.my hx, align_not_le.e hx], };
    try { simp only [align_not_le.mx hy, align_not_le.my hy, align_not_le.e hy], };
    push_cast; rw [add_mul, add_mul],
    { rw [h, mul_assoc, mul_assoc],
      erw [zpow_rat_cast _ _ (sub_nonneg.2 hx), h2, ←fpow_add],
      erw [zpow_rat_cast _ _ (sub_nonneg.2 hy), h2, ←fpow_add],
      simp, rw [h'], norm_num, norm_num, },
    { rw [h, mul_assoc, mul_assoc],
      erw [zpow_rat_cast _ _ (sub_nonneg.2 hx), h2, ←fpow_add],
      erw [zpow_rat_cast _ _ (sub_nonneg.2 (le_of_not_le hy)), h2, ←fpow_add],
      simp, rw [←h'], norm_num, norm_num, },
    { rw [h', mul_assoc, mul_assoc],
      erw [zpow_rat_cast _ _ (sub_nonneg.2 (le_of_not_le hx)), h2, ←fpow_add],
      erw [zpow_rat_cast _ _ (sub_nonneg.2 hy), h2, ←fpow_add],
      simp, rw [h], norm_num, norm_num, },
    { rw [h', mul_assoc, mul_assoc],
      erw [zpow_rat_cast _ _ (sub_nonneg.2 (le_of_not_le hx)), h2, ←fpow_add],
      erw [zpow_rat_cast _ _ (sub_nonneg.2 (le_of_not_le hy)), h2, ←fpow_add],
      simp, rw [←h], norm_num, norm_num, }
end 

lemma to_rat.mul {x y x' y' : 𝔽} (h : to_rat x = to_rat y) (h' : to_rat x' = to_rat y')
: to_rat (mul x x') = to_rat (mul y y') :=
begin 
  simp only [to_rat_mk, mul.m, mul.e] at *, 
  simp only [fpow_add (by norm_num : (2 : ℚ) ≠ 0)], push_cast,
  calc ↑(x.m) * ↑(x'.m) * ((2 : ℚ) ^ x.e * (2 : ℚ) ^ x'.e) 
      = (↑(x.m) * 2 ^ x.e) * (↑(x'.m) * 2 ^ x'.e) : by ring 
  ... = (↑(y.m) * 2 ^ y.e) * (↑(y'.m) * 2 ^ y'.e) : by rw [h, h']
  ... = ↑(y.m) * ↑(y'.m) * (2 ^ y.e * 2 ^ y'.e) : by ring
end 

-- 𝔽 is not a ring but 𝔽/R where R(x,y) iff to_rat x = to_rat y is a ring.

@[reducible] private def R : 𝔽 → 𝔽 → Prop := λ x y, to_rat x = to_rat y

private lemma R.reflexive : reflexive R := λ x, by unfold R; exact eq.refl

private lemma R.symmetric : symmetric R := λ x y, by unfold R; exact eq.symm

private lemma R.transitive : transitive R := λ x y z, by unfold R; exact eq.trans

private lemma R.equivalence : equivalence R := ⟨R.reflexive, R.symmetric, R.transitive⟩

instance dyadic_rational.setoid : setoid 𝔽 := ⟨R, R.equivalence⟩

def 𝔽R := quotient dyadic_rational.setoid 

instance : comm_ring 𝔽R := {
    zero := ⟦zero⟧,
    one := ⟦one⟧,
    neg := quotient.lift (λ x, ⟦neg x⟧) (λ a b h, quotient.sound $ to_rat.neg h),
    add := quotient.lift₂ (λ x y, ⟦add x y⟧) (λ a₁ a₂ b₁ b₂ h₁ h₂, quotient.sound $ to_rat.add h₁ h₂),
    mul := quotient.lift₂ (λ x y, ⟦mul x y⟧) (λ a₁ a₂ b₁ b₂ h₁ h₂, quotient.sound $ to_rat.mul h₁ h₂),
    zero_add := λ x, begin
      have h2 : ((2 : ℤ) : ℚ) = (2 : ℚ) := by norm_num,
      apply quotient.induction_on x, intros a, apply quotient.sound,
      simp only [add.def], show to_rat _ = to_rat a,
      by_cases (zero.e ≤ a.e),
      { simp only [align_le.mx h, align_le.my h, align_le.e h, to_rat_mk],
        push_cast, erw [zpow_rat_cast _ _ (sub_nonneg.2 h), h2], simp,  },
      { simp only [align_not_le.mx h, align_not_le.my h, align_not_le.e h, to_rat_mk],
        push_cast, erw [zpow_rat_cast _ _ (sub_nonneg.2 (le_of_not_le h)), h2], simp, }
    end,
    add_zero := λ x, begin 
      have h2 : ((2 : ℤ) : ℚ) = (2 : ℚ) := by norm_num,
      apply quotient.induction_on x, intros a, apply quotient.sound,
      simp only [add.def], show to_rat _ = to_rat a, 
      by_cases (a.e ≤ zero.e),
        { simp only [align_le.mx h, align_le.my h, align_le.e h, to_rat_mk],
          push_cast, erw [zpow_rat_cast _ _ (sub_nonneg.2 h), h2], simp,  },
        { simp only [align_not_le.mx h, align_not_le.my h, align_not_le.e h, to_rat_mk],
          push_cast, erw [zpow_rat_cast _ _ (sub_nonneg.2 (le_of_not_le h)), h2], simp, }
    end,
    add_left_neg := λ x, begin
      have h2 : ((2 : ℤ) : ℚ) = (2 : ℚ) := by norm_num,
      apply quotient.induction_on x, intros a, apply quotient.sound,
      simp only [add.def], show to_rat _ = to_rat _,
      by_cases ((neg a).e ≤ a.e),
      { simp only [align_le.mx h, align_le.my h, align_le.e h, to_rat_mk],
        push_cast, erw [zpow_rat_cast _ _ (sub_nonneg.2 h), h2], simp*,  },
      { simp only [align_not_le.mx h, align_not_le.my h, align_not_le.e h, to_rat_mk],
        push_cast, erw [zpow_rat_cast _ _ (sub_nonneg.2 (le_of_not_le h)), h2], simp*, }
    end,
    add_comm := λ x y, begin 
      apply quotient.induction_on₂ x y, intros a b, apply quotient.sound,
      simp only [add.def], show to_rat _ = to_rat _,
      simp_rw [align_semi_comm a b, add_comm],
    end,
    add_assoc := λ x y z, begin 
      apply quotient.induction_on₃ x y z, intros a b c, apply quotient.sound,
      simp only [add.def], show to_rat _ = to_rat _, dsimp, sorry,
    end,
    one_mul := sorry,
    mul_one := sorry,
    mul_comm := sorry,
    mul_assoc := sorry,
    left_distrib := sorry,
    right_distrib := sorry,
}

end dyadic_rational
