import data.int.basic
import data.real.basic
import data.buffer.parser
import tactic.find
import analysis.special_functions.pow

import taylor_models.zpow

open parser zpow

structure ideal_float :=
(m : ℤ)
(e : ℤ)

local notation `𝔽` := ideal_float

namespace ideal_float

--meta instance : has_to_format ℤ := 
--⟨λ z, int.rec_on z (λ k, ↑k) (λ k, "-"++↑(k+1))⟩

meta instance : has_to_format 𝔽 :=
⟨λ f, (to_fmt f.m) ++ (to_fmt " * 2^") ++ (to_fmt f.e)⟩

@[reducible] noncomputable def to_real (x : 𝔽) : ℝ :=
x.m * (2 ^ x.e)

@[simp] lemma to_real_mk {m e : ℤ} : to_real ⟨m, e⟩ = m * (2 ^ e) := rfl

-- Needed.

instance : has_pow ℤ ℤ := ⟨zpow⟩
--local attribute [instance] zpow

-- Basic operations.

@[reducible] def zero : 𝔽 := ⟨0, 0⟩

lemma zero_spec : to_real zero = 0 := by simp

@[reducible] def one : 𝔽 := ⟨1, 0⟩

lemma one_spec : to_real one = 1 := by simp

@[reducible] def align (x y : 𝔽) : ℤ × ℤ × ℤ :=
if x.e ≤ y.e 
then ⟨x.m, y.m * 2 ^ (y.e - x.e), x.e⟩
else ⟨x.m * 2 ^ (x.e - y.e), y.m, y.e⟩ 

@[simp ]lemma align_le {x y : 𝔽} (h : x.e ≤ y.e) 
: align x y = ⟨x.m, y.m * 2 ^ (y.e - x.e), x.e⟩ := 
by simp only [align]; split_ifs; refl

@[simp] lemma align_not_le {x y : 𝔽} (h : ¬ (x.e ≤ y.e)) 
: align x y = ⟨x.m * 2 ^ (x.e - y.e), y.m, y.e⟩ := 
by simp only [align]; split_ifs; refl

-- TODO: Move
lemma zpow_real_cast (x y : ℤ) (hy : 0 ≤ y) : ((zpow x y) : ℝ) = (x : ℝ) ^ (y : ℝ) :=
begin
    simp only [zpow_eq_pow, zpow_def],
    lift y to ℕ using hy,
    rw [real.rpow_int_cast, int.to_nat_coe_nat], norm_num,
end 

lemma align_spec (x y : 𝔽) : 
let a := align x y in
to_real x = to_real ⟨a.1, a.2.2⟩ ∧ to_real y = to_real ⟨a.2.1, a.2.2⟩ :=
begin 
    intros a,
    have h2 : ((2 : ℤ) : ℝ) = (2 : ℝ) := by norm_num,
    split; by_cases (x.e ≤ y.e); simp*;
    try { erw [zpow_real_cast _ _ (sub_nonneg.2 (le_of_not_le h))], };
    try { erw [zpow_real_cast _ _ (sub_nonneg.2 h)], };
    erw [mul_assoc, h2, ←real.rpow_int_cast, ←real.rpow_int_cast, ←real.rpow_add];
    simp; norm_num,
end

def neg (x : 𝔽) : 𝔽 :=
⟨-x.m, x.e⟩

def add (x y : 𝔽) : 𝔽 :=
let ⟨mx, my, e⟩ := align x y in ⟨mx + my, e⟩

def sub (x y : 𝔽) : 𝔽 :=
let ⟨mx, my, e⟩ := align x y in ⟨mx - my, e⟩

def mul (x y : 𝔽) : 𝔽 :=
⟨x.m * y.m, x.e * y.e⟩

instance : comm_ring 𝔽 := {
    zero := zero,
    one := one,
    neg := neg,
    add := add,
    mul := mul,
    zero_add := λ x, sorry,
    add_zero := λ x, sorry,
    add_left_neg := sorry,
    add_comm := sorry,
    add_assoc := λ x y z, sorry,
    one_mul := sorry,
    mul_one := sorry,
    mul_comm := sorry,
    mul_assoc := sorry,
    left_distrib := sorry,
    right_distrib := sorry,
}

end ideal_float
