import analysis.special_functions.exp_log 

noncomputable theory

open set real

section rounding

/-- Addition of affine forms with error. -/
-- TODO: Move.
def log₂ (x : ℝ) := log x / log 2

-- TODO: This should happen over the dyadic rationals.
-- Or not, but prove a lemma that there exists a dyadic that casts to the computed real.
-- TODO: Move to dyadic.
def round_down (p : ℤ) (r : ℝ) : ℝ := ⌊r * 2 ^ p⌋ * 2 ^ -p 

lemma round_down_zero (p : ℤ) : round_down p 0 = 0 := 
by simp [round_down]

def round_up (p : ℤ) (r : ℝ) : ℚ := ⌈r * 2 ^ p⌉ * 2 ^ -p 

-- TODO: This should be shorter.
lemma round_up_mono (p : ℤ) (x y : ℝ) (h : x ≤ y) 
: round_up p x ≤ round_up p y :=
begin 
  simp [round_up], refine (mul_le_mul_right _).2 _, 
  { simp, exact (fpow_pos_of_pos (by linarith) p), },
  { simp, apply ceil_mono, refine (mul_le_mul_right _).2 h,
    exact fpow_pos_of_pos (by linarith) p, },
end 

def truncate_down (p : ℕ) (r : ℝ) : ℝ := round_down (p - ⌊log₂ r⌋ - 1) r

lemma truncate_down_zero (p : ℕ) : truncate_down p 0 = 0 := 
by simp [truncate_down, round_down_zero]

def truncate_up (p : ℕ) (r : ℝ) : ℝ := round_up (p - ⌊log₂ r⌋ - 1) r

lemma truncate_up_mono (p : ℕ) (x y : ℝ) (h : x ≤ y)
: truncate_up p x ≤ truncate_up p x :=
by simp [truncate_up, round_up_mono]  

-- We need something like ⌈a * b⌉ ≥ ⌈a⌉ * b if b ≥ 1. Then we should
-- assume that p - ⌊log₂ r⌋ ≥ 1. That is not great, it holds regardless...
lemma truncate_up_ge (p : ℕ) (r : ℝ) : r ≤ truncate_up p r :=
begin 
  simp [truncate_up, round_up], sorry, 
end 

-- Def trunc-bound-eucl (p. 152)
def truncate_with_error (p : ℕ) (r : ℝ) : ℝ × ℝ := 
let q := truncate_down p r, e := truncate_up p (abs (q - r)) in ⟨q, e⟩ 

lemma truncate_with_error_is_bound (p : ℕ) (r : ℝ) 
: ∃ e : ℝ, (truncate_with_error p r).1 = r + e ∧ abs e ≤ (truncate_with_error p r).2 :=
begin 
  use [truncate_down p r - r], split, 
  { ring, },
  { simp [truncate_with_error, truncate_up_ge], }
end 

end rounding
