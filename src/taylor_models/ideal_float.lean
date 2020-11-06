import data.int.basic
import data.real.basic
import data.buffer.parser
import tactic.find

open parser

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

def zpow : has_pow ℤ ℤ := sorry
local attribute [instance] zpow

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

lemma align_spec (x y : 𝔽) : 
let a := align x y in
to_real x = to_real ⟨a.1, a.2.2⟩ ∧ to_real y = to_real ⟨a.2.1, a.2.2⟩ :=
begin 
    intros a,
    split; by_cases (x.e ≤ y.e); simp*,
    -- These should be solved by norm_num or ring, but zpow is not defined...
    { sorry, },
    { sorry, },
end

def neg (x : 𝔽) : 𝔽 :=
⟨-x.m, x.e⟩

def add (x y : 𝔽) : 𝔽 :=
let ⟨mx, my, e⟩ := align x y in ⟨mx + my, e⟩

def sub (x y : 𝔽) : 𝔽 :=
let ⟨mx, my, e⟩ := align x y in ⟨mx - my, e⟩

def mul (x y : 𝔽) : 𝔽 :=
⟨x.m * y.m, x.e * y.e⟩

instance : has_zero 𝔽 := ⟨zero⟩
instance : has_one 𝔽 := ⟨one⟩
instance : has_neg 𝔽 := ⟨neg⟩
instance : has_add 𝔽 := ⟨add⟩
instance : has_sub 𝔽 := ⟨sub⟩
instance : has_mul 𝔽 := ⟨mul⟩

end ideal_float
