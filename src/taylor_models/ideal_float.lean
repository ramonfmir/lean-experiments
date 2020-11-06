import data.int.basic
import data.real.basic
import data.buffer.parser
import tactic.find

open parser

structure ideal_float :=
(m : ℤ)
(e : ℤ)

--meta instance : has_to_format ℤ := 
--⟨λ z, int.rec_on z (λ k, ↑k) (λ k, "-"++↑(k+1))⟩

meta instance : has_to_format ideal_float :=
⟨λ f, (to_fmt f.m) ++ (to_fmt "*2^") ++ (to_fmt f.e)⟩

noncomputable def to_real (x : ideal_float) : ℝ :=
x.m * (2 ^ x.e)

-- Needed.

def zpow : has_pow ℤ ℤ := sorry
local attribute [instance] zpow

-- Basic operations.

def align (x y : ideal_float) : ℤ × ℤ × ℤ :=
if x.e ≤ y.e 
then ⟨x.m, y.m * 2 ^ (y.e - x.e), x.e⟩
else ⟨x.m * 2 ^ (x.e - y.e), y.m, y.e⟩ 

def neg (x : ideal_float) : ideal_float :=
⟨-x.m, x.e⟩

def add (x y : ideal_float) : ideal_float :=
let ⟨mx, my, e⟩ := align x y in ⟨mx + my, e⟩

def sub (x y : ideal_float) : ideal_float :=
let ⟨mx, my, e⟩ := align x y in ⟨mx - my, e⟩

def mul (x y : ideal_float) : ideal_float :=
⟨x.m * y.m, x.e * y.e⟩
