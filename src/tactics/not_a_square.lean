import tactic
import data.nat.basic

namespace tactic.interactive

open tactic.interactive («have»)
open tactic (get_local infer_type) 
open lean.parser interactive interactive.types (texpr)

meta def using_texpr := (tk "using" *> texpr)

lemma le_of_mul_self_eq {n m : ℕ} (h : n = m * m) : m ≤ n := sorry

meta def not_a_square_aux (x : parse texpr) (h : parse using_texpr) : tactic unit :=
do {xe ← tactic.to_expr x,
    he ← tactic.to_expr h,
    «have» ("hl" : name) none ``(zero_le %%xe),
    «have» ("hu" : name) none ``(le_of_mul_self_eq %%he),
    interval_cases x none none }

meta def not_a_square : tactic unit :=
do `[rintros ⟨x, hx⟩, not_a_square_aux x using hx; cases hx]
<|> tactic.trace "Error"

example : ¬ ∃ x, 3 = x * x := by not_a_square

-- Timeout...
example : ¬ ∃ x, 30 = x * x := by not_a_square

end tactic.interactive