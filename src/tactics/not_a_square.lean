import tactic
import data.nat.basic 
import data.zmod.basic

namespace tactic.interactive

open tactic.interactive («have»)
open tactic (get_local infer_type) 
open lean.parser interactive interactive.types (texpr)

meta def using_texpr := (tk "using" *> ident)

lemma le_of_mul_self_eq {n m : ℕ} (h : n = m * m) : m ≤ n := sorry

meta def not_a_square (x : parse ident) (h : parse using_texpr) : tactic unit :=
do {`(false) ← tactic.target,
    xe ← get_local x,
    he ← get_local h,
    «have» ("hl" : name) none ``(zero_le %%xe),
    «have» ("hu" : name) none ``(le_of_mul_self_eq %%he),
    `[interval_cases x; try {cases hx}] }
<|> tactic.trace "Error"

lemma three_not_a_square : ¬ ∃ x, 3 = x * x :=
begin 
    rintros ⟨x, hx⟩,
    not_a_square x using hx,
end 

end tactic.interactive