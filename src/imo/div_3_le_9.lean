import tactic
import data.nat.basic

open nat

lemma div_3_le_9 (x : ℕ) (h9 : x ≤ 9) (h3 : 3 ∣ x) : x = 0 ∨ x = 3 ∨ x = 6 ∨ x = 9 :=
begin
    cases h3 with k h3k,
    have : k ≤ 3 := by linarith,
    interval_cases k; dec_trivial!,
end
