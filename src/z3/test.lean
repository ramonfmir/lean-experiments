import data.nat.basic 
import smt2

lemma test : ∀ a b : ℕ, a < b → a + 1 < b + 1 :=
by { intros a b h, z3, } -- Probably only works with older Lean.
