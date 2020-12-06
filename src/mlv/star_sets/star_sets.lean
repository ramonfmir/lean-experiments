import data.real.basic 
import data.matrix.basic

open_locale matrix big_operators

@[reducible] private def vec (n : ℕ) : Type := fin n → ℝ
@[reducible] private def mat (n m : ℕ) : Type := matrix (fin n) (fin m) ℝ

structure star_set (n m : ℕ) :=
-- Centre. 
(c : vec n)
-- Basis.
(V : mat m n)
-- Predicate. 
(P : vec m → Prop)

def star_set.eval (n m : ℕ) (Θ : star_set n m) : set (vec n) :=
{ x | ∃ (α : vec m), x = Θ.c + ∑ i, (α i) • (Θ.V i) ∧ Θ.P α }
