import data.nat.basic 

lemma schur (r : ℕ) 
: ∃ (S : ℕ) (f : fin S → fin r) (c : fin r) (x y z : fin S),
  { x, y, z } ⊆ { w | f w = c } → x + y = z := 
sorry
