import data.real.basic 
import data.matrix.basic 

notation `ℝ^[` n `]` := fin n → ℝ
notation `ℝ^[` n `,` m `]` := matrix (fin m) (fin n) ℝ

-- Infinitely many layers. There were issues with fin and casting...
structure nn :=
(n : ℕ → ℕ)
(b : Π i, ℝ^[n (i + 1)])
(M : Π i, ℝ^[(n i), (n (i + 1))])
(f : Π i, ℝ^[n (i + 1)] → ℝ^[n (i + 1)])

-- Evaluate result at depth d.
def eval_nn (φ : nn) : Π (d : ℕ) (v : ℝ^[φ.n 0]), ℝ^[φ.n d] 
| 0     v := v  
| (l+1) v := φ.f l (matrix.mul_vec (φ.M l) (eval_nn l v) + (φ.b l))
