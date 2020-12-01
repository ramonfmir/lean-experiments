-- Program Verification #3: Tail-recursive sum
import data.nat.basic

def sum_simple (f : ℕ → ℕ) : ℕ → ℕ
| 0       := f 0
| n@(m+1) := f n + sum_simple m

def sum_aux : ℕ → (ℕ → ℕ) → ℕ → ℕ
| a f 0       := f 0 + a
| a f n@(m+1) := sum_aux (f n + a) f m

def sum_tail := sum_aux 0

lemma sum_eq_aux (f n k) : sum_aux k f n = (sum_simple f n) + k :=
begin 
    revert k, induction n with n hn,
    { intros k, refl, },
    { intros k, dsimp [sum_aux, sum_simple],
      rw [hn (f (n + 1) + k), ←add_assoc, add_comm _ (f (n + 1))], },
end

theorem sum_eq (f n) : sum_tail f n = sum_simple f n :=
sum_eq_aux f n 0
