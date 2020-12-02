import data.list
import data.vector2

-- To mathlib: data.vector2.
namespace vector

lemma nth_repeat {α : Type*} {n : ℕ} (x : α) : 
∀ (i : fin n), vector.nth (vector.repeat x n) i = x :=
λ i, by rw vector.nth_eq_nth_le; dsimp [vector.repeat]; rw list.nth_le_repeat

def fin_range (n : ℕ) : vector (fin n) n :=
⟨list.fin_range n, list.length_fin_range n⟩

@[simp] lemma fin_range_zero : fin_range 0 = vector.nil := rfl

-- vector.has_mem ?
@[simp] lemma mem_fin_range {n : ℕ} (a : fin n) : a ∈ (fin_range n).to_list :=
list.mem_fin_range a

-- Define pairwise and 
-- lemma nodup_fin_range (n : ℕ) : (fin_range n).nodup := list.nodup_fin_range n

-- @[simp] lemma length_fin_range (n : ℕ) : (fin_range n).length = n := list.length_fin_range n

-- @[simp] lemma fin_range_eq_nil {n : ℕ} : fin_range n = [] ↔ n = 0 := list.fin_range_eq_nil n

end vector