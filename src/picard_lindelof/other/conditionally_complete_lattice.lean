import order.conditionally_complete_lattice

open set

-- TODO: Move: conditionally_complete_lattice
private lemma le_csupr_iff.mpr
{α : Type*} {ι : Sort*} [conditionally_complete_lattice α] 
{s : ι → α} {a : α} (hs : bdd_above (range s)) (h : ∀ (b : α), (∀ (i : ι), s i ≤ b) → a ≤ b)
: a ≤ supr s := 
h (supr s) (λ i, le_csupr hs i)
