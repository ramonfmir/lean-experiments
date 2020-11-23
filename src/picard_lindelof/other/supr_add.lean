import order.complete_lattice
import data.real.ennreal

-- TODO: Is there a better way?
class complete_ordered_add_comm_monoid (α : Type*) 
extends complete_lattice α, add_comm_monoid α :=
(add_le_add_left : ∀ (a b : α), a ≤ b → ∀ (c : α), c + a ≤ c + b)
(lt_of_add_lt_add_left : ∀ (a b c : α), a + b < a + c → b < c)

instance to_complete_lattice {α : Type*} [complete_ordered_add_comm_monoid α] 
: complete_lattice α := by apply_instance

instance to_ordered_add_comm_monoid {α : Type*} [complete_ordered_add_comm_monoid α] 
: ordered_add_comm_monoid α := { .._inst_1 }

noncomputable instance ennreal.complete_ordered_add_comm_monoid 
: complete_ordered_add_comm_monoid ennreal := 
{ ..ennreal.canonically_ordered_comm_semiring }

lemma Sup_add_le_add_Sup 
{α : Type*} [complete_ordered_add_comm_monoid α] {A B : set α} 
: Sup (A + B) ≤ (Sup A) + (Sup B) :=
Sup_le $ λ _ ⟨a, b, ha, hb, hx⟩, (hx ▸ add_le_add (le_Sup ha) (le_Sup hb))

lemma supr_add_le_add_supr 
{α : Type*} [complete_ordered_add_comm_monoid α] {ι : Type*} (s t : ι → α)
: supr (s + t) ≤ (supr s) + (supr t) :=
supr_le $ λ i, add_le_add (le_supr s i) (le_supr t i)
