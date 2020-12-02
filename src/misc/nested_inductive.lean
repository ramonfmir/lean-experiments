-- Simple test.

import data.real.basic

section real_tree

inductive real_tree
| Leaf : ℝ → real_tree
| Node : real_tree → real_tree → real_tree 

open real_tree

--#print real_tree.rec
--#print real_tree.cases_on

def sum_real_tree : real_tree → ℝ 
| (Leaf r) := r 
| (Node t1 t2) := (sum_real_tree t1) + (sum_real_tree t2)

end real_tree 

-- List construction (Nested inductive).
-- Note: This will change in Lean 4?

section real_branching_tree

inductive real_branching_tree
| Leaf : ℝ → real_branching_tree
| Node : list real_branching_tree → real_branching_tree

open real_branching_tree

--#print real_branching_tree.rec
--#print real_branching_tree.cases_on

@[elab_as_eliminator] 
protected def real_branching_tree.cases_on'
: Π {C : real_branching_tree → Sort*} (x : real_branching_tree),
  (Π (a : ℝ), C (Leaf a)) → 
  (Π (l : list real_branching_tree), C (Node l)) → 
  C x
| C (Leaf a) mL mN := mL a 
| C (Node l) mL mN := mN l

def real_branching_tree.lt : real_branching_tree → real_branching_tree → Prop 
| t (Node l) := t ∈ l
| t _ := false

instance : has_lt real_branching_tree := ⟨real_branching_tree.lt⟩

@[simp] lemma real_branching_tree.lt_Node 
(t : real_branching_tree) (l : list real_branching_tree) 
: t < (Node l) ↔ t ∈ l :=
by rw [←real_branching_tree.lt.equations._eqn_2 t l]; refl

lemma real_branching_tree.lt_sizeof (t1 t2 : real_branching_tree) 
: t1 < t2 → sizeof t1 < sizeof t2 :=
begin
    intro H,
    cases t2 with r l,
    { cases H, },
    { change sizeof t1 < real_branching_tree.sizeof (Node l),
      rw real_branching_tree.Node.sizeof_spec l,
      have H1 := (real_branching_tree.lt_Node t1 l).1 H,
      have H2 := list.sizeof_lt_sizeof_of_mem H1,
      exact ((nat.one_add (sizeof l)).symm ▸ (nat.lt_succ_of_lt H2)), }
end

lemma real_branching_tree.lt_well_founded : well_founded real_branching_tree.lt :=
(subrelation.wf real_branching_tree.lt_sizeof) (inv_image.wf _ nat.lt_wf)

@[elab_as_eliminator]
protected def real_branching_tree.rec' 
: Π {C : real_branching_tree → Sort*},
  (Π (a : ℝ), C (Leaf a)) → 
  (Π (a : list real_branching_tree), C (Node a)) → 
  Π (x : real_branching_tree), C x :=
begin
    intros C m1 m2 x,
    apply (well_founded.fix real_branching_tree.lt_well_founded),
    intros y Hy,
    exact (real_branching_tree.cases_on' y m1 m2),
end 

--def real_branching_tree.sum : real_branching_tree → ℝ 
--| (Leaf r) := r
--| (Node l) := list.sum (list.map real_branching_tree.sum l)

-- This is still not good enough. Best we can do:

-- mutual inductive foo, list_foo
-- with foo : Type
-- | mk : list_foo -> foo
-- with list_foo : Type
-- | nil : list_foo
-- | cons : foo -> list_foo -> list_foo

end real_branching_tree
