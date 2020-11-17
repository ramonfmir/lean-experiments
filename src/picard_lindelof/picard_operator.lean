import analysis.calculus.mean_value
import topology.continuous_map
import measure_theory.interval_integral
import topology.metric_space.contracting

section to_mathlib

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

-- TODO: to mathlib.
lemma Sup_add_le_add_Sup 
{α : Type*} [complete_ordered_add_comm_monoid α] {A B : set α} 
: Sup (A + B) ≤ (Sup A) + (Sup B) :=
Sup_le $ λ _ ⟨a, b, ha, hb, hx⟩, (hx ▸ add_le_add (le_Sup ha) (le_Sup hb))

lemma supr_add_le_add_supr 
{α : Type*} [complete_ordered_add_comm_monoid α] {ι : Type*} (s t : ι → α)
: supr (s + t) ≤ (supr s) + (supr t) :=
supr_le $ λ i, add_le_add (le_supr s i) (le_supr t i)

end to_mathlib

-- Banach fixed point theorem:
-- https://github.com/leanprover-community/mathlib/blob/f25340175631cdc85ad768a262433f968d0d6450/src/topology/metric_space/lipschitz.lean#L110

-- Following Imperial's MA2AA1 notes.

noncomputable theory
open metric set asymptotics filter real measure_theory interval_integral topological_space
open_locale topological_space classical filter

section picard_operator

-- NOTE: This is meant to be [a, b].
variables {A : Type*} [linear_order A] [measurable_space A]
          [topological_space A] [compact_space A]

variables (μ : measure A)

-- NOTE: This is meant to be ℝ^n.
variables {B : Type*} [normed_group B] [normed_space ℝ B]
          [second_countable_topology B]
          [complete_space B] [measurable_space B]
          [borel_space B]

variables (t0 : A) (f : A → B → B)

def picard_operator_raw (x : C(A, B)) :=
λ t, (x t0) + ∫ s in t0..t, (f s (x s)) ∂μ

lemma picard_operator_raw_continuous 
: ∀ (x : C(A, B)), continuous (picard_operator_raw μ t0 f x) :=
begin 
    intros x, rw continuous_iff_continuous_at,
    intros a, unfold continuous_at,
    sorry, 
    -- Perhaps just deduce this from Lipschitz.
end 

def picard_operator : C(A, B) → C(A, B) :=
λ x, ⟨picard_operator_raw μ t0 f x, picard_operator_raw_continuous μ t0 f x⟩

-- Should be easy. Assuming A and B nonempty.
instance : nonempty C(A, B) := sorry

instance : has_edist C(A, B) := ⟨λ x y, supr (λ t, edist (x t) (y t))⟩

instance : emetric_space C(A, B) := {
    edist_self := begin 
        intros x, unfold edist, erw [supr_eq_bot], 
        intros t, erw [metric_space.edist_dist, metric_space.dist_self],
        norm_num,
    end,
    eq_of_edist_eq_zero := begin 
        intros x y h, unfold edist at h, erw [supr_eq_bot] at h,
        ext i, replace h := h i, erw [metric_space.edist_dist, ennreal.of_real_eq_zero] at h,
        replace h := le_antisymm h dist_nonneg,
        exact metric_space.eq_of_dist_eq_zero h,
    end,
    edist_comm := begin
        intros x y, unfold edist, apply le_antisymm,
        { rw supr_le_iff, intros i, 
          erw [metric_space.edist_dist, metric_space.dist_comm, ←metric_space.edist_dist],
          exact (le_supr (λ t, metric_space.edist (y t) (x t)) i), },
        { -- TODO: Avoid repetition.
          rw supr_le_iff, intros i, 
          erw [metric_space.edist_dist, metric_space.dist_comm, ←metric_space.edist_dist],
          exact (le_supr (λ t, metric_space.edist (x t) (y t)) i), }
    end,
    edist_triangle := begin
        intros x y z, unfold edist,
        suffices hle1 : 
            supr (λ t, metric_space.edist (x t) (z t)) ≤
            supr (λ t, (metric_space.edist (x t) (y t)) + (metric_space.edist (y t) (z t))),
        { have hle2 := supr_add_le_add_supr 
            (λ t, metric_space.edist (x t) (y t))
            (λ t, metric_space.edist (y t) (z t)),
          exact (le_trans hle1 hle2), },
        rw supr_le_iff, intros i, 
        have hxyz := metric_space.dist_triangle (x i) (y i) (z i),
        replace hxyz := ennreal.of_real_le_of_real hxyz,
        replace hxyz := le_trans hxyz ennreal.of_real_add_le,
        repeat { rw [←metric_space.edist_dist] at hxyz, },
        exact (@le_supr_of_le _ _ _ (λ t, metric_space.edist (x t) (y t) + metric_space.edist (y t) (z t)) _ i hxyz),
    end,
}

instance : complete_space C(A, B) := sorry

-- Ideally, we can show that it is a Banach space.
--instance : normed_group C(Icc a b, E) := sorry
--instance : normed_space ℝ C(Icc a b, E) := sorry
--instance : complete_space C(Icc a b, E) := sorry

variables (K : nnreal) (hK : K < 1)

lemma picard_operator_lipschitz 
: lipschitz_with K (picard_operator μ t0 f) :=
sorry 

def picard_efixed_point : C(A, B) := 
contracting_with.efixed_point (picard_operator μ t0 f) ⟨hK, picard_operator_lipschitz μ t0 f K⟩ sorry sorry

#check picard_efixed_point μ t0 f K hK

end picard_operator
