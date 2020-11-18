import analysis.calculus.mean_value
import topology.continuous_map
import measure_theory.interval_integral
import topology.metric_space.contracting
import topology.metric_space.cau_seq_filter
import topology.algebra.continuous_functions

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

-- Following Imperial's MA2AA1 notes and Ch 2 of 'Spectral Theory and Quantum Mechanics'.

noncomputable theory
open metric set asymptotics filter real measure_theory interval_integral topological_space uniform_space
open_locale topological_space classical filter uniformity

section picard_operator

-- NOTE: This is meant to be [a, b].
variables {A : Type*} [linear_order A] [measurable_space A]
          [topological_space A] [compact_space A] [nonempty A]
          [uniform_space A] [complete_space A] -- Maybe

variables (μ : measure A)

-- NOTE: This is meant to be ℝ^n.
variables {B : Type*} [normed_group B] [normed_space ℝ B]
          [second_countable_topology B]
          [complete_space B] [measurable_space B]
          [borel_space B] [nonempty B]
          [complete_lattice B] [ring B] [topological_ring B] -- Maybe

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

instance : nonempty C(A, B) := ⟨⟨λ (a : A), @nonempty.some B (by apply_instance), continuous_const⟩⟩

instance : has_norm C(A, B) := ⟨λ x, supr (λ t, norm (x t))⟩

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

#check sequentially_complete.seq
#check image_le_of_liminf_slope_right_lt_deriv_boundary
#check @cauchy_seq.tendsto_lim 
#check dist_le_of_le_geometric_two_of_tendsto₀
#check @edist_mem_uniformity
#check @ennreal.of_real_lt_of_real_iff
#check @ennreal.of_real
#check @dist_eq_norm
#check metric_space.edist_dist
#check ennreal.of_real_lt_of_real_iff
#check dist_eq_norm
#print ennreal.coe_to_real
#check finset.supr_coe
--#find (_ - _) _ = (_ _) - (_ _)

open continuous_functions

instance : ring C(A, B) := continuous_map_ring

-- TODO: Move
private lemma ennreal.of_real_supr {ι : Type*} (f : ι → ℝ) 
: ennreal.of_real (supr f) = supr (λ t, ennreal.of_real (f t)) := 
begin 
    unfold ennreal.of_real, unfold nnreal.of_real,
    sorry,
end 

lemma continuous_complete : complete_space C(A, B) := 
begin 
    apply emetric.complete_of_cauchy_seq_tendsto,
    intros u hu,
    have huε : is_cau_seq norm u,
    { cases cauchy_iff.1 hu with hu1 hu2,
      intros ε hε,
      have hεrw := (ennreal.of_real_lt_of_real_iff hε),
      have hennε := hεrw.2 hε,
      rw ennreal.of_real_zero at hennε,
      rcases hu2 {x | edist x.1 x.2 < ennreal.of_real ε} (edist_mem_uniformity hennε) with ⟨t, ⟨ht, htsub⟩⟩,
      simp at ht, cases ht with N hN,
      existsi N, intros j hj,
      unfold has_norm.norm,
      have hujN := @htsub (u j, u N) (set.mk_mem_prod (hN j hj) (hN N (le_refl N))),
      simp at hujN,
      unfold edist at hujN,
      -- TODO: Prove some nice properties of edist.
      have heq : (λ (t : A), metric_space.edist ((u j) t) ((u N) t)) =
                 (λ (t : A), ennreal.of_real ∥(((u j) - (u N)) t)∥ ),
      { funext, erw [←dist_eq_norm, metric_space.edist_dist], },
      apply (ennreal.of_real_lt_of_real_iff hε).1,
      rw ennreal.of_real_supr, 
      sorry,
      -- TODO: So close. Will this work when ennreal.of_real_supr is proved?
      --erw ←heq,
      --exact hujN,
      },

    let fn := λ x n, (u n) x,
    let f := λ x, (lim at_top (fn x)), 
    have hf : continuous f := sorry,
    --have h := tendsto_nhds_lim,
    use [⟨f, hf⟩],
    rw emetric.cauchy_seq_iff at hu,
    rw emetric.tendsto_nhds,
    intros ε hε, 

    sorry,
end 

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
