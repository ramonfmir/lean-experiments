import analysis.calculus.mean_value
import topology.continuous_map
import measure_theory.interval_integral
import topology.metric_space.contracting
import topology.metric_space.cau_seq_filter
import topology.algebra.continuous_functions

noncomputable theory
open metric set asymptotics filter real measure_theory interval_integral topological_space uniform_space
open_locale topological_space classical filter uniformity

-- NOTE: This is meant to be [a, b].
variables {A : Type*} [linear_order A] [measurable_space A]
          [topological_space A] [compact_space A] [nonempty A]
          [uniform_space A] [complete_space A] -- Maybe

-- NOTE: This is meant to be ℝ^n.
variables {B : Type*} [normed_group B] [normed_space ℝ B]
          [second_countable_topology B]
          [complete_space B] [measurable_space B]
          [borel_space B] [nonempty B]
          [complete_lattice B] [ring B] [topological_ring B] -- Maybe


instance : nonempty C(A, B) := ⟨⟨λ (a : A), @nonempty.some B (by apply_instance), continuous_const⟩⟩

-- TODO: Isn't this deduced from has_dist?
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

open continuous_functions

instance : ring C(A, B) := continuous_map_ring

-- TODO: Move
private lemma ennreal.of_real_supr {ι : Type*} (f : ι → ℝ) 
: ennreal.of_real (supr f) = supr (λ t, ennreal.of_real (f t)) := 
begin 
    ext, split,
    { sorry, },
    { sorry, }
end 

instance : complete_space C(A, B) := 
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
                 (λ (t : A), ennreal.of_real (norm (((u j) - (u N)) t))),
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