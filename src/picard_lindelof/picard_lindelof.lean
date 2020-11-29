import picard_lindelof.definitions
import picard_lindelof.other.interval_integral

-- Following Imperial's MA2AA1 notes.

noncomputable theory
open metric set asymptotics filter real measure_theory 
open interval_integral topological_space uniform_space
open picard_operator
open_locale topological_space classical filter uniformity 

section picard_lindelof

local infix ` →ᵇ `:25 := bounded_continuous_function 

#check abs_of_nonpos

-- NOTE: This is meant to be ℝ^n.
variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                      [normed_space ℝ E] [complete_space E] [second_countable_topology E]

lemma P.lipschitz_at' (x₀ : E) (v : α → E → E) (I : IVP(v)) (x y : α →ᵇ E) (t : α)
: dist (P x₀ v I x t) (P x₀ v I y t) ≤ I.K * dist x y :=
begin 
    simp, rw dist_eq_norm,
    calc ∥(∫ s in 0..t, v s (x s)) - (∫ s in 0..t, v s (y s))∥
        = ∥∫ s in 0..t, (v s (x s)) - (v s (y s))∥ 
        : by rw interval_integral.integral_sub (I.hintegrable x t) (I.hintegrable y t)
    ... ≤ ∫ s in Ioc (min 0 t) (max 0 t), ∥(v s (x s)) - (v s (y s))∥
        : interval_integral.norm_integral_le_integral_norm_Ioc
    ... = ∫ s in Ioc (min 0 t) (max 0 t), (dist (v s (x s)) (v s (y s)))
        : by congr; ext; exact (dist_eq_norm _ _).symm
    ... ≤ ∫ s in Ioc (min 0 t) (max 0 t), I.K * dist (x s) (y s)
        : begin 
            apply integral_mono,
            { -- TODO: Something about integrable (bounded) distances.
              sorry, },
            { sorry, },
            intros t; dsimp, 
            exact ((lipschitz_with_iff_dist_le_mul.1 (I.hlipschitz t)) (x t) (y t)),
        end
    ... ≤ ∫ s in Ioc (min 0 t) (max 0 t), I.K * dist x y
        : begin 
            apply integral_mono sorry sorry,
            intros t; dsimp, mono,
            { apply le_cInf,
              { exact bounded_continuous_function.dist_set_exists, },
              { intros b hb, exact (hb.2 t), }, },
            { exact dist_nonneg, },
            { exact I.K.2, },
        end
    ... ≤ (abs t.1) * (I.K * dist x y) 
        : begin 
            rw [measure_theory.integral_const, measure.restrict_apply_univ],
            simp only [α.volume_Ioc, ennreal.to_real_of_real', ←neg_sub t.1],
            -- TODO: This should be simpler.
            by_cases h : 0 ≤ t,
            { erw [max_eq_right h, min_eq_left h, sub_zero t.val],
              replace h : 0 ≤ t.1 := h, rw [max_eq_left h],
              refine (mul_le_mul _ (le_refl _) _ _),
              { exact le_abs_self t.1, },
              { exact (mul_nonneg I.K.2 dist_nonneg), },
              { exact abs_nonneg t.1, }, },
            { replace h := le_of_not_le h,
              erw [max_eq_left h, min_eq_right h, zero_sub t.val],
              replace h : t.1 ≤ 0 := h, 
              have h' := neg_le_neg h,
              rw neg_zero at h', rw [max_eq_left h'],
              refine (mul_le_mul _ (le_refl _) _ _),
              { rw [abs_of_nonpos h], },
              { exact (mul_nonneg I.K.2 dist_nonneg), },
              { exact abs_nonneg t.1, }, },
          end
    ... ≤ I.K * (dist x y)
        : sorry --mul_le_of_le_one_left (mul_nonneg I.K.2 dist_nonneg) t.2.2
end

-- lemma P.dist_eq_neg (x₀ : E) (v : α → E → E) (I : IVP(v)) (x y : α →ᵇ E) (t : α) 
-- : dist (P x₀ v I x t) (P x₀ v I y t) = dist (P x₀ v I x (-t)) (P x₀ v I y (-t)) :=
-- begin 
--     simp [dist_eq_norm],
--     erw [interval_integral.integral_sub (I.hintegrable x t) (I.hintegrable y t)],
-- end 

lemma P.lipschitz_at (x₀ : E) (v : α → E → E) (I : IVP(v)) (x y : α →ᵇ E) (t : α) 
: dist (P x₀ v I x t) (P x₀ v I y t) ≤ I.K * dist x y :=
begin
    by_cases ht : 0 ≤ t,
    { exact P.lipschitz_at' x₀ v I x y t ht, },
    { sorry, },
end 

-- TODO: Move. 
private lemma mul_Inf {K : ℝ} (hK : 0 ≤ K) {p : ℝ → Prop} 
(h : ∃ x, 0 ≤ x ∧ p x) (hp : p (Inf {x | 0 ≤ x ∧ p x}))
: K * Inf {x | 0 ≤ x ∧ p x} = Inf {y | ∃ x, (y : ℝ) = K * x ∧ 0 ≤ x ∧ p x} :=
begin 
  rcases h with ⟨i, hnni, hpi⟩,
  let S := {y | ∃ x, y = K * x ∧ 0 ≤ x ∧ p x},
  apply le_antisymm,
  { have h1 : (∃ (x : ℝ), x ∈ S) := ⟨K * i, ⟨i, rfl, hnni, hpi⟩⟩,
    have h2 : (∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → x ≤ y),
    { existsi (0 : ℝ), rintros y ⟨x, hy, hnnx, hpx⟩,
      rw hy, exact mul_nonneg hK hnnx, },
    rw real.le_Inf S h1 h2, rintros z ⟨w, hz, hnnw, hpw⟩,
    rw hz, mono,
    { refine cInf_le _ ⟨hnnw, hpw⟩, use 0, intros a ha, exact ha.1, },
    { apply le_cInf,
      { use [i, ⟨hnni, hpi⟩], },
      { intros b hb, exact hb.1, }, }, },
  { apply real.Inf_le,
    { use [0], intros y hy, rcases hy with ⟨x, ⟨hy, hnnx, hpx⟩⟩,
      rw hy, exact mul_nonneg hK hnnx, },
    { use [Inf {x : ℝ | 0 ≤ x ∧ p x}], refine ⟨rfl, _, _⟩, 
      { apply le_cInf,
        { use [i, ⟨hnni, hpi⟩], },
        { intros b hb, exact hb.1, }, },
      { exact hp, }, }, },
end

lemma P.lipschitz (μ : measure α) (v : α → E → E) (I : IVP(v)) 
: lipschitz_with I.K (P v I) :=
begin 
  intros x y, cases I.K with K hKnonneg,
  unfold edist, rw metric_space.edist_dist, unfold dist,
  rw metric_space.edist_dist, unfold dist, 
  rw ←ennreal.of_real_eq_coe_nnreal hKnonneg,
  rw ←ennreal.of_real_mul hKnonneg,
  apply ennreal.of_real_le_of_real,
  have h1 : ∃ (C : ℝ), 0 ≤ C ∧ ∀ (t : α), dist (x t) (y t) ≤ C := dist_set_exists,
  have h2 : ∀ (t : α), dist (x t) (y t) ≤ Inf {C : ℝ | 0 ≤ C ∧ ∀ (s : α), dist (x s) (y s) ≤ C},
  { intros t, apply le_cInf,
    { use h1, },
    { intros b hb, exact (hb.2 t), }, },
  erw mul_Inf hKnonneg h1 h2, apply cInf_le_cInf,
  { use 0, intros b hb, exact hb.1, },
  { cases h1 with C hC, use [K * C, C, ⟨rfl, hC.1, hC.2⟩], },
  clear h1 h2,
  rintros C ⟨C', ⟨hC, hnnC', hC'⟩⟩, rw hC,
  refine ⟨mul_nonneg hKnonneg hnnC', _⟩, intros s,
  have hC's := hC' s,
  sorry,
end

--lemma P.edist_lt_top : Π (x : A →ᵇ B), edist x (P x) < ⊥ := sorry

-- def P.efixed_point_of_lipschitz (hf : ∀ s, lipschitz_with K (f s)) : ℝ →ᵇ B := 
-- contracting_with.efixed_point P ⟨hK, P.lipschitz_of_lipschitz hf⟩ sorry sorry

--#check contracting_with.efixed_point P

/-- There exists only one solution of an ODE \(\dot x=v(t, x)\) with
a given initial value provided that RHS is Lipschitz continuous in `x`. -/
theorem ODE_solution_unique' {v : ℝ → E → E}
  {K : nnreal} (hv : ∀ t, lipschitz_with K (v t))
  {f g : ℝ → E} {a b : ℝ}
  (hf : continuous_on f (Icc a b))
  (hf' : ∀ t ∈ Ico a b, has_deriv_within_at f (v t (f t)) (Ioi t) t) -- integral_has_deriv_within_at_right
  (hg : continuous_on g (Icc a b))
  (hg' : ∀ t ∈ Ico a b, has_deriv_within_at g (v t (g t)) (Ioi t) t)
  (ha : f a = g a) :
  ∀ t ∈ Icc a b, f t = g t := 
begin
    sorry,
end

end picard_lindelof
