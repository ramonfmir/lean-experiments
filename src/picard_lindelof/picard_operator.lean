import analysis.calculus.mean_value
import topology.continuous_map
import measure_theory.interval_integral
import topology.metric_space.contracting
import topology.metric_space.cau_seq_filter
import topology.bounded_continuous_function


-- Following Imperial's MA2AA1 notes and Ch 2 of 'Spectral Theory and Quantum Mechanics'.

noncomputable theory
open metric set asymptotics filter real measure_theory 
open interval_integral topological_space uniform_space
open_locale topological_space classical filter uniformity 

section picard_operator

-- NOTE: This is meant to be [a, b].
parameters {A : Type*} [nonempty A] [topological_space A] [measurable_space A] 
                       [linear_order A]

parameter (μ : measure A)

-- NOTE: This is meant to be ℝ^n.
parameters {B : Type*} [normed_group B] [normed_space ℝ B] [measurable_space B]
                       [complete_space B] [second_countable_topology B] [borel_space B]
          

parameters (t0 : A) (x0 : B) (f : A → B → B)

local infixr ` →ᵇ `:25 := bounded_continuous_function

-- Picard operator as a function.
def P_raw (x : A →ᵇ B) : A → B := λ t, x0 + ∫ s in t0..t, (f s (x s)) ∂μ

lemma P_raw.continuous 
: ∀ (x : A →ᵇ B), continuous (P_raw x) :=
begin 
    intros x, rw continuous_iff_continuous_at,
    intros a, unfold continuous_at,
    sorry, 
    -- Perhaps just deduce this from Lipschitz.
end 

lemma P_raw.bounded 
: ∀ (x : A →ᵇ B), ∃ C, ∀ (s t : A), dist (P_raw x s) (P_raw x t) ≤ C := 
sorry

def P : (A →ᵇ B) → (A →ᵇ B) :=
λ x, ⟨P_raw x, ⟨P_raw.continuous x, P_raw.bounded x⟩⟩ 

@[simp] lemma P_fn (x : A →ᵇ B) (t : A) 
: P x t = x0 + ∫ s in t0..t, (f s (x s)) ∂μ := rfl

-- TODO: Move.
private lemma ennreal.continuous_at_of_real : ∀ x, continuous_at ennreal.of_real x := 
λ x, (continuous_iff_continuous_at.1 ennreal.continuous_of_real x)

private lemma ennreal.monotone_of_real : monotone ennreal.of_real :=
λ a b, ennreal.of_real_le_of_real

private lemma ennreal.of_real_supr 
{ι : Type*} [nonempty ι] (f : ι → ℝ) (hbdd : bdd_above (range f))
: ennreal.of_real (supr f) = supr (λ t, ennreal.of_real (f t)) := 
begin
    have hcts := ennreal.continuous_at_of_real (supr f),
    have hmono := ennreal.monotone_of_real,
    exact (map_csupr_of_continuous_at_of_monotone hcts hmono hbdd),
end 

open bounded_continuous_function

-- TODO: Move: conditionally_complete_lattice
private lemma le_csupr_iff.mpr
{α : Type*} {ι : Sort*} [conditionally_complete_lattice α] 
{s : ι → α} {a : α} (hs : bdd_above (range s)) (h : ∀ (b : α), (∀ (i : ι), s i ≤ b) → a ≤ b)
: a ≤ supr s := 
h (supr s) (λ i, le_csupr hs i)

-- TODO: Prove something of the form:
-- bdd_above (range (λ (t : A), dist (⇑(P x) t) (⇑(P y) t))).

lemma P.edist_eq_supr (x y : A →ᵇ B) 
: edist (P x) (P y) = supr (λ t, edist (P x t) (P y t)) :=
begin
    unfold edist, unfold metric_space.edist,
    let S := {C : ℝ | 0 ≤ C ∧ ∀ (x_1 : A), dist ((P x) x_1) ((P y) x_1) ≤ C},
    show ennreal.of_real (Inf S) = _,
    have hS : S.nonempty, 
    { use [supr (λ t, dist ((P x) t) ((P y) t))], split,
      { eapply le_csupr_iff.mpr,
        { sorry, },
        { intros b h,
          replace h := h (nonempty.some (by apply_instance)),
          exact (le_trans dist_nonneg h), }, },
      { apply le_csupr,
        { sorry, }, }, },
    have hSbdd : bdd_below S,
    { use 0, intros x hx, exact hx.1, },
    have h := map_cInf_of_continuous_at_of_monotone 
        (ennreal.continuous_at_of_real (Inf S)) ennreal.monotone_of_real hS hSbdd,
    rw h, -- Is this even useful?
    sorry,
end 

parameters (K : nnreal) (hK : K < 1)

-- TODO: Move.
private lemma norm_integral_le_integral_norm_Ioc_of_le
{α E : Type*} [linear_order α] [measurable_space α]
[measurable_space E] [normed_group E]
[second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E]
{a b : α} {f : α → E} {μ : measure α} (h : a ≤ b)
: ∥∫ x in a..b, f x ∂μ∥ ≤ ∫ x in a..b, ∥f x∥ ∂μ :=
begin 
    rw [integral_of_le h, integral_of_le h],
    have hle := @norm_integral_le_integral_norm_Ioc α E _ _ _ _ _ _ _ _ a b f μ,
    rw [integral_of_le h, max_eq_right h, min_eq_left h] at hle,
    exact hle,
end 

--private lemma interval_integral.integral_mono
s
lemma P.lipschitz_at_of_lipshitz 
(hf : ∀ s, lipschitz_with K (f s)) (t : A) (ht : t0 ≤ t) (x y : A →ᵇ B) 
(hx : interval_integrable (λ t, f t (x t)) μ t0 t) (hy : interval_integrable (λ t, f t (y t)) μ t0 t)
: edist (P x t) (P y t) ≤ ↑K * edist x y :=
begin 
    simp, unfold edist, unfold metric_space.edist,
    rw metric_space.edist_dist, cases K with K hK,
    rw ←ennreal.of_real_eq_coe_nnreal,
    rw ←ennreal.of_real_mul hK,
    apply ennreal.of_real_le_of_real,
    rw dist_eq_norm, 
    calc ∥x0 + ∫ s in t0..t, f s (x s) ∂μ - (x0 + ∫ s in t0..t, f s (y s) ∂μ)∥ 
        = ∥∫ s in t0..t, f s (x s) ∂μ - ∫ s in t0..t, f s (y s) ∂μ∥
        : by rw [sub_eq_add_neg, neg_add, add_comm x0, add_assoc, ←add_assoc x0, 
                 add_comm x0, neg_add_self, zero_add, ←sub_eq_add_neg]
    ... = ∥∫ s in t0..t, (f s (x s)) - (f s (y s)) ∂μ∥ 
        : by rw interval_integral.integral_sub hx hy
    ... ≤ ∫ s in t0..t, ∥(f s (x s)) - (f s (y s))∥ ∂μ
        : norm_integral_le_integral_norm_Ioc_of_le ht
    ... = ∫ s in t0..t, (dist (f s (x s)) (f s (y s))) ∂μ
        : by congr; ext; exact (dist_eq_norm _ _).symm
    ... ≤ ∫ s in t0..t, K * dist (x s) (y s) ∂μ
        : begin 
            have hxsys := λ s, hf s (x s) (y s),
            -- TODO: Factor this out. Argument about edist dist and le.
            have hrw : (λ s, dist (f s (x s)) (f s (y s))) ≤ (λ s, K * dist (x s) (y s)) := sorry,
            -- This follows from interval_integral.integral_mono.
            sorry
         end
         -- Then we use norm_integral_le_of_norm_le_const
         -- Bound it above by the supremum!
         -- Well have something like K * (t - t0) * s ≤ K * s 
         -- So we play with the t-t0 and K's and we should be good.
    ... ≤ K * Inf {C : ℝ | 0 ≤ C ∧ ∀ (x_1 : A), dist (x x_1) (y x_1) ≤ C} : sorry
end

lemma P.lipschitz_of_lipschitz (hf : ∀ s, lipschitz_with K (f s))
: lipschitz_with K P :=
begin 
    intros x y,
    calc edist (P x) (P y) 
        = supr (λ t, edist (P x t) (P y t)) : P.edist_eq_supr x y
    ... ≤ ↑K * edist x y : sorry --supr_le (λ t, P.lipschitz_at_of_lipshitz hf t x y),
end 

--lemma P.edist_lt_top : Π (x : A →ᵇ B), edist x (P x) < ⊥ := sorry

def P.efixed_point_of_lipschitz (hf : ∀ s, lipschitz_with K (f s)) : A →ᵇ B := 
contracting_with.efixed_point P ⟨hK, P.lipschitz_of_lipschitz hf⟩ sorry sorry

#check contracting_with.efixed_point P

end picard_operator
