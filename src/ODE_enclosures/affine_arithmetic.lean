import data.real.basic 
import algebra.big_operators.intervals
import measure_theory.measurable_space
import topology.basic
import measure_theory.borel_space

noncomputable theory

open set topological_space finsupp

open_locale big_operators classical

section affine_arithmetic

structure affine_form (E : Type*) [normed_group E] [normed_space ℝ E] := 
(x₀ : E) (x : ℕ →₀ E)

structure affine_form_with_error extends affine_form ℝ :=
(error : ℝ)

namespace affine_form

/-- In order to evaluate noise symbols, we will use a function of type `noise`. -/
def error_interval : set ℝ := Icc (-1) 1

def noise := ℕ → error_interval

variable (n : ℕ)

variables {E : Type*} [normed_group E] [normed_space ℝ E]

/--- Given valuation for noise symbols `ε` and affine form `A`, the value of `A` with `ε` is given
by the formula ⟦A, ε⟧ := x₀ + ∑ εᵢ * xᵢ. -/
def eval (ε : noise) (A : affine_form E) : E :=
A.x₀ + ∑ i in A.x.support, (ε i).val • (A.x i)

/-- The image over all possible noises gives a set, which is how we usually think of the affine 
form `A`. It is computted as ⟦A⟧ := { ⟦A, ε⟧ | ε : ℕ → [-1, 1] }. -/
def set (A : affine_form E) : set E :=
set.image (λ ε, eval ε A) ⊤

section operations

/-- Addition of affine forms. The lemma `eval_add_eq_add_eval` shows that it is defined 
correctly. -/
def add (A₁ A₂ : affine_form E) : affine_form E :=
⟨A₁.x₀ + A₂.x₀, A₁.x + A₂.x⟩

instance : has_add (affine_form E) := ⟨add⟩ 

@[simp] lemma add_centre (A₁ A₂ : affine_form E) 
: (A₁ + A₂).x₀ = A₁.x₀ + A₂.x₀ := rfl

@[simp] lemma add_partials (A₁ A₂ : affine_form E) 
: (A₁ + A₂).x = A₁.x + A₂.x := rfl

private lemma eval_add_eq_sum_union (ε : noise) (A₁ A₂ : affine_form E) 
: eval ε (A₁ + A₂) = 
  (A₁.x₀ + A₂.x₀) 
  + (∑ i in A₁.x.support ∪ A₂.x.support, ((ε i).val • (A₁.x i) + (ε i).val • (A₂.x i))) :=
begin  
  simp [eval, add_centre, add_partials],
  apply finset.sum_subset,
  { convert @finsupp.support_add ℕ E _ (A₁.x) (A₂.x), }, 
  { intros x hx hxns,
    simp [←smul_add, ←add_apply, not_mem_support_iff.1 hxns], }, 
end

private lemma eval_add_eq_def (ε : noise) (A₁ A₂ : affine_form E) 
: eval ε (A₁ + A₂) = 
  (A₁.x₀ + A₂.x₀) 
  + (∑ i in A₁.x.support, (ε i).val • (A₁.x i) 
  + ∑ i in A₂.x.support, (ε i).val • (A₂.x i)) :=
begin 
  simp [eval_add_eq_sum_union ε A₁ A₂, finset.sum_add_distrib], 
  apply congr_arg2 (+),
  -- Lemma here about sums over unions?
  { symmetry, apply finset.sum_subset (finset.subset_union_left _ _),
    intros x hx hxns, simp [not_mem_support_iff.1 hxns], },
  { symmetry, apply finset.sum_subset (finset.subset_union_right _ _),
    intros x hx hxns, simp [not_mem_support_iff.1 hxns], },
end

@[simp] lemma eval_add_eq_add_eval (ε : noise) (A₁ A₂ : affine_form E) 
: eval ε (A₁ + A₂) = (eval ε A₁) + (eval ε A₂) :=
by { simp only [eval_add_eq_def], dsimp [eval], abel, }

/-- Addition of affine forms with error. -/

end operations 

-- definition add_aform'::"nat ⇒ nat ⇒ 'a::executable_euclidean_space aform ⇒ 'a aform ⇒ 'a aform"
--   where "add_aform' p n x y =
--     (let
--       z0 = trunc_bound_eucl p (fst x + fst y);
--       z = trunc_bound_pdevs p (add_pdevs (snd x) (snd y))
--       in (fst z0, pdev_upd (fst z) n (listsum' p [snd z0, snd z])))"

-- TODO 1: Maybe create an instance for executable euclidean space.
-- TODO 2: Finish dyadic rationals. Prove a bunch of instances. 
-- def add' (A₁ A₂ : affine_form 𝔽 n) : affine_form 𝔽 (n + 1) := ... 

def add' (A₁ A₂ : affine_form E) : affine_form E := sorry

-- THEOREM 5.
-- lemma add_aform'E:
--   fixes X Y::"real aform"
--   assumes e: "e ∈ UNIV → {- 1..1}"
--     and xn: "pdevs_apply (snd X) n = 0"
--     and yn: "pdevs_apply (snd Y) n = 0"
--   obtains err
--   where "aform_val e (add_aform X Y) = aform_val (e(n:=err)) (add_aform' p n X Y)" "err ∈ {-1 .. 1}"

theorem add_add' (ε : noise n) (A₁ A₂ : affine_form E n) 
: ∃ E : error_interval, 
    eval n ε (add n A₁ A₂) = 
    eval (n + 1) (noise.insert_left n ε E) (add' n A₁ A₂) := sorry

end affine_form

-- Skipping all to do with expressions.

end affine_arithmetic
