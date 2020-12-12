import data.real.basic 
import algebra.big_operators.intervals
import measure_theory.measurable_space
import topology.basic
import measure_theory.borel_space
import analysis.special_functions.exp_log 

noncomputable theory

open set topological_space finsupp real

open_locale big_operators classical

section affine_arithmetic

structure affine_form (E : Type*) [normed_group E] [normed_space ℝ E] := 
(x₀ : E) (x : ℕ →₀ E)

structure affine_form_with_error extends affine_form ℝ :=
(error : ℝ)

namespace affine_form

/-- In order to evaluate noise symbols, we will use a function of type `noise`, which is simply 
`ℕ → [0,1]`. -/
def error_interval : set ℝ := Icc (-1) 1

def noise := ℕ → error_interval

variable (n : ℕ)

variables {E : Type*} [normed_group E] [normed_space ℝ E]

/--- Given valuation for noise symbols `ε` and affine form `A`, the value of `A` with `ε` is given
by the formula ⟦A, ε⟧ := x₀ + ∑ εᵢ * xᵢ. -/
def eval (ε : noise) (A : affine_form E) : E :=
A.x₀ + ∑ i in A.x.support, (ε i).val • (A.x i)

/-- The image over all possible noises gives a set, which is how we usually think of the affine form
`A`. It is computted as ⟦A⟧ := { ⟦A, ε⟧ | ε : ℕ → [-1, 1] }. -/
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
  -- TODO: Lemma here about sums over unions?
  { symmetry, apply finset.sum_subset (finset.subset_union_left _ _),
    intros x hx hxns, simp [not_mem_support_iff.1 hxns], },
  { symmetry, apply finset.sum_subset (finset.subset_union_right _ _),
    intros x hx hxns, simp [not_mem_support_iff.1 hxns], },
end

@[simp] lemma eval_add_eq_add_eval (ε : noise) (A₁ A₂ : affine_form E) 
: eval ε (A₁ + A₂) = (eval ε A₁) + (eval ε A₂) :=
by { simp only [eval_add_eq_def], dsimp [eval], abel, }

/-- Addition of affine forms with error. -/
-- TODO: Move.
def log₂ (x : ℝ) := log x / log 2

-- TODO: This should happen over the dyadic rationals.
-- Or not, but prove a lemma that there exists a dyadic that casts to the computed real.
-- TODO: Move to dyadic.
-- Following https://www.isa-afp.org/browser_info/current/AFP/Affine_Arithmetic/document.pdf.
def round_down (p : ℤ) (r : ℝ) : ℝ := ⌊r * 2 ^ p⌋ * 2 ^ -p 

lemma round_down_zero (p : ℤ) : round_down p 0 = 0 := 
by simp [round_down]

def round_up (p : ℤ) (r : ℝ) : ℚ := ⌈r * 2 ^ p⌉ * 2 ^ -p 

-- TODO: This should be shorter.
lemma round_up_mono (p : ℤ) (x y : ℝ) (h : x ≤ y) 
: round_up p x ≤ round_up p y :=
begin 
  simp [round_up], refine (mul_le_mul_right _).2 _, 
  { simp, exact (fpow_pos_of_pos (by linarith) p), },
  { simp, apply ceil_mono, refine (mul_le_mul_right _).2 h,
    exact fpow_pos_of_pos (by linarith) p, },
end 

def truncate_down (p : ℕ) (r : ℝ) : ℝ := round_down (p - ⌊log₂ r⌋ - 1) r

lemma truncate_down_zero (p : ℕ) : truncate_down p 0 = 0 := 
by simp [truncate_down, round_down_zero]

def truncate_up (p : ℕ) (r : ℝ) : ℝ := round_up (p - ⌊log₂ r⌋ - 1) r

lemma truncate_up_mono (p : ℕ) (x y : ℝ) (h : x ≤ y)
: truncate_up p x ≤ truncate_up p x :=
by simp [truncate_up, round_up_mono]  

lemma truncate_up_ge (p : ℕ) (r : ℝ) : r ≤ truncate_up p r :=
begin 
  simp [truncate_up, round_up], sorry,
end 

-- Def trunc-bound-eucl (p. 152)
def truncate_with_error (p : ℕ) (r : ℝ) : ℝ × ℝ := 
let q := truncate_down p r, e := truncate_up p (abs (q - r)) in ⟨q, e⟩ 

lemma truncate_with_error_is_bound (p : ℕ) (r : ℝ) 
: ∃ e : ℝ, (truncate_with_error p r).1 = r + e ∧ abs e ≤ (truncate_with_error p r).2 :=
begin 
  use [truncate_down p r - r], split, 
  { ring, },
  { simp [truncate_with_error, truncate_up_ge], }
end 

lemma truncate_with_error_zero_fst (p : ℕ) 
: (prod.fst ∘ truncate_with_error p) 0 = 0 := 
by simp [truncate_with_error, truncate_down_zero] 

-- Def trunc-bound-pdevs (p. 152)
def truncate_partials_with_error (p : ℕ) (x : ℕ →₀ ℝ) : (ℕ →₀ ℝ) × ℝ :=
⟨map_range (prod.fst ∘ truncate_with_error p) (truncate_with_error_zero_fst p) x,
∑ i in x.support, abs ((truncate_with_error p (x i)).1 - (x i))⟩

-- Def add-aform' (p. 160)
def add_with_error (p : ℕ) (A₁ A₂ : affine_form_with_error) : affine_form_with_error :=
let z₀ := truncate_with_error p (A₁.x₀ + A₂.x₀),
    z  := truncate_partials_with_error p (A₁.x + A₂.x) in
{ x₀    := z₀.1, 
  x     := z.1, 
  error := z₀.2 + z.2 + abs A₁.error + abs A₂.error }

end operations 

-- THEOREM 5.
-- lemma add_aform'E:
--   fixes X Y::"real aform"
--   assumes e: "e ∈ UNIV → {- 1..1}"
--     and xn: "pdevs_apply (snd X) n = 0"
--     and yn: "pdevs_apply (snd Y) n = 0"
--   obtains err
--   where "aform_val e (add_aform X Y) = aform_val (e(n:=err)) (add_aform' p n X Y)" "err ∈ {-1 .. 1}"

-- theorem add_add' (ε : noise n) (A₁ A₂ : affine_form E n) 
-- : ∃ E : error_interval, 
--     eval n ε (add n A₁ A₂) = 
--     eval (n + 1) (noise.insert_left n ε E) (add' n A₁ A₂) := sorry

end affine_form

-- Skipping all to do with expressions.

end affine_arithmetic
