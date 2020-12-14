import data.real.basic 
import algebra.big_operators.intervals
import measure_theory.measurable_space
import topology.basic
import measure_theory.borel_space

noncomputable theory

open set topological_space finsupp real

open_locale big_operators classical

-- Following https://www.isa-afp.org/browser_info/current/AFP/Affine_Arithmetic/document.pdf.
section affine_arithmetic

structure affine_form (E : Type*) [normed_group E] [normed_space ℝ E] := 
(x₀ : E) (x : ℕ →₀ E)

namespace affine_form

/-- In order to evaluate noise symbols, we will use a function of type `noise`, which is simply 
`ℕ → [0,1]`. -/
def error_interval : set ℝ := Icc (-1) 1

def noise := ℕ → error_interval

variable (n : ℕ)

variables {E : Type*} [normed_field E] [normed_space ℝ E]

/-- Constant affine form. -/
def const (c : E) : affine_form E := ⟨c, 0⟩

instance : inhabited (affine_form E) := ⟨const 0⟩

/-- Degree of an affine form. -/
def degree (A : affine_form E) : ℕ := A.x.support.card

/-- Total deviation of an affine form. -/
def total_deviation (A : affine_form E) : ℝ := ∑ i in A.x.support, ∥A.x i∥

/--- Given valuation for noise symbols `ε` and affine form `A`, the value of `A` with `ε` is given
by the formula ⟦A, ε⟧ := x₀ + ∑ εᵢ * xᵢ. -/
def eval (ε : noise) (A : affine_form E) : E :=
A.x₀ + ∑ i in A.x.support, (ε i).val • (A.x i)

/-- The image over all possible noises gives a set, which is how we usually think of the affine form
`A`. It is computted as ⟦A⟧ := { ⟦A, ε⟧ | ε : ℕ → [-1, 1] }. -/
def set (A : affine_form E) : set E :=
set.image (λ ε, eval ε A) ⊤

section operations

/-- Update affine form, i.e. add a partial. -/
def update (A : affine_form E) (y : E) : affine_form E :=
⟨A.x₀, A.x + finsupp.single (degree A + 1) y⟩

/-- Negation of affine forms. -/
def neg (A : affine_form E) : affine_form E :=
⟨-A.x₀, -A.x⟩

instance : has_neg (affine_form E) := ⟨neg⟩ 

@[simp] lemma neg_centre (A : affine_form E) 
: (-A).x₀ = -A.x₀ := rfl

@[simp] lemma neg_partials (A : affine_form E) 
: (-A).x = -A.x := rfl

@[simp] lemma eval_neg_eq_neg_eval (ε : noise) (A : affine_form E) 
: eval ε (-A) = -(eval ε A) :=
by { simp [eval, neg_centre, neg_partials, finsupp.support_neg, neg_add], }

/-- Scaling of affine forms. -/
def smul (k : ℝ) (A : affine_form E) : affine_form E :=
⟨k • A.x₀, k • A.x⟩

instance : has_scalar ℝ (affine_form E) := ⟨smul⟩ 

@[simp] lemma smul_centre (k : ℝ) (A : affine_form E) 
: (k • A).x₀ = k • A.x₀ := rfl

@[simp] lemma smul_partials (k : ℝ) (A : affine_form E) 
: (k • A).x = k • A.x := rfl

-- TODO: Move (finsupp/basic).
lemma support_smul_nonzero {α M} {R} 
  [division_ring R] [add_comm_group M] [module R M] {b : R} (hb : b ≠ 0) {g : α →₀ M} 
  : (b • g).support = g.support :=
begin 
  ext x, split,
  { intros h, exact finsupp.support_smul h, },
  { intros h, simp only [smul_apply', mem_support_iff, ne.def] at *,
    intros hc, rw [smul_eq_zero] at hc, cases hc,
    { exact hb hc, }, { exact h hc, }, },
end 

@[simp] lemma eval_smul_eq_smul_eval (ε : noise) (k : ℝ) (hk : k ≠ 0) (A : affine_form E) 
: eval ε (k • A) = k • (eval ε A) :=
by { simp [eval, smul_centre, smul_partials, support_smul_nonzero hk, 
      smul_add, finset.smul_sum, smul_smul, mul_comm], }

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

/-- Multiplication of affine forms. -/
def mul (A₁ A₂ : affine_form E) : affine_form E :=
-- TODO: Does this calculation of the error work for ℝ^n?
let e := (∑ i in A₁.x.support, ∥A₁.x i∥) * (∑ i in A₂.x.support, ∥A₂.x i∥) in
update ⟨A₁.x₀ * A₂.x₀, (A₁.x₀ • A₁.x) + (A₂.x₀ • A₂.x)⟩ (e • 1)

end operations 

section real 

-- I prove that a real affine form is enclosed by the total deviation interval. 
theorem affine_form_enclosed (A : affine_form ℝ) 
: set A ⊆ Icc (A.x₀ - total_deviation A) (A.x₀ + total_deviation A) :=
begin 
  intros x hx, rcases hx with ⟨ε, ⟨hε, (hx : eval ε A = x)⟩⟩,
  simp only [←hx, eval, total_deviation, mem_Icc], split,
  { simp only [sub_eq_add_neg, ←finset.sum_neg_distrib], 
    apply add_le_add (le_refl _), apply finset.sum_le_sum, intros n hn,
    show _ ≤ _ * _,
    by_cases h : 0 < A.x n,
    { rw [neg_le, neg_mul_eq_neg_mul], refine le_trans _ (le_abs_self _),
      rw [mul_le_iff_le_one_left h, neg_le], exact (ε n).2.1, },
    { replace h := le_of_not_lt h, rw [neg_le, neg_mul_eq_mul_neg],
      refine le_trans _ (neg_le_abs_self _),
      rw mul_le_iff_le_one_left _,
      { exact (ε n).2.2, },
      { rw [lt_neg, neg_zero], exact lt_of_le_of_ne h (mem_support_iff.1 hn), }, }, },
  { apply add_le_add (le_refl _), apply finset.sum_le_sum, intros n hn,
    show _ * _ ≤ _,
    by_cases h : 0 < A.x n,
    { refine le_trans _ (le_abs_self _), rw mul_le_iff_le_one_left h, exact (ε n).2.2, },
    { replace h := le_of_not_lt h,
      refine le_trans _ (neg_le_abs_self _), 
      erw [←neg_neg (_ * _), neg_mul_eq_neg_mul, neg_mul_eq_mul_neg],
      rw mul_le_iff_le_one_left _,
      { rw neg_le, exact (ε n).2.1, },
      { rw [lt_neg, neg_zero], exact lt_of_le_of_ne h (mem_support_iff.1 hn), } }, }, 
end 

-- This is proved in picard_lindelof/interval_arithmetic.
lemma mem_Icc_iff_exists_affine_form (a b : ℝ) (h : a < b)
: ∀ x, x ∈ Icc a b ↔ 
  ∃ γ ∈ (Icc (-1 : ℝ) (1 : ℝ)), x = ((a + b) / 2) + γ * ((b - a) / 2) :=
begin 
  replace h := sub_pos.2 h,
  have h2 : 0 < (b - a) / 2 := div_pos h (by linarith),
  intros x, split, 
  { rintros ⟨hax, hxb⟩, 
    use [(2*x - a - b) / (b - a)], refine ⟨⟨_, _⟩, _⟩, 
      { simp [le_div_iff h], linarith, },
      { simp [div_le_iff h], linarith, },
      { simp [mul_comm, ←mul_div_assoc, mul_div_cancel_left _ (ne_of_gt h)], ring, }, },
  { rintros ⟨γ, ⟨hγlb, hγub⟩, hx⟩, rw hx, split,
    { apply le_add_of_sub_left_le, 
      refine le_trans _ ((mul_le_mul_right h2).2 hγlb),
      linarith, },
    { apply add_le_of_le_sub_left,
      refine le_trans ((mul_le_mul_right h2).2 hγub) _,
      linarith, }, },
end

-- Conversely, an interval is contained in an affine form. 
-- TODO: Integrate proof above.
theorem interval_affine (A : affine_form ℝ) (a b : ℝ) (h : a < b)
: Icc a b ⊆ set ⟨(a + b) / 2, single 0 ((b - a) / 2)⟩ :=
begin 
  intros x hx, 
  rcases ((mem_Icc_iff_exists_affine_form a b h x).1 hx) with ⟨γ, hγ, heq⟩,
  use (λ n, ⟨γ, hγ⟩), split, { trivial, }, simp [eval],
  have h2 : (b - a) / 2 ≠ 0 := ne_of_gt (div_pos (sub_pos.2 h) (by linarith)),
  rw [support_single_ne_zero h2, finset.sum_singleton, single_eq_same, heq],
end 

end real 

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
