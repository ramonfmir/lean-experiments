import data.real.basic 
import algebra.big_operators.intervals
import measure_theory.measurable_space
import topology.basic
import measure_theory.borel_space

noncomputable theory

open set topological_space finset

open_locale big_operators interval

section affine_arithmetic

-- type_synonym 'a aform = "'a × 'a pdevs"

structure affine_form (E : Type*) (n : ℕ) := 
(x₀ : E)
(x : fin n → E)

def error_interval : set ℝ := [-1, 1]

def noise (n : ℕ) : Type := fin n → error_interval

def noise.insert_left (n : ℕ) (ε : noise n) (E : error_interval) : noise (n + 1) :=
@fin.cases n (λ_, error_interval) E ε

namespace affine_form

variable (n : ℕ)

variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                      [normed_space ℝ E] [complete_space E] [second_countable_topology E]

-- definition aform_val :: "(nat ⇒ real) ⇒ 'a::real_normed_vector aform ⇒ 'a"
--   where "aform_val e X = fst X + pdevs_val e (snd X)"

def eval (ε : noise n) (A : affine_form E n) : E :=
A.x₀ + ∑ i, (ε i).val • (A.x i)

-- definition Affine ::
--     "'a::real_normed_vector aform ⇒ 'a set"
--   where "Affine X = valuate (λe. aform_val e X)"

def set (A : affine_form E n) : set E :=
set.image (λ ε, eval n ε A) ⊤

-- definition add_aform::"'a::real_vector aform ⇒ 'a aform ⇒ 'a aform"
--   where "add_aform x y = (fst x + fst y, add_pdevs (snd x) (snd y))"

def add (A₁ A₂ : affine_form E n) : affine_form E n :=
⟨A₁.x₀ + A₁.x₀, λ i, (A₁.x i) + (A₂.x i)⟩

-- definition add_aform'::"nat ⇒ nat ⇒ 'a::executable_euclidean_space aform ⇒ 'a aform ⇒ 'a aform"
--   where "add_aform' p n x y =
--     (let
--       z0 = trunc_bound_eucl p (fst x + fst y);
--       z = trunc_bound_pdevs p (add_pdevs (snd x) (snd y))
--       in (fst z0, pdev_upd (fst z) n (listsum' p [snd z0, snd z])))"

-- TODO 1: Maybe create an instance for executable euclidean space.
-- TODO 2: Finish dyadic rationals. Prove a bunch of instances. 
-- def add' (A₁ A₂ : affine_form 𝔽 n) : affine_form 𝔽 (n + 1) := ... 
def add' (A₁ A₂ : affine_form E n) : affine_form E (n + 1) := sorry

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
