import data.real.basic 
import algebra.big_operators.intervals
import measure_theory.measurable_space
import topology.basic
import measure_theory.borel_space
import analysis.special_functions.exp_log 

import ODE_enclosures.affine_arithmetic
import ODE_enclosures.float

noncomputable theory

open set topological_space finsupp real

open_locale big_operators classical

-- Following https://www.isa-afp.org/browser_info/current/AFP/Affine_Arithmetic/document.pdf.
section affine_arithmetic_with_error

structure affine_form_with_error extends affine_form ℝ :=
(error : ℝ)

namespace affine_form_with_error 

variable (n : ℕ)

variables {E : Type*} [normed_group E] [normed_space ℝ E]

section operations 

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

end affine_form_with_error

end affine_arithmetic_with_error
