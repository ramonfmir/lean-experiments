import data.mv_polynomial
import data.real.basic
import analysis.calculus.times_cont_diff

namespace mv_taylor_models

variable (n : ℕ)

structure taylor_model :=
(p : mv_polynomial (fin n) ℝ)
(I : ℝ × ℝ)
(hI : I.fst < I.snd)

local notation `ℝ^n` := fin n → ℝ

open mv_polynomial

def is_taylor_model_at 
(tm : taylor_model n) (f : ℝ^n → ℝ) (x₀ : ℝ^n) (hf : times_cont_diff_at ℝ n f x₀) : Prop :=
∀ x : ℝ^n, (eval (x - x₀) tm.p) + tm.I.fst ≤ f x ∧ f x ≤ (eval (x - x₀) tm.p) + tm.I.snd

section operations

noncomputable def add (tm₁ tm₂ : taylor_model n) : taylor_model n := 
{ p := tm₁.p + tm₂.p,
  I := (min tm₁.I.fst tm₂.I.fst, max tm₁.I.snd tm₂.I.snd),
  hI := sorry, }

end operations

end mv_taylor_models
