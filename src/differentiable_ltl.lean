-- The paper 'Elaborating on Learned Demonstrations with Temporal Logic 
-- Specifications' (https://arxiv.org/pdf/2002.00784.pdf) was presented today
-- 08/10/2020 at the IPAB workshop and there was a question about whether the
-- translation function preserves logical equivalences. I thought Lean would 
-- give us the answer.

import data.real.basic
import data.list.min_max
import data.complex.exponential
import analysis.complex.basic
import analysis.special_functions.exp_log

noncomputable theory

open real classical

section LTL

inductive LTL_term : Type
-- For the purpose of this proof, terms are just symbols indexed by nat.
| Term : nat → LTL_term 

-- Evaluate term t_i at time t.
parameter (eval_term : LTL_term → ℕ → ℝ)

inductive LTL_prop : Type
| LT : LTL_term → LTL_term → LTL_prop
| LEQ : LTL_term → LTL_term → LTL_prop
| EQ : LTL_term → LTL_term → LTL_prop
| GEQ : LTL_term → LTL_term → LTL_prop
| GT : LTL_term → LTL_term → LTL_prop
| NEQ : LTL_term → LTL_term → LTL_prop

open LTL_prop

def eval_prop : LTL_prop → Prop
| (LT t1 t2) := (eval_term t1) < (eval_term t2)
| (LEQ t1 t2) := (eval_term t1) <= (eval_term t2)
| (EQ t1 t2 ) := (eval_term t1) = (eval_term t2)
| (GEQ t1 t2) := (eval_term t1) >= (eval_term t2)
| (GT t1 t2) := (eval_term t1) > (eval_term t2)
| (NEQ t1 t2) := (eval_term t1) ≠ (eval_term t2)

inductive LTL_formula : Type
| P : LTL_prop → LTL_formula 
| Neg : LTL_formula → LTL_formula
| And : LTL_formula → LTL_formula → LTL_formula
| Box : LTL_formula → LTL_formula
| Diamond : LTL_formula → LTL_formula
| Next : LTL_formula → LTL_formula
| Until : LTL_formula → LTL_formula → LTL_formula

open LTL_formula

def eval_formula : ℕ → LTL_formula → Prop
| i (P p) := eval_prop p 
| i (Neg φ) := ¬ (eval_formula i φ)
| i (And φ1 φ2) := (eval_formula i φ1) ∧ (eval_formula i φ2)
| i (Box φ) := ∀ j >= i, (eval_formula j φ)
| i (Diamond φ) := ∃ j >= i, (eval_formula j φ)
| i (Next φ) := eval_formula (i + 1) φ
| i (Until φ1 φ2) := 
    ∃ j >= i, (∀ k < j, (eval_formula k φ1)) ∧ (∀ k >= j, (eval_formula k φ2))

inductive semi_diff
| Val : ℝ → semi_diff
| SoftMax : ℝ → list ℝ → semi_diff
| SoftMin : ℝ → list ℝ → semi_diff

open semi_diff

def eval_semi_diff : semi_diff → ℝ 
| (Val c) := c
| (SoftMax γ l) := γ * log(list.sum (list.map (λ x, exp(x / γ)) l))
| (SoftMin γ l) := - γ * log(list.sum (list.map (λ x, exp(- x / γ)) l))

-- Factor used for inequalities
parameter (ζ : ℝ)

def LTL_LEQ.to_semi_diff (i : ℕ) : LTL_term → LTL_term → semi_diff :=
λ t1 t2, Val (max ((eval_term t1 i) - (eval_term t2 i)) 0) 

def LTL_NEQ.to_semi_diff (i : ℕ) : LTL_term → LTL_term → semi_diff :=
λ t1 t2, if (eval_term t1 i) = (eval_term t2 i) then (Val ζ) else (Val 0)

def semi_diff.land : ℝ → semi_diff → semi_diff → semi_diff :=
λ γ x1 x2, SoftMax γ [eval_semi_diff x1, eval_semi_diff x2]

def semi_diff.lor : ℝ → semi_diff → semi_diff → semi_diff :=
λ γ x1 x2, SoftMin γ [eval_semi_diff x1, eval_semi_diff x2]

def LTL_prop.to_semi_diff (i : ℕ) (γ : ℝ) : LTL_prop → semi_diff
| (LT t1 t2) := semi_diff.land γ (LTL_LEQ.to_semi_diff i t1 t2) (LTL_NEQ.to_semi_diff i t1 t2)
| (LEQ t1 t2) := LTL_LEQ.to_semi_diff i t1 t2
| (EQ t1 t2 ) := semi_diff.land γ (LTL_LEQ.to_semi_diff i t1 t2) (LTL_LEQ.to_semi_diff i t2 t2)
| (GEQ t1 t2) := LTL_LEQ.to_semi_diff i t2 t1
| (GT t1 t2) := semi_diff.land γ (LTL_LEQ.to_semi_diff i t2 t1) (LTL_NEQ.to_semi_diff i t1 t2)
| (NEQ t1 t2) := LTL_NEQ.to_semi_diff i t1 t2

-- Max time.
parameter (T : ℕ)

def LTL_formula.to_semi_diff (i : ℕ) (γ : ℝ) : LTL_formula → semi_diff := 
| (P p) := LTL_prop.to_semi_diff i γ p
| (And φ1 φ2) := semi_diff.land γ (LTL_formula.to_semi_diff i γ φ1) (LTL_formula.to_semi_diff i γ φ2)
| (Box φ) := SoftMax γ 
    (list.map (λ j, eval_semi_diff (LTL_formula.to_semi_diff (i + j) γ φ)) (list.range (T - i)))
| (Diamond φ) := SoftMin γ 
    (list.map (λ j, eval_semi_diff (LTL_formula.to_semi_diff (i + j) γ φ)) (list.range (T - i))) 
| (Next φ) := Val 0 
| (Until φ1 φ2) := Val 0 
| (Neg φ) := Val 0

end LTL
