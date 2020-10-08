-- The paper 'Elaborating on Learned Demonstrations with Temporal Logic 
-- Specifications' (https://arxiv.org/pdf/2002.00784.pdf) was presented today
-- 08/10/2020 at the IPAB workshop and there was a question about whether the
-- translation function preserves logical equivalences. I thought Lean would 
-- give us the answer.

import data.real.basic

section LTL

inductive LTL_term : Type
-- For the purpose of this proof, terms are just symbols indexed by nat.
| Term : nat → LTL_term 

parameter (eval_term : LTL_term → nat)

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
| i (Until φ1 φ2) := ∃ j >= i, (∀ k < j, (eval_formula k φ1)) ∧ (∀ k >= j, (eval_formula k φ2))

-- Factor used for inequalities
parameter (ζ : ℝ)

inductive diff_function
| soft_max : ℝ → list ℝ → diff_function
| soft_min : ℝ → list ℝ → diff_function

def LTL_prop.trans : LTL_formula → diff_function := sorry


end LTL
