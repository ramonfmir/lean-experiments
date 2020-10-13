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

parameter (eval_term : LTL_term → ℝ)

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
| Const : ℝ → semi_diff
| Term : LTL_term → semi_diff
| Sub : semi_diff → semi_diff → semi_diff
| If : semi_diff → semi_diff → semi_diff → semi_diff → semi_diff
| Max : list semi_diff → semi_diff
| Min : list semi_diff → semi_diff
| SoftMax : ℝ → list semi_diff → semi_diff
| SoftMin : ℝ → list semi_diff → semi_diff

open semi_diff

--#print semi_diff.cases_on
--#print _nest_1_1.semi_diff.cases_on
--#print _nest_1_1._nest_1_1.semi_diff._mut_.rec

@[elab_as_eliminator] protected def cases_on' :
  Π (C : semi_diff → Sort*) (x : semi_diff),
    (Π (a : ℝ), C (Const a)) →
    (Π (a : LTL_term), C (Term a)) →
    (Π (a a_1 : semi_diff), C (a.Sub a_1)) →
    (Π (a a_1 a_2 a_3 : semi_diff), C (a.If a_1 a_2 a_3)) →
    (Π (a : list semi_diff), C (Max a)) →
    (Π (a : list semi_diff), C (Min a)) →
    (Π (a : ℝ) (a_1 : list semi_diff), C (SoftMax a a_1)) →
    (Π (a : ℝ) (a_1 : list semi_diff), C (SoftMin a a_1)) → C x :=
sorry

noncomputable def eval_semi_diff : semi_diff → ℝ 
| (Const c) := c
| (Term t) := eval_term t
| (Sub x1 x2) := (eval_semi_diff x1) - (eval_semi_diff x2)
| (If x1 x2 x3 x4) := 
    if (eval_semi_diff x1) = (eval_semi_diff x2) 
    then (eval_semi_diff x3) 
    else (eval_semi_diff x4) 
| (Max l) := 0
    match (list.maximum (list.map eval_semi_diff l)) with
    | none := 0 -- In practice list will never be empty.
    | some m := m 
    end 
| (Min l) := 
    match (list.minimum (list.map eval_semi_diff l)) with
    | none := 0 -- In practice list will never be empty.
    | some m := m 
    end 
| (SoftMax γ l) := γ * log((list.map (λ x, exp((eval_semi_diff x) / γ)) l).sum)
| (SoftMin γ l) := - γ * log((list.map (λ x, exp(- (eval_semi_diff x) / γ)) l).sum)

-- Factor used for inequalities
parameter (ζ : ℝ)

def LTL_LEQ.to_semi_diff : LTL_term → LTL_term → semi_diff :=
λ t1 t2, Max [Sub (Term t2) (Term t1), Const 0] -- Flipped from paper.

def LTL_NEQ.to_semi_diff : LTL_term → LTL_term → semi_diff :=
λ t1 t2, If (Term t1) (Term t2) (Const ζ) (Const 0) 

def semi_diff.land : ℝ → semi_diff → semi_diff → semi_diff :=
λ γ x1 x2, SoftMax γ [x1, x2]

def semi_diff.lor : ℝ → semi_diff → semi_diff → semi_diff :=
λ γ x1 x2, SoftMin γ [x1, x2]

def LTL_prop.to_semi_diff : LTL_prop → semi_diff :=
| (LT t1 t2) := semi_diff.land (LTL_LEQ.to_semi_diff t1 t2) (LTL_NEQ.to_semi_diff t1 t2)
| (LEQ t1 t2) := LTL_LEQ.to_semi_diff t1 t2
| (EQ t1 t2 ) := semi_diff.land (LTL_LEQ.to_semi_diff t1 t2) (LTL_LEQ.to_semi_diff t2 t2)
| (GEQ t1 t2) := LTL_LEQ.to_semi_diff t2 t1
| (GT t1 t2) := semi_diff.land (LTL_LEQ.to_semi_diff t2 t1) (LTL_NEQ.to_semi_diff t1 t2)
| (NEQ t1 t2) := LTL_NEQ.to_semi_diff t1 t2

def LTL_formula.to_semi_diff : LTL_formula → semi_diff := 
| (P p) := sorry 
| (And φ1 φ2) := sorry
| (Box φ) := sorry
| (Diamond φ) := sorry 
| (Next φ) := sorry 
| (Until φ1 φ2) := sorry 
| (Neg φ) := sorry 

end LTL
