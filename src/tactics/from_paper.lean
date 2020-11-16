-- Example from the paper 'A Metaprogramming Framework for Formal Verification' p. 17

inductive myexp : Type
| Cnst (n : nat) : myexp
| Plus (e1 e2 : myexp) : myexp
| Mult (e1 e2 : myexp) : myexp

open myexp

def myeval : myexp → nat
| (Cnst n) := n
| (Plus e1 e2) := (myeval e1) + (myeval e2)
| (Mult e1 e2) := (myeval e1) + (myeval e2)

def mytimes (k : nat) : myexp → myexp
| (Cnst n) := Cnst (k * n)
| (Plus e1 e2) := Plus (mytimes e1) (mytimes e2)
| (Mult e1 e2) := Mult (mytimes e1) e2

def myreassoc : myexp → myexp
| (Cnst n) := (Cnst n)
| (Plus e1 e2) :=
    let e1' := myreassoc e1 in
    let e2' := myreassoc e2 in
    match e2' with
    | (Plus e21 e22) := Plus (Plus e1' e21) e22
    | _  := Plus e1' e2'
    end
| (Mult e1 e2) :=
    let e1' := myreassoc e1 in
    let e2' := myreassoc e2 in
    match e2' with
    | (Mult e21 e22) := Mult (Mult e1' e21) e22
    | _ := Mult e1' e2'
    end

namespace mytactics

open tactic

-- Defining rsimp.

meta def find : expr → list expr → tactic expr
| e [] := failed
| e (h :: hs) :=
do t ← infer_type h,
(unify e t >> return h) <|> find e hs

meta def assumption : tactic unit :=
do { 
    ctx ← local_context,
    t ← target,
    h ← find t ctx,
    exact h }
<|> fail "assumption tactic failed"

meta def size : expr → nat
| (expr.app f a) := size f + size a
| _ := 1

meta def choose (ccs : cc_state) (e : expr) : expr :=
ccs.fold_eqc e e $ λ (best_so_far curr : expr),
if size curr < size best_so_far then curr else best_so_far

meta def eblast : smt_tactic unit := sorry
--repeat (ematch; try close)

meta def collect_implied_eqs : tactic cc_state := sorry
--focus $ using_smt $ do
--add_lemmas_from_facts, eblast,
--(done; return cc_state.mk) <|> to_cc_state

meta def rsimp : tactic unit :=
do ccs ← collect_implied_eqs,
try $ simp_top_down $ λ t, do
let root := ccs.root t,
let t' := choose ccs root,
p ← ccs.eqv_proof t t',
return (t', p)

-- Defining nano_crush.

meta def try_list {α} (tac : α → tactic unit) : list α → tactic unit
| [] := failed
| (e::es) := (tac e >> done) <|> try_list es

meta def collect_inductive_hyps {α} : tactic (list α) := sorry

meta def collect_inductive_from_target {α} : tactic (list α) := sorry

meta def induct (tac : tactic unit) : tactic unit :=
collect_inductive_hyps >>= try_list (λ e, induction' e; tac)

meta def split (tac : tactic unit) : tactic unit :=
collect_inductive_from_target >>= try_list (λ e, cases e; tac)

meta def search (tac : tactic unit) : nat → tactic unit
| 0 := try tac >> done
| (d+1) := try tac >> (done <|> all_goals (split (search d)))

meta def mk_relevant_lemmas : tactic unit := sorry

meta def rsimp' : tactic unit := sorry

meta def nano_crush (depth : nat := 1) :=
do hs ← mk_relevant_lemmas, induct (search (rsimp' hs) depth)

end mytactics
