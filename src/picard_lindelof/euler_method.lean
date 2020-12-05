import data.real.basic
import analysis.calculus.times_cont_diff

import picard_lindelof.picard_lindelof
import picard_lindelof.domain

noncomputable theory

open metric set asymptotics filter real measure_theory 
open interval_integral topological_space uniform_space

open_locale topological_space classical filter uniformity 

-- fun rk_eval :: "(nat⇒nat⇒real) ⇒ (nat⇒real) ⇒ (real×'a::real_vector ⇒ 'a) ⇒ real ⇒ real ⇒ 'a ⇒ nat ⇒ 'a" where
--   "rk_eval A c f t h x j =
--   f (t + h * c j, x + h *⇩R (∑l=1 ..< j. A j l *⇩R rk_eval A c f t h x l))"

-- primrec rk_eval_dynamic :: "(nat⇒nat⇒real) ⇒ (nat⇒real) ⇒ (real×'a::real_vector ⇒ 'a) ⇒ real ⇒ real ⇒ 'a ⇒ nat ⇒ (nat ⇒ 'a)" where
--   "rk_eval_dynamic A c f t h x 0 = (λi. 0)"
-- | "rk_eval_dynamic A c f t h x (Suc j) =
--   (let K = rk_eval_dynamic A c f t h x j in
--   K(Suc j:=f (t + h * c (Suc j), x + h *⇩R (∑l=1..j. A (Suc j) l *⇩R K l))))"

-- fun rk_eval_float :: "(nat⇒nat⇒float) ⇒ (nat⇒float) ⇒ (float×float ⇒ float) ⇒ float ⇒ float ⇒ float ⇒ nat ⇒ float" where
--   "rk_eval_float A c f t h x j =
--   f (t + h * c j, x + h * setsum (λl. A j l * rk_eval_float A c f t h x l) {1..< j})"

-- definition rk_increment where
--   "rk_increment f s A b c h t x = (∑j=1..s. b j *⇩R rk_eval A c f t h x j)"

-- definition rk_increment_float where
--   "rk_increment_float error f s A b c h t x =
--   float_down error (∑j=1..s. b j * rk_eval_float A c f t h x j)"

-- definition euler_increment where
--   "euler_increment f = rk_increment f 1 (λi j. 0) (λi. 1) (λi. 0)"

--   = (rk_eval (*0) (*0) f t h x 1)"

--   = f (t, x)"

-- definition euler where
--   "euler f = grid_function (discrete_evolution (euler_increment f))"

-- definition discrete_evolution
-- where "discrete_evolution incr t1 t0 x = x + (t1 - t0) *⇩R incr (t1 - t0) t0 x"

-- definition "consistent x t T B p incr ⟷
--   (∀h≥0. t + h ≤ T ⟶ dist (x (t + h)) (discrete_evolution incr (t + h) t (x t)) ≤ B * h ^ (p + 1))"

-- lemma euler_consistent_traj:
--   fixes t
--   assumes "B ≥ 0"
--   assumes "∀s∈{t..T}. (x has_vector_derivative f (s, x s)) (at s)"
--   assumes "∀s∈{t..T}. ((λs. f (s, x s)) has_vector_derivative f' s) (at s)"
--   assumes "∀s∈{t..T}. ¦f' s¦ ≤ 2 * B"
--   shows "consistent x t T B 1 (euler_increment f)"

-- lemma euler_lipschitz:
--   fixes x::"real ⇒ real"
--   assumes t: "t ∈ {t0..T}"
--   assumes lipschitz: "∀t∈{t0..T}. lipschitz D' (λx. f (t, x)) L"
--   shows "lipschitz D' (euler_increment f h t) L"

-- locale euler_consistent =
--   has_solution i +
--   ivp_on_interval i T +
--   global_lipschitz I D' f L + 
--   grid: grid_from t t0 +
--   bounded_derivative I D f B f' B'
--   for i::"real ivp" and t T D' L B f' B' +
--   fixes r
--   assumes lipschitz_area: "⋀t. t ∈ I ⟹ cball (solution t) ¦r¦ ⊆ D'"
-- begin

-- lemma euler_consistent_solution:
--   fixes t'
--   assumes t': "t' ∈ I"
--   shows "consistent solution t' T B' 1 (euler_increment f)"

section euler_method 

local infix ` →ᵇ `:25 := bounded_continuous_function 

-- NOTE: This is meant to be ℝ^n.
variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                      [normed_space ℝ E] [complete_space E] [second_countable_topology E]

def euler_step (f : ℝ → E → E) (x : ℝ →ᵇ E) (h : ℝ) (t : ℝ) : E := 
(x t) + h • (f t (x t))

lemma euler_step_consistent 
  (f : ℝ → E → E) (x : ℝ →ᵇ E) (h : ℝ) (t : ℝ)
  -- Initial value problem: x'(t) = f(t,x(t)).
  (hf : ∀ t, has_deriv_at x (f t (x t)) t)
  -- Assume the derivative is bounded.
  (C : nnreal) (hbdd : ∀ t, ∥f t (x t)∥ ≤ C)
  -- Assume it is Lipschitz on the second argument? 
  (K : nnreal) (hltz : ∀ s, lipschitz_with K (f s))
  : dist (f (t + h) (x (t + h))) (euler_step f x h t) ≤ C * h^2 / 2 :=
begin
  sorry, 
end 

noncomputable def euler.recursive (f : ℝ → E → E) (x : ℝ → E) (h : ℝ) (t : ℝ) : ℕ → E
| 0     := x t
| (n+1) := (euler.recursive n) + h • (f (t + h) (euler.recursive n))



end euler_method
