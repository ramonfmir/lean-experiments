import data.real.basic
import analysis.calculus.times_cont_diff
import topology.bounded_continuous_function
import measure_theory.interval_integral
import topology.metric_space.basic

import ODE_enclosures.taylors_theorem

noncomputable theory

open metric set asymptotics filter real measure_theory 
open interval_integral topological_space uniform_space

open_locale topological_space classical filter uniformity 

section euler_method 

local infix ` →ᵇ `:25 := bounded_continuous_function 

variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E] [linear_order E]
                      [normed_space ℝ E] [complete_space E] [second_countable_topology E]

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

def euler_step (f : ℝ → E → E) (x : ℝ →ᵇ E) (h : ℝ) (t : ℝ) : E := 
(x t) + h • (f t (x t))

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

-- THEOREM 4 
-- lemma euler_consistent_solution:
--   fixes t'
--   assumes t': "t' ∈ I"
--   shows "consistent solution t' T B' 1 (euler_increment f)"

-- MISSING: Taylor's formula.

lemma euler_step_consistent 
  -- Should be 
  --    (f : ℝ → E → E) (x : ℝ →ᵇ E) (h : ℝ) (t : ℝ)
  -- but my statement of Taylor's formula is on fns ℝ → ℝ.
  (f : ℝ → ℝ → ℝ) (x : ℝ →ᵇ ℝ) (h : ℝ) (hpos : 0 < h) (t : ℝ)
  -- Initial value problem: x'(t) = f(t,x(t)).
  (hdiff : ∀ t, times_cont_diff_at ℝ 2 x t)
  (hf : ∀ t, has_deriv_at x (f t (x t)) t)
  -- Assume the derivative (of f) is bounded.
  (C : nnreal) (hbdd : ∀ s, ∥deriv (λ t, f t (x t)) s∥ ≤ C)
  -- Assume it is Lipschitz on the second argument? 
  (K : nnreal) (hltz : ∀ s, lipschitz_with K (f s))
  : dist (f (t + h) (x (t + h))) (euler_step f x h t) ≤ C * h^2 / 2 :=
begin
  have h := taylor_left x.1 t 1 (hdiff t) (t + h) ((lt_add_iff_pos_right t).2 hpos),
  rcases h with ⟨c, hc1, hc2, h⟩,
  -- Proof follows from here.
  sorry,
end 

-- Consistency implies convergence of:
noncomputable def euler.recursive (f : ℝ → E → E) (x : ℝ → E) (h : ℝ) (t : ℝ) : ℕ → E
| 0     := x t
| (n+1) := (euler.recursive n) + h • (f (t + h) (euler.recursive n))

end euler_method
