import measure_theory.interval_integral
import measure_theory.integration
import topology.basic

open measure_theory topological_space interval_integral

-- TODO: Move.
private lemma interval_integral.norm_integral_le_integral_norm_Ioc_of_le
{α E : Type*} [linear_order α] [measurable_space α]
[measurable_space E] [normed_group E]
[second_countable_topology E] [complete_space E] [normed_space ℝ E] [borel_space E]
{a b : α} {f : α → E} {μ : measure α} (h : a ≤ b)
: ∥∫ x in a..b, f x ∂μ∥ ≤ ∫ x in a..b, ∥f x∥ ∂μ :=
begin 
    rw [integral_of_le h, integral_of_le h],
    have hle := @norm_integral_le_integral_norm_Ioc α E _ _ _ _ _ _ _ _ a b f μ,
    rw [integral_of_le h, max_eq_right h, min_eq_left h] at hle,
    exact hle,
end 

-- TODO: Move.
private lemma interval_integral.integral_mono 
{B : Type*} [normed_group B] [normed_space ℝ B] [second_countable_topology B] 
[measurable_space B] [linear_order B] [complete_space B] [borel_space B]
(μ : measure ℝ)
{f g : ℝ → B} (a b : ℝ)
(hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b) (h : f ≤ g)
: ∫ t in a..b, f a ∂μ ≤ ∫ t in a..b, g t ∂μ := sorry