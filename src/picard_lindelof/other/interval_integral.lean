import measure_theory.interval_integral
import measure_theory.integration
import topology.basic

open set measure_theory topological_space interval_integral

-- TODO: Move.
lemma temp.norm_integral_le_integral_norm_Ioc_of_le
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

variables {E : Type*}
    [normed_group E] [normed_space ℝ E] [second_countable_topology E] 
    [measurable_space E] [linear_order E] [complete_space E] [borel_space E]

lemma interval_integral.norm_integral_le_of_norm_le_const' 
    {a b C : ℝ} (hab : a ≤ b) {f : ℝ → E}
    (h : ∀ x ∈ Ioc a b, ∥f x∥ ≤ C) :
    ∥∫ x in a..b, f x∥ ≤ C * abs (b - a) :=
begin
    apply interval_integral.norm_integral_le_of_norm_le_const,
    rw [min_eq_left hab, max_eq_right hab], exact h,
end
