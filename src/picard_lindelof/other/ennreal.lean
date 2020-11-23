import topology.instances.real
import topology.instances.ennreal
import data.real.ennreal
import topology.algebra.ordered

open topological_space set real filter
open_locale topological_space classical filter

-- TODO: Move.
private lemma ennreal.continuous_at_of_real : ∀ x, continuous_at ennreal.of_real x := 
λ x, (continuous_iff_continuous_at.1 ennreal.continuous_of_real x)

private lemma ennreal.monotone_of_real : monotone ennreal.of_real :=
λ a b, ennreal.of_real_le_of_real

private lemma ennreal.of_real_supr 
{ι : Type*} [nonempty ι] (h : ι → ℝ) (hbdd : bdd_above (range h))
: ennreal.of_real (supr h) = supr (λ t, ennreal.of_real (h t)) := 
begin
    have hcts := ennreal.continuous_at_of_real (supr h),
    have hmono := ennreal.monotone_of_real,
    exact (map_csupr_of_continuous_at_of_monotone hcts hmono hbdd),
end 
