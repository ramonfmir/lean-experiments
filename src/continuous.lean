-- To mathlib ?

import data.set.function
import data.equiv.basic
import topology.basic
import topology.constructions

#print continuous_equiv_fun_basis
#check function.uncurry
#check continuous
#print is_open_map.of_inverse
#print is_open_map.comp
#check preimage_equivalence
#print nhds_le_of_le

lemma continuous_uncurry {A B C : Type} [topological_space A] [topological_space B] [topological_space C] 
: continuous (@function.uncurry A B C) :=
begin
    intros s hs,
    apply is_open_iff_nhds.mpr,
    intros a ha,
    rw filter.le_principal_iff,
    change (function.uncurry a ∈ s) at ha,
    sorry,
end

lemma continuous_uncurry_apply {A B C : Type} [topological_space A] [topological_space B] [topological_space C]
(f : A → B → C) (hf : continuous f) : continuous (function.uncurry f) :=
begin
  intros s1 hs1,
  let s2 : set (B → C) := { h : B → C | ∀ b, h b ∈ s1 },
  have hs2 : is_open s2,
  { sorry, },
  sorry,
end

#check continuous_iff_continuous_at
#print continuous_at 
#print filter.tendsto 
#print continuous_infi_dom
#check continuous_iff_coinduced_le
#print topological_space.coinduced

lemma continuous_flip {A B C: Type} [topological_space A] [topological_space B] [topological_space C]
(f : A → B → C) (hf : continuous f) : continuous (flip f) :=
begin
  --rw continuous_iff_continuous_at,
  --replace hf := (continuous_iff_continuous_at.mp hf),
  --intros x s hs,
  rw continuous_iff_coinduced_le,
  rw continuous_iff_coinduced_le at hf,
  intros x hx,
  sorry,
end
