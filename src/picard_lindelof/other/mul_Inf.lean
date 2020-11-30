import data.real.basic 

-- TODO: Move. 
lemma mul_Inf {K : ℝ} (hK : 0 ≤ K) {p : ℝ → Prop} 
(h : ∃ x, 0 ≤ x ∧ p x) (hp : p (Inf {x | 0 ≤ x ∧ p x}))
: K * Inf {x | 0 ≤ x ∧ p x} = Inf {y | ∃ x, (y : ℝ) = K * x ∧ 0 ≤ x ∧ p x} :=
begin 
  rcases h with ⟨i, hnni, hpi⟩,
  let S := {y | ∃ x, y = K * x ∧ 0 ≤ x ∧ p x},
  apply le_antisymm,
  { have h1 : (∃ (x : ℝ), x ∈ S) := ⟨K * i, ⟨i, rfl, hnni, hpi⟩⟩,
    have h2 : (∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → x ≤ y),
    { existsi (0 : ℝ), rintros y ⟨x, hy, hnnx, hpx⟩,
      rw hy, exact mul_nonneg hK hnnx, },
    rw real.le_Inf S h1 h2, rintros z ⟨w, hz, hnnw, hpw⟩,
    rw hz, mono,
    { refine cInf_le _ ⟨hnnw, hpw⟩, use 0, intros a ha, exact ha.1, },
    { apply le_cInf,
      { use [i, ⟨hnni, hpi⟩], },
      { intros b hb, exact hb.1, }, }, },
  { apply real.Inf_le,
    { use [0], intros y hy, rcases hy with ⟨x, ⟨hy, hnnx, hpx⟩⟩,
      rw hy, exact mul_nonneg hK hnnx, },
    { use [Inf {x : ℝ | 0 ≤ x ∧ p x}], refine ⟨rfl, _, _⟩, 
      { apply le_cInf,
        { use [i, ⟨hnni, hpi⟩], },
        { intros b hb, exact hb.1, }, },
      { exact hp, }, }, },
end
