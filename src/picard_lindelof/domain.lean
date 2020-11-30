import topology.bounded_continuous_function
import measure_theory.interval_integral

noncomputable theory
open nat metric real set measure_theory interval_integral topological_space filter
open_locale topological_space filter

section domain

def α : Type := subtype (Icc (-1 : ℝ) (1 : ℝ))

instance : has_zero α := ⟨⟨0, ⟨by linarith, by linarith⟩⟩⟩

instance : nonempty α := ⟨0⟩

instance : has_neg α := ⟨λ a, ⟨-a.1, ⟨neg_le_neg a.2.2, neg_le.1 a.2.1⟩⟩⟩

instance : linear_order α := by unfold α; apply_instance

instance : topological_space α := by unfold α; apply_instance

instance : measurable_space α := by unfold α; apply_instance

instance : metric_space α := by unfold α; apply_instance

instance : opens_measurable_space α := subtype.opens_measurable_space _

instance : order_closed_topology α := {
  is_closed_le' := begin 
    -- TODO: Same technique can be used to prove a general statement about subtypes.
    apply is_open_prod_iff.mpr, rintros a b hab,
    replace hab : ¬ a ≤ b := hab,
    replace hab := lt_of_not_ge hab,
    cases a with a hIa, cases b with b hIb, simp at hab, 
    obtain ⟨u, v, hu, hv, hbu, hav, h⟩ := order_separated hab,
    use [{x : α | x.1 ∈ v}, {x : α | x.1 ∈ u}],
    refine ⟨_, _, _, _, _⟩,
    { rw is_open_iff at hv ⊢, intros x hx,
      rcases (hv x.val hx) with ⟨ε, H, hε⟩,
      use [ε, H], intros y hy, exact (hε hy), },
    { rw is_open_iff at hu ⊢, intros x hx,
      rcases (hu x.val hx) with ⟨ε, H, hε⟩,
      use [ε, H], intros y hy, exact (hε hy), },
    { exact hav, },
    { exact hbu, },
    { rintros ⟨x, y⟩ hxy, cases hxy with hx hy,
      dsimp at hx hy, simp, exact (h y.val hy x.val hx), },
  end
}

-- TODO: Move
lemma bdd_below_Icc {a b : ℝ} : bdd_below (Icc a b) := ⟨a, λ _, and.left⟩

lemma α.compact_univ : is_compact (⊤ : set α) :=
begin
  erw compact_iff_compact_in_subtype, simp,
  rw compact_iff_closed_bounded, split,
  { exact is_closed_Icc, },
  { exact (bounded_iff_bdd_below_bdd_above.2 ⟨bdd_below_Icc, bdd_above_Icc⟩), },
end

instance : compact_space α := begin
  have hcompact := α.compact_univ,
  erw ←compact_iff_compact_univ at hcompact,
  exact compact_iff_compact_space.1 hcompact,
end

lemma dist_le_2 (a b : α) : dist a b ≤ 2 := begin
  obtain ⟨halb, haub⟩ := a.2, obtain ⟨hblb, hbub⟩ := b.2,
  erw [dist_eq_norm, norm_eq_abs], by_cases h : 0 ≤ a.val - b.val,
  { erw abs_of_nonneg h, linarith, },
  { erw abs_of_neg (lt_of_not_ge h), linarith, } 
end

instance : has_lift_t α ℝ := ⟨λ t, t.1⟩

-- Canonical measure. Hopefully not really needed.
def α.volume : measure α := begin 
  let v : measure ℝ := volume,
  let m : set α → ennreal := λ s, v.to_outer_measure.measure_of (coe '' s),
  apply measure.of_measurable (λ s _, m s),
  { dsimp [m], simp, },
  { dsimp [m], intros f hm hpw, 
    have h := v.m_Union, 
    let fα : ℕ → set ℝ := λ n, coe '' (f n),
    have hfαi : ∀ i, is_measurable (fα i),
    { intros i, apply is_measurable.subtype_image,
      { exact is_measurable_Icc, },
      { exact hm i, }, },
    have hfαpw : pairwise (disjoint on fα),
    { intros i j hij x hx, dsimp [fα] at hx,
      cases hx with hxi hxj, simp at hxi hxj,
      rcases hxi with ⟨xα, ⟨hxi, hxα⟩⟩,
      rcases hxj with ⟨xα', ⟨hxj, hxα'⟩⟩,
      have heq : xα = xα',
      { rw ←hxα' at hxα, exact subtype.eq hxα, },
      rw ←heq at hxj, exact (hpw i j hij ⟨hxi, hxj⟩), },
    replace h := h hfαi hfαpw, dsimp [fα, v] at h ⊢,
    erw ←h, simp [volume], 
    show (lebesgue_outer _ = lebesgue_outer _),
    congr, rw image_Union, },
end

instance : measure_space α := ⟨α.volume⟩

lemma α.coe_Ioc {a b : α} : coe '' (Ioc a b) = Ioc a.1 b.1 :=
begin
  dsimp [Ioc, set.image], ext x, split, 
  { rintros ⟨c, ⟨⟨hac, hcb⟩, hc⟩⟩, rw ←hc, exact ⟨hac, hcb⟩, },
  { rintros ⟨hax, hxb⟩, 
    have hlbx := le_of_lt (lt_of_le_of_lt a.2.1 hax),
    have hubx := le_trans hxb b.2.2,
    use [⟨x, ⟨hlbx, hubx⟩⟩, ⟨⟨hax, hxb⟩, rfl⟩], },
end 

@[simp] lemma α.volume_Ioc {a b : α} : volume (Ioc a b) = ennreal.of_real (b.1 - a.1) :=
begin 
  simp [volume, α.volume], rw measure.of_measurable_apply,
  { rw α.coe_Ioc, erw (lebesgue_outer_Ioc a.1 b.1), refl, },
  { exact is_measurable_Ioc, },
end 

lemma α.coe_Icc {a b : α} : coe '' (Icc a b) = Icc a.1 b.1 :=
begin
  dsimp [Ioc, set.image], ext x, split, 
  { rintros ⟨c, ⟨⟨hac, hcb⟩, hc⟩⟩, rw ←hc, exact ⟨hac, hcb⟩, },
  { rintros ⟨hax, hxb⟩, 
    have hlbx := le_trans a.2.1 hax,
    have hubx := le_trans hxb b.2.2,
    use [⟨x, ⟨hlbx, hubx⟩⟩, ⟨⟨hax, hxb⟩, rfl⟩], },
end 

@[simp] lemma α.volume_Icc {a b : α} : volume (Icc a b) = ennreal.of_real (b.1 - a.1) :=
begin 
  simp [volume, α.volume], rw measure.of_measurable_apply,
  { rw α.coe_Icc, erw (lebesgue_outer_Icc a.1 b.1), refl, },
  { exact is_measurable_Icc, },
end 

instance : finite_measure (volume : measure α) :=
begin 
  constructor, simp [volume, α.volume], rw measure.of_measurable_apply,
  { simp, erw (lebesgue_outer_Icc (-1 : ℝ) (1 : ℝ)), simp, },
  { simp, }
end 

end domain
