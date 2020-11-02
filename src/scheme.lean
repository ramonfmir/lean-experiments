import algebraic_geometry.Spec
import algebraic_geometry.Scheme
import ring_theory.localization

--open classical
open topological_space
open category_theory
open Top
open opposite
open algebraic_geometry
open algebraic_geometry.Scheme

noncomputable theory

variable (R : CommRing)

-- ring_theory/ideal/basic
local attribute [instance] ideal.comap_is_prime

-- ring_theory/localizations
def at_prime_from_comap {R S : CommRing} (f : R →+* S) (P : ideal S) [hP : P.is_prime]:
localization.at_prime (ideal.comap f P) → localization.at_prime P :=
λ x, sorry

noncomputable
def Spec.of {R S : CommRing} (f : R ⟶ S) :
(Top.of ((Spec S).to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace)) ⟶
(Top.of ((Spec R).to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace)) :=
⟨prime_spectrum.comap f, prime_spectrum.comap_continuous f⟩

-- def Spec.of' {R S : CommRing} (f : R ⟶ S) :
-- (Top.of (prime_spectrum S)) ⟶
-- (Top.of (prime_spectrum R)) :=
-- ⟨prime_spectrum.comap f, prime_spectrum.comap_continuous f⟩

lemma opens.map.Spec.of
{R S : CommRing}
(f : R ⟶ S)
(X : (opens (prime_spectrum R))ᵒᵖ) :
(opens.map (Spec.of f)).op.obj X = op ((opens.comap (Spec.of f).2) (unop X)) :=
rfl

def Spec_hom_of_ring_hom
{R S : CommRing}
(f : R ⟶ S) :
((Spec S).to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace) ⟶
((Spec R).to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace) :=
{ base := Spec.of f,
  c := {
    app := λ X, {
      to_fun := λ a, begin
        rw presheaf.pushforward_obj_obj,
        rcases a with ⟨a, ha⟩,
        refine ⟨_, _⟩,
        { intros x,
          have hx : (Spec.of f).1 x.1 ∈ (unop X) := x.2,
          have h := a ⟨(prime_spectrum.comap f) x.1, hx⟩,
          dsimp only [structure_sheaf.localizations, prime_spectrum.comap] at *,
          dunfold prime_spectrum.as_ideal at *,
          simp at h,
          use (at_prime_from_comap f _ h), },
        { intros x,
          sorry, },
      end,
      map_one' := sorry,
      map_mul' := sorry,
      map_zero' := sorry,
      map_add' := sorry,
    },
    naturality' := sorry,
  } }

-- lemma is_locally_fraction_pred'
--   {U : opens (Spec.Top R)} (f : Π x : U, structure_sheaf.localizations R x) :
--   (structure_sheaf.is_locally_fraction R).to_prelocal_predicate.pred f =
--   ∀ x : U, ∃ (V) (m : x.1 ∈ V) (i : V ⟶ U),
--   ∃ (r s : R), ∀ y : V,
--   ¬ (s ∈ y.1.as_ideal) ∧
--     f (i y : U) * (localization.of _).to_map s = (localization.of _).to_map r :=
-- rfl

def Spec_functor : CommRing ⥤ Schemeᵒᵖ :=
{ obj := λ R, (op (Spec R)),
  map := λ R S f, has_hom.hom.op $
    { val := Spec_hom_of_ring_hom f,
      property := λ x, begin
        sorry,
      end,
    },
  map_id' := sorry,
  map_comp' := sorry,
}

-- noncomputable
-- def SpecF : CommRing ⥤ Schemeᵒᵖ :=
-- { obj := λ R, (op (Spec R)),
--   map := λ R S f, has_hom.hom.op $
--     { val :=
--         { base := Spec.of f,
--           c := {
--             app := λ X, {
--               to_fun := begin
--                 intros a,
--                 rw presheaf.pushforward_obj_obj,
--                 dsimp only [Scheme.to_LocallyRingedSpace] at *,
--                 dsimp only [Spec] at *,
--                 dsimp only [Spec.LocallyRingedSpace] at *,
--                 dsimp only [Spec.SheafedSpace] at *,
--                 dsimp only [structure_sheaf] at *,
--                 dsimp only [structure_presheaf_in_CommRing] at *,
--                 dsimp only [structure_sheaf_in_Type] at *,
--                 dsimp only [subsheaf_to_Types] at *,
                
--                 simp, --simp at a,
--                 rcases a with ⟨a, ha⟩,
--                 --have h : Π (x : ((opens.map (Spec.of f)).obj (unop X))), structure_sheaf.localizations S x,
--                 --{ sorry, },
--                 refine ⟨_,_⟩,
--                 { intros x,
--                   --have y : (prime_spectrum.comap f) ⁻¹' (unop X).1 := x.1,
--                 --   rcases x with ⟨x, hx⟩,
--                 --   have hx' : (prime_spectrum.comap f) x ∈ (unop X) := hx,
--                 --   have ha' := a ⟨prime_spectrum.comap f x, hx'⟩, 
--                 --   rw is_locally_fraction_pred' at ha,
--                 --   have hax := (ha ⟨prime_spectrum.comap f x, hx'⟩),
--                   --rcases hax with ⟨V, H⟩,
--                   --choose V h using hax,
--                   sorry, },
--                 { intros x,
--                   rcases x with ⟨x, hx⟩,
--                   have hx' : (prime_spectrum.comap f) x ∈ (unop X) := hx,
--                   have ha' := a ⟨prime_spectrum.comap f x, hx'⟩, 
--                   rw is_locally_fraction_pred' at ha,
--                   have hax := (ha ⟨prime_spectrum.comap f x, hx'⟩),
--                   --rcases hax with ⟨V, m, i, r, s, H⟩,
--                   sorry, }
--               end,
--               map_one' := sorry,
--               map_mul' := sorry,
--               map_zero' := sorry,
--               map_add' := sorry,
--             },
--             naturality' := sorry,
--           } },
--         property := λ x,
--           begin
--             sorry,
--           end },
--   map_id' := sorry,
--   map_comp' := sorry,
-- }