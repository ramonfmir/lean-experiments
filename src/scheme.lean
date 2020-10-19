import algebraic_geometry.Spec
import algebraic_geometry.Scheme
import ring_theory.localization

open classical
open topological_space
open category_theory
open Top
open opposite
open algebraic_geometry
open algebraic_geometry.Scheme

noncomputable theory

--set_option pp.all true
--set_option pp.notation false

#check prelocal_predicate.sheafify
#check prelocal_predicate.sheafify_of
#check sheaf.no_confusion_type
#print opens.map
#check opens
#check op_op_map
#print Top.of
#check op_unop
#check prelocal_predicate.sheafify
#check subtype.map
#print local_predicate

variable (R : CommRing)

#check structure_sheaf.is_fraction
#check op_op_obj

set_option pp.proofs true
set_option pp.coercions false

noncomputable
def Spec.of {R S : CommRing} (f : R ⟶ S) :
(Top.of ((Spec S).to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace)) ⟶
(Top.of ((Spec R).to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace)) :=
⟨prime_spectrum.comap f, prime_spectrum.comap_continuous f⟩

def Spec.of' {R S : CommRing} (f : R ⟶ S) :
(Top.of (prime_spectrum S)) ⟶
(Top.of (prime_spectrum R)) :=
⟨prime_spectrum.comap f, prime_spectrum.comap_continuous f⟩

#print opens.map_obj

lemma opens.map.Spec.of'
{R S : CommRing}
(f : R ⟶ S)
(X : (opens (prime_spectrum R))ᵒᵖ) :
(opens.map (Spec.of' f)).op.obj X = op ((opens.comap (Spec.of' f).2) (unop X)) :=
rfl

def function_I_need
{R S : CommRing}
(f : R ⟶ S)
(X : (opens ((Spec R).to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ) :
((Spec R).to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.presheaf.obj X) →
((Spec S).to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.presheaf.obj ((opens.map (Spec.of' f)).op.obj X)) :=
begin
intros a,
erw opens.map.Spec.of',
have g := prime_spectrum.comap f,
sorry,
end

lemma is_locally_fraction_pred'
  {U : opens (Spec.Top R)} (f : Π x : U, structure_sheaf.localizations R x) :
  (structure_sheaf.is_locally_fraction R).to_prelocal_predicate.pred f =
  ∀ x : U, ∃ (V) (m : x.1 ∈ V) (i : V ⟶ U),
  ∃ (r s : R), ∀ y : V,
  ¬ (s ∈ y.1.as_ideal) ∧
    f (i y : U) * (localization.of _).to_map s = (localization.of _).to_map r :=
rfl

#print localization.of
#print preimage

noncomputable
def SpecF : CommRing ⥤ Schemeᵒᵖ :=
{ obj := λ R, (op (Spec R)),
  map := λ R S f, has_hom.hom.op $
    { val :=
        { base := Spec.of f,
          c := {
            app := λ X, {
              to_fun := begin
                intros a,
                rw presheaf.pushforward_obj_obj,
                dsimp only [Scheme.to_LocallyRingedSpace] at *,
                dsimp only [Spec] at *,
                dsimp only [Spec.LocallyRingedSpace] at *,
                dsimp only [Spec.SheafedSpace] at *,
                dsimp only [structure_sheaf] at *,
                dsimp only [structure_presheaf_in_CommRing] at *,
                dsimp only [structure_sheaf_in_Type] at *,
                dsimp only [subsheaf_to_Types] at *,
                
                simp, --simp at a,
                rcases a with ⟨a, ha⟩,
                --have h : Π (x : ((opens.map (Spec.of f)).obj (unop X))), structure_sheaf.localizations S x,
                --{ sorry, },
                refine ⟨_,_⟩,
                { intros x,
                  --have y : (prime_spectrum.comap f) ⁻¹' (unop X).1 := x.1,
                --   rcases x with ⟨x, hx⟩,
                --   have hx' : (prime_spectrum.comap f) x ∈ (unop X) := hx,
                --   have ha' := a ⟨prime_spectrum.comap f x, hx'⟩, 
                --   rw is_locally_fraction_pred' at ha,
                --   have hax := (ha ⟨prime_spectrum.comap f x, hx'⟩),
                  --rcases hax with ⟨V, H⟩,
                  --choose V h using hax,
                  sorry, },
                { intros x,
                  rcases x with ⟨x, hx⟩,
                  have hx' : (prime_spectrum.comap f) x ∈ (unop X) := hx,
                  have ha' := a ⟨prime_spectrum.comap f x, hx'⟩, 
                  rw is_locally_fraction_pred' at ha,
                  have hax := (ha ⟨prime_spectrum.comap f x, hx'⟩),
                  --rcases hax with ⟨V, m, i, r, s, H⟩,
                  sorry, }
              end,
              map_one' := sorry,
              map_mul' := sorry,
              map_zero' := sorry,
              map_add' := sorry,
            },
            naturality' := sorry,
          } },
        property := λ x,
          begin
            sorry,
          end },
  map_id' := sorry,
  map_comp' := sorry,
}