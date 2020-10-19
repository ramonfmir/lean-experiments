import algebraic_geometry.Spec
import ring_theory.localization

open topological_space
open category_theory
open Top
open opposite
open algebraic_geometry

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

#print opens.comap

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
sorry,
end

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

                --dsimp only [Scheme.to_LocallyRingedSpace] at *,
                --dsimp only [Spec] at *,
                --dsimp only [Spec.LocallyRingedSpace] at *,
                --dsimp only [Spec.SheafedSpace] at *,
                --dsimp only [structure_sheaf] at *,
                --dsimp only [structure_presheaf_in_CommRing] at *,
                --dsimp only [structure_sheaf_in_Type] at *,
                --dsimp only [subsheaf_to_Types] at *,
                --dsimp only [subpresheaf_to_Types] at *,
                --dsimp only [structure_sheaf.is_locally_fraction] at *,
                --dsimp only [structure_sheaf.is_fraction_prelocal] at *,
                --dsimp at *,
                apply subtype.map,
                sorry,
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