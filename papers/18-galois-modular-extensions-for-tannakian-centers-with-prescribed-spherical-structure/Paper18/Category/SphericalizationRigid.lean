import Paper18.Category.SphericalizationPivotal
import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# Rigidity and the tautological pivotal structure of pivotalization

All cups and caps are actual ambient morphisms. Their compatibility with the
chosen double-dual identifications is proved from preservation of exact pairings,
rather than included as new object data.
-/
noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- Canonical double dualization preserves the chosen evaluation literally,
under its canonical tensor and unit comparisons. -/
lemma doubleDual_evaluation_unit (X : C) :
    μ (doubleDualFunctor C) (dual C X) X ≫
      (doubleDualFunctor C).map (ε_ X (dual C X)) ≫ η (doubleDualFunctor C) =
        ε_ ((doubleDualFunctor C).obj X) (dual C ((doubleDualFunctor C).obj X)) := by
  rw [canonicalDoubleDual_tensor, ← assoc, doubleDual_evaluation]
  simp only [assoc, ← canonicalDoubleDual_unit, ε_η, comp_id]
  rfl

/-- The canonical dual comparison of canonical double dualization is the
identity on the triple dual. -/
lemma doubleDual_dualComparison_hom (X : C) :
    (dualComparison (doubleDualFunctor C) X).hom = 𝟙 (dual C ((doubleDualFunctor C).obj X)) := by
  apply pairing_hom_ext
    (inferInstanceAs (ExactPairing ((doubleDualFunctor C).obj X)
      (dual C ((doubleDualFunctor C).obj X))))
  rw [dualComparison_evaluation, doubleDual_evaluation_unit]
  dsimp only [doubleDualFunctor]
  simp only [id_whiskerRight, id_comp]

/-- Canonical double dualization also preserves the chosen coevaluation. -/
lemma doubleDual_coevaluation_unit (X : C) :
    ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map (η_ X (dual C X)) ≫
      δ (doubleDualFunctor C) X (dual C X) =
        η_ ((doubleDualFunctor C).obj X) (dual C ((doubleDualFunctor C).obj X)) := by
  have hc := dualComparison_coevaluation (doubleDualFunctor C) X
  rw [doubleDual_dualComparison_hom] at hc
  dsimp only [doubleDualFunctor] at hc ⊢
  simpa only [whiskerLeft_id, comp_id] using hc

/-- Isomorphic changes in an object and its inverse dual preserve evaluation. -/
lemma pivotalized_iso_evaluation {X Y : C} (e : X ≅ Y) :
    ((dualMapIso e).inv ⊗ₘ e.hom) ≫ ε_ Y (dual C Y) = ε_ X (dual C X) := by
  dsimp only [dualMapIso, dualMap]
  rw [tensorHom_def', assoc, rightAdjointMate_comp_evaluation]
  simp [← whiskerLeft_comp_assoc]

/-- The corresponding coevaluation identity. -/
lemma pivotalized_iso_coevaluation {X Y : C} (e : X ≅ Y) :
    η_ X (dual C X) ≫ (e.hom ⊗ₘ (dualMapIso e).inv) = η_ Y (dual C Y) := by
  dsimp only [dualMapIso, dualMap]
  rw [tensorHom_def', coevaluation_comp_rightAdjointMate_assoc]
  simp

namespace Pivotalized

/-- The right dual of `(X,phi)` uses the inverse right mate of `phi`. -/
def rightDualObj (X : Pivotalized C) : Pivotalized C where
  obj := dual C X.obj
  phi := (dualMapIso X.phi).symm

/-- The ambient evaluation is a morphism of pivotalized objects. -/
def rightEvaluation (X : Pivotalized C) : rightDualObj X ⊗ X ⟶ 𝟙_ (Pivotalized C) where
  hom := ε_ X.obj (dual C X.obj)
  comm := by
    change ε_ X.obj (dual C X.obj) ≫ ε (doubleDualFunctor C) =
      (((dualMapIso X.phi).inv ⊗ₘ X.phi.hom) ≫
        μ (doubleDualFunctor C) (dual C X.obj) X.obj) ≫
          (doubleDualFunctor C).map (ε_ X.obj (dual C X.obj))
    rw [assoc, canonicalDoubleDual_tensor, doubleDual_evaluation, ← assoc]
    have he := pivotalized_iso_evaluation X.phi
    dsimp only [doubleDualFunctor] at he
    rw [he, canonicalDoubleDual_unit]

/-- The ambient coevaluation is a morphism of pivotalized objects. -/
def rightCoevaluation (X : Pivotalized C) : 𝟙_ (Pivotalized C) ⟶ X ⊗ rightDualObj X where
  hom := η_ X.obj (dual C X.obj)
  comm := by
    change η_ X.obj (dual C X.obj) ≫
      ((X.phi.hom ⊗ₘ (dualMapIso X.phi).inv) ≫
        μ (doubleDualFunctor C) X.obj (dual C X.obj)) =
          ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map (η_ X.obj (dual C X.obj))
    rw [← assoc, pivotalized_iso_coevaluation]
    have hc := doubleDual_coevaluation_unit X.obj =≫
      μ (doubleDualFunctor C) X.obj (dual C X.obj)
    simpa only [assoc, δ_μ, comp_id] using hc.symm

/-- The actual cup and cap satisfy both snake identities. -/
def rightExactPairing (X : Pivotalized C) : ExactPairing X (rightDualObj X) := by
  letI : ExactPairing ((forget (C := C)).obj X)
      ((forget (C := C)).obj (rightDualObj X)) := by
    change ExactPairing X.obj (dual C X.obj)
    infer_instance
  apply exactPairingOfFaithful forget (rightEvaluation X) (rightCoevaluation X)
  · simp only [forget_δ, forget_ε]
    erw [id_comp, comp_id]
    rfl
  · simp only [forget_η, forget_μ]
    erw [id_comp, comp_id]
    rfl

/-- The category of pivotalized objects is right rigid. -/
instance rightRigidCategory : RightRigidCategory (Pivotalized C) where
  rightDual X := { rightDual := rightDualObj X, exact := rightExactPairing X }

@[simp] lemma dual_obj (X : Pivotalized C) : (dual (Pivotalized C) X).obj = dual C X.obj := rfl
@[simp] lemma evaluation_hom (X : Pivotalized C) :
    (ε_ X (dual (Pivotalized C) X)).hom = ε_ X.obj (dual C X.obj) := rfl
@[simp] lemma coevaluation_hom (X : Pivotalized C) :
    (η_ X (dual (Pivotalized C) X)).hom = η_ X.obj (dual C X.obj) := rfl

/-- Taking a chosen right mate commutes with the actual forgetful functor. -/
@[simp] lemma dualMap_hom {X Y : Pivotalized C} (f : X ⟶ Y) :
    (dualMap (Pivotalized C) f).hom = dualMap C f.hom := by
  apply pairing_hom_ext (inferInstanceAs (ExactPairing X.obj (dual C X.obj)))
  have he := rightAdjointMate_comp_evaluation f
  have hh := congrArg (fun a => a.hom) he
  simp only [comp_hom, whiskerRight_hom, whiskerLeft_hom, evaluation_hom] at hh
  exact hh.trans (rightAdjointMate_comp_evaluation f.hom).symm

@[simp] lemma doubleDual_map_hom {X Y : Pivotalized C} (f : X ⟶ Y) :
    ((doubleDualFunctor (Pivotalized C)).map f).hom =
      (doubleDualFunctor C).map f.hom := by
  dsimp only [doubleDualFunctor]
  rw [dualMap_hom, dualMap_hom]

@[simp] lemma associator_hom (X Y Z : Pivotalized C) :
    (α_ X Y Z).hom.hom = (α_ X.obj Y.obj Z.obj).hom := rfl
@[simp] lemma associator_inv (X Y Z : Pivotalized C) :
    (α_ X Y Z).inv.hom = (α_ X.obj Y.obj Z.obj).inv := rfl
@[simp] lemma leftUnitor_hom (X : Pivotalized C) :
    (λ_ X).hom.hom = (λ_ X.obj).hom := rfl
@[simp] lemma leftUnitor_inv (X : Pivotalized C) :
    (λ_ X).inv.hom = (λ_ X.obj).inv := rfl
@[simp] lemma rightUnitor_hom (X : Pivotalized C) :
    (ρ_ X).hom.hom = (ρ_ X.obj).hom := rfl
@[simp] lemma rightUnitor_inv (X : Pivotalized C) :
    (ρ_ X).inv.hom = (ρ_ X.obj).inv := rfl

@[simp] lemma tensorCoevaluation_hom (X Y : Pivotalized C) :
    (tensorCoevaluation (Pivotalized C) X Y).hom = tensorCoevaluation C X.obj Y.obj := by
  simp only [tensorCoevaluation, comp_hom, coevaluation_hom, whiskerLeft_hom,
    whiskerRight_hom, leftUnitor_inv, associator_hom, associator_inv, tensorObj_obj, dual_obj]

@[simp] lemma tensorEvaluation_hom (X Y : Pivotalized C) :
    (tensorEvaluation (Pivotalized C) X Y).hom = tensorEvaluation C X.obj Y.obj := by
  simp only [tensorEvaluation, comp_hom, evaluation_hom, whiskerLeft_hom,
    whiskerRight_hom, leftUnitor_hom, associator_hom, associator_inv, tensorObj_obj, dual_obj]

@[simp] lemma dualTensorTo_hom (X Y : Pivotalized C) :
    (dualTensorTo (Pivotalized C) X Y).hom = dualTensorTo C X.obj Y.obj := by
  simp only [dualTensorTo, comp_hom, tensorCoevaluation_hom, whiskerLeft_hom,
    whiskerRight_hom, rightUnitor_inv, leftUnitor_hom, associator_inv, evaluation_hom,
    tensorObj_obj, dual_obj]

@[simp] lemma dualTensorFrom_hom (X Y : Pivotalized C) :
    (dualTensorFrom (Pivotalized C) X Y).hom = dualTensorFrom C X.obj Y.obj := by
  simp only [dualTensorFrom, comp_hom, tensorEvaluation_hom, whiskerLeft_hom,
    whiskerRight_hom, rightUnitor_inv, leftUnitor_hom, associator_inv, coevaluation_hom,
    tensorObj_obj, dual_obj]

@[simp] lemma doubleDualTensorHom_hom (X Y : Pivotalized C) :
    (doubleDualTensorHom (Pivotalized C) X Y).hom = doubleDualTensorHom C X.obj Y.obj := by
  simp only [doubleDualTensorHom, comp_hom, dualTensorFrom_hom, dualMap_hom,
    dualTensorTo_hom, dual_obj]

@[simp] lemma dualUnitTo_hom :
    (dualUnitTo (Pivotalized C)).hom = dualUnitTo C := by
  simp only [dualUnitTo, comp_hom, rightUnitor_inv, evaluation_hom, tensorUnit_obj, dual_obj]

@[simp] lemma dualUnitFrom_hom :
    (dualUnitFrom (Pivotalized C)).hom = dualUnitFrom C := by
  simp only [dualUnitFrom, comp_hom, leftUnitor_hom, coevaluation_hom, tensorUnit_obj, dual_obj]

@[simp] lemma doubleDualUnitHom_hom :
    (doubleDualUnitHom (Pivotalized C)).hom = doubleDualUnitHom C := by
  simp only [doubleDualUnitHom, comp_hom, dualUnitFrom_hom, dualMap_hom, dualUnitTo_hom]

/-- The chosen identification of a pivotalized object is itself an
isomorphism of pivotalized objects to its actual double dual. -/
def tautologicalIso (X : Pivotalized C) : X ≅ (doubleDualFunctor (Pivotalized C)).obj X :=
  mkIso X.phi (by
    change X.phi.hom ≫ dualMap C (dualMap C X.phi.hom) =
      X.phi.hom ≫ (doubleDualFunctor C).map X.phi.hom
    rfl)

/-- Naturality of the tautological identification is precisely the defining
commutation relation on actual morphisms. -/
def tautologicalNatIso : 𝟭 (Pivotalized C) ≅ doubleDualFunctor (Pivotalized C) :=
  NatIso.ofComponents tautologicalIso (fun f => by
    apply Hom.ext
    change f.hom ≫ _ = _ ≫ ((doubleDualFunctor (Pivotalized C)).map f).hom
    rw [doubleDual_map_hom]
    exact f.comm)

/-- The tautological coherent pivotal structure is derived on pivotalization;
no pivotal structure on the original category is required. -/
def pivotalStructure : PivotalStructure (Pivotalized C) where
  j := tautologicalNatIso
  unit := by
    apply Hom.ext
    change ε (doubleDualFunctor C) = (doubleDualUnitHom (Pivotalized C)).hom
    rw [doubleDualUnitHom_hom, canonicalDoubleDual_unit]
  tensor X Y := by
    apply Hom.ext
    change (X.phi.hom ⊗ₘ Y.phi.hom) ≫ μ (doubleDualFunctor C) X.obj Y.obj =
      (X.phi.hom ⊗ₘ Y.phi.hom) ≫ (doubleDualTensorHom (Pivotalized C) X Y).hom
    rw [doubleDualTensorHom_hom, canonicalDoubleDual_tensor]

@[simp] lemma pivotalStructure_component_hom (X : Pivotalized C) :
    ((pivotalStructure (C := C)).j.hom.app X).hom = X.phi.hom := rfl

@[simp] lemma pivotalStructure_component_inv (X : Pivotalized C) :
    ((pivotalStructure (C := C)).j.inv.app X).hom = X.phi.inv := rfl

/-- The right pivotal trace in pivotalization is the actual cap/cup trace
using the object's chosen double-dual identification. -/
lemma rightTrace_hom (X : Pivotalized C) (f : X ⟶ X) :
    ((pivotalStructure (C := C)).rightTrace f).hom =
      η_ X.obj (dual C X.obj) ≫ f.hom ▷ dual C X.obj ≫
        X.phi.hom ▷ dual C X.obj ≫ ε_ (dual C X.obj) (dual C (dual C X.obj)) := by
  simp only [PivotalStructure.rightTrace, PivotalStructure.leftEvaluation,
    comp_hom, coevaluation_hom, whiskerRight_hom, pivotalStructure_component_hom,
    evaluation_hom, dual_obj]

/-- The actual left pivotal trace uses the inverse chosen identification. -/
lemma leftTrace_hom (X : Pivotalized C) (f : X ⟶ X) :
    ((pivotalStructure (C := C)).leftTrace f).hom =
      η_ (dual C X.obj) (dual C (dual C X.obj)) ≫
        dual C X.obj ◁ X.phi.inv ≫ dual C X.obj ◁ f.hom ≫ ε_ X.obj (dual C X.obj) := by
  simp only [PivotalStructure.leftTrace, PivotalStructure.leftCoevaluation,
    comp_hom, coevaluation_hom, whiskerLeft_hom, evaluation_hom, dual_obj,
    pivotalStructure_component_inv, assoc]

end Pivotalized
end Paper18.Category
