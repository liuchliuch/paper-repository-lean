import Paper18.Category.RelativeTensorPivotalBasic
import Paper18.Category.RigidDoubleDual
import Paper18.Category.RadfordDualBraiding

/-! # Actual free-module dual comparisons against a multiplication pairing -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category.ModuleBalancing.MultiplicationPairing
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C] [HasCoequalizers C]
  {A : C} [MonObj A] [IsCommMonObj A] (P : MultiplicationPairing A)
  [RightRigidCategory (Mod_ C A)]
open RelativeTensor

omit [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A]
  [RightRigidCategory (Mod_ C A)] in
/-- Sliding a strand across an actual multiplication cap reverses the
crossing. The equation follows from ambient braiding naturality. -/
@[reassoc]
lemma multiplicationCap_slide (X : C) :
    (α_ A X A).hom ≫ (A ◁ (β_ X A).hom) ≫ (α_ A A X).inv ≫
        (@ExactPairing.evaluation C _ _ A A P.pairing) ▷ X ≫ (λ_ X).hom =
      (β_ X A).inv ▷ A ≫ (α_ X A A).hom ≫
        (X ◁ (@ExactPairing.evaluation C _ _ A A P.pairing)) ≫ (ρ_ X).hom := by
  apply (cancel_epi ((β_ X A).hom ▷ A)).mp
  simp only [← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, id_comp]
  calc
    _ = (α_ X A A).hom ≫ (β_ X (A ⊗ A)).hom ≫
        (@ExactPairing.evaluation C _ _ A A P.pairing) ▷ X ≫ (λ_ X).hom := by
      rw [braiding_tensor_right_hom]
      simp
    _ = _ := by
      rw [← braiding_naturality_right_assoc, braiding_tensorUnit_right]
      simp


/-- The canonical dual comparison of the actual strong free functor has
an explicit actual cap after forgetting. -/
lemma freeDualComparison_cap (X : C) :
    ((dualComparison (InternalModule.freeFunctor (A := A)) X).hom.hom ▷
        (InternalModule.free A X).X) ≫ P.ambientCap (InternalModule.free A X) =
      tensorFreeMap (InternalModule.free A (dual C X)) X ≫
        (α_ A (dual C X) X).hom ≫ (A ◁ ε_ X (dual C X)) ≫
        (ρ_ A).hom ≫ P.counit := by
  unfold ambientCap
  erw [← π_whiskerRight_assoc]
  have h := congrArg Mod_.Hom.hom
    (dualComparison_evaluation (InternalModule.freeFunctor (A := A)) X)
  simp only [Mod_.comp_hom'] at h
  erw [reassoc_of% h]
  rw [freeFunctor_μ_eq]
  change π (InternalModule.free A (dual C X)) (InternalModule.free A X) ≫
      (freeTensorIso (dual C X) X).hom.hom ≫
        (A ◁ ε_ X (dual C X)) ≫ (freeUnitIso (A := A)).inv.hom ≫ P.counit = _
  dsimp only [freeTensorIso, Iso.trans_hom, Mod_.comp_hom']
  simp only [assoc]
  erw [π_tensorFreeHom_assoc]
  rfl

omit [HasCoequalizers C] [RightRigidCategory (Mod_ C A)] in
/-- The same cap is the canonical tensor cap after the negative crossing
and the actual algebra-to-dual comparison. -/
lemma freeDualComparison_cap_formula (X : C) :
    tensorFreeMap (InternalModule.free A (dual C X)) X ≫
        (α_ A (dual C X) X).hom ≫ (A ◁ ε_ X (dual C X)) ≫
        (ρ_ A).hom ≫ P.counit =
      (((β_ (dual C X) A).inv ≫ (dual C X ◁ (P.algebraDualIso).hom)) ▷
        (A ⊗ X)) ≫ tensorEvaluation C A X := by
  rw [tensorEvaluation_eq]
  rw [comp_whiskerRight, assoc, tensorEval_map_leftDual,
    P.algebraDualIso_evaluation]
  unfold tensorFreeMap rightAction
  erw [braiding_tensor_left_hom]
  erw [InternalModule.free_smul]
  simp only [comp_whiskerRight, assoc, Iso.hom_inv_id_assoc]
  have hm : (β_ A A).hom ▷ (dual C X) ▷ X ≫ μ[A] ▷ (dual C X) ▷ X =
      μ[A] ▷ (dual C X) ▷ X := by
    rw [← comp_whiskerRight, ← comp_whiskerRight, IsCommMonObj.mul_comm]
  rw [reassoc_of% hm]
  have he : (α_ A (dual C X) X).hom ≫ (A ◁ ε_ X (dual C X)) ≫
      (ρ_ A).hom ≫ P.counit =
      P.counit ▷ (dual C X) ▷ X ≫ (λ_ (dual C X)).hom ▷ X ≫
        ε_ X (dual C X) := by
    rw [← rightUnitor_naturality, whisker_exchange_assoc,
      ← associator_naturality_left_assoc]
    monoidal
  calc
    _ = (α_ (A ⊗ dual C X) A X).inv ≫
        (α_ A (dual C X) A).hom ▷ X ≫
        (A ◁ (β_ (dual C X) A).hom) ▷ X ≫
        (α_ A A (dual C X)).inv ▷ X ≫
        (μ[A] ▷ (dual C X)) ▷ X ≫
        (α_ A (dual C X) X).hom ≫ (A ◁ ε_ X (dual C X)) ≫
        (ρ_ A).hom ≫ P.counit := by
      monoidal
    _ = (α_ (A ⊗ dual C X) A X).inv ≫
        ((α_ A (dual C X) A).hom ≫ (A ◁ (β_ (dual C X) A).hom) ≫
        (α_ A A (dual C X)).inv ≫
        (@ExactPairing.evaluation C _ _ A A P.pairing) ▷ (dual C X) ≫
        (λ_ (dual C X)).hom) ▷ X ≫ ε_ X (dual C X) := by
      rw [P.evaluation]
      simp only [comp_whiskerRight, assoc]
      rw [he]
    _ = _ := by
      rw [P.multiplicationCap_slide]
      dsimp only [tensorEval]
      monoidal

/-- Explicit ambient formula for the canonical free dual comparison. -/
lemma freeDualComparison_formula (X : C) :
    (dualComparison (InternalModule.freeFunctor (A := A)) X).hom.hom ≫
        (P.ambientDualIso (InternalModule.free A X)).hom ≫
        (dualTensorIso A X).hom =
      (β_ (dual C X) A).inv ≫ (dual C X ◁ (P.algebraDualIso).hom) := by
  apply pairing_hom_ext (tensorExactPairing A X)
  change _ ▷ (A ⊗ X) ≫ tensorEvaluation C A X =
    _ ▷ (A ⊗ X) ≫ tensorEvaluation C A X
  simp only [comp_whiskerRight, assoc]
  rw [dualTensorIso_evaluation]
  erw [P.ambientDualIso_evaluation]
  erw [P.freeDualComparison_cap]
  rw [P.freeDualComparison_cap_formula]
  simp only [comp_whiskerRight, assoc]

/-- The free object's actual ambient dual comparison. -/
def ambientFreeDualIso (X : C) : A ⊗ dual C X ≅ dual C (A ⊗ X) :=
  (β_ (dual C X) A).symm ≪≫ whiskerLeftIso (dual C X) P.algebraDualIso ≪≫
    (dualTensorIso A X).symm

omit [HasCoequalizers C] [RightRigidCategory (Mod_ C A)] in
lemma ambientFreeDualIso_pivotal (J : PivotalStructure C)
    (hA : (J.twistIso A).hom = 𝟙 A) (X : C) :
    J.j.hom.app (A ⊗ X) ≫ dualMap C (P.ambientFreeDualIso X).hom =
      (A ◁ J.j.hom.app X) ≫ (P.ambientFreeDualIso (dual C X)).hom := by
  have hn := dualTensorIso_naturality_right (dual C X) (P.algebraDualIso).hom
  have hb := dualTensorIso_braiding (dual C X) A
  have hni : (dualTensorIso (dual C X) (dual C A)).inv ≫
      dualMap C (dual C X ◁ (P.algebraDualIso).hom) =
      dualMap C (P.algebraDualIso).hom ▷ dual C (dual C X) ≫
        (dualTensorIso (dual C X) A).inv := by
    apply (cancel_mono (dualTensorIso (dual C X) A).hom).mp
    simp only [assoc, Iso.inv_hom_id, comp_id]
    rw [hn, Iso.inv_hom_id_assoc]
  have hbi : (dualTensorIso (dual C X) A).inv ≫
      dualMap C (β_ (dual C X) A).inv =
      (β_ (dual C (dual C X)) (dual C A)).inv ≫
        (dualTensorIso A (dual C X)).inv := by
    have hi : dualMapIso (β_ (dual C X) A) ≪≫ dualTensorIso (dual C X) A =
        dualTensorIso A (dual C X) ≪≫ β_ (dual C (dual C X)) (dual C A) :=
      Iso.ext hb
    exact congrArg Iso.inv hi
  rw [J.tensor]
  dsimp only [doubleDualTensorHom]
  simp only [assoc]
  rw [← dualTensorIso_inv, ← dualTensorIso_hom]
  change (J.j.hom.app A ⊗ₘ J.j.hom.app X) ≫
      (dualTensorIso (dual C X) (dual C A)).inv ≫
      dualMap C (dualTensorIso A X).hom ≫
      dualMap C (P.ambientFreeDualIso X).hom = _
  dsimp only [ambientFreeDualIso, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]
  simp only [dualMap, comp_rightAdjointMate, assoc]
  rw [← comp_rightAdjointMate_assoc]
  simp only [Iso.inv_hom_id, rightAdjointMate_id, id_comp]
  change (J.j.hom.app A ⊗ₘ J.j.hom.app X) ≫
      (dualTensorIso (dual C X) (dual C A)).inv ≫
      dualMap C (dual C X ◁ (P.algebraDualIso).hom) ≫
      dualMap C (β_ (dual C X) A).inv = _
  rw [reassoc_of% hni, hbi]
  erw [tensorHom_comp_whiskerRight_assoc,
    P.algebraDualIso_pivotal J hA, braiding_inv_naturality_assoc,
    braiding_inv_naturality_right_assoc, MonoidalCategory.tensorHom_def, assoc]
  rfl

/-- The actual canonical free comparison followed by the perfect-cap
comparison is the explicit ambient free dual isomorphism. -/
lemma freeDualComparison_ambient (X : C) :
    (dualComparison (InternalModule.freeFunctor (A := A)) X).hom.hom ≫
        (P.ambientDualIso (InternalModule.free A X)).hom =
      (P.ambientFreeDualIso X).hom := by
  apply (cancel_mono (dualTensorIso A X).hom).mp
  simpa only [ambientFreeDualIso, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, assoc, Iso.inv_hom_id, comp_id] using
    P.freeDualComparison_formula X

lemma freeDoubleDualComparison_ambient (X : C) :
    (doubleDualComparison (InternalModule.freeFunctor (A := A)) X).hom.hom ≫
        (P.ambientDoubleDualIso (InternalModule.free A X)).hom =
      (P.ambientFreeDualIso (dual C X)).hom ≫ dualMap C (P.ambientFreeDualIso X).inv := by
  have hi : (P.ambientDualIso (InternalModule.free A X)).inv ≫
      (dualComparison (InternalModule.freeFunctor (A := A)) X).inv.hom =
      (P.ambientFreeDualIso X).inv := by
    have he : (Mod_.forget (D := C) A).mapIso
          (dualComparison (InternalModule.freeFunctor (A := A)) X) ≪≫
        P.ambientDualIso (InternalModule.free A X) = P.ambientFreeDualIso X :=
      Iso.ext (P.freeDualComparison_ambient X)
    exact congrArg Iso.inv he
  dsimp only [doubleDualComparison, ambientDoubleDualIso, Iso.trans_hom,
    Iso.symm_hom, dualMapIso, Mod_.comp_hom']
  simp only [assoc]
  erw [reassoc_of% (P.ambientDualIso_naturality
    (dualComparison (InternalModule.freeFunctor (A := A)) X).inv)]
  erw [← assoc, P.freeDualComparison_ambient]
  rw [← comp_rightAdjointMate, hi]

/-- The actual free functor intertwines the ambient pivotal structure
with the underlying candidate on modules. -/
lemma free_pivotalUnderlying (J : PivotalStructure C)
    (hA : (J.twistIso A).hom = 𝟙 A) (X : C) :
    ((InternalModule.freeFunctor (A := A)).map (J.j.hom.app X) ≫
        (doubleDualComparison (InternalModule.freeFunctor (A := A)) X).hom).hom =
      (P.pivotalUnderlyingIso J).hom.app (InternalModule.free A X) := by
  apply (cancel_mono (P.ambientDoubleDualIso (InternalModule.free A X)).hom).mp
  simp only [Mod_.comp_hom', assoc]
  change (A ◁ J.j.hom.app X) ≫
      (doubleDualComparison (InternalModule.freeFunctor (A := A)) X).hom.hom ≫
        (P.ambientDoubleDualIso (InternalModule.free A X)).hom = _
  rw [P.freeDoubleDualComparison_ambient, ← assoc,
    ← P.ambientFreeDualIso_pivotal J hA X, assoc]
  simp only [dualMap, ← comp_rightAdjointMate, Iso.inv_hom_id,
    @rightAdjointMate_id]
  rw [P.pivotalUnderlyingIso_hom_app]
  simp only [assoc, Iso.inv_hom_id, comp_id]
  change J.j.hom.app (A ⊗ X) ≫ 𝟙 _ = J.j.hom.app (A ⊗ X)
  exact comp_id _

end Paper18.Category.ModuleBalancing.MultiplicationPairing
