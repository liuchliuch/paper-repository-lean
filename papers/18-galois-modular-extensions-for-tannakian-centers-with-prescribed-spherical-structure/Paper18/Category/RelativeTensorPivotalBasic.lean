import Paper18.Category.LocalModulesPivotalDual
import Paper18.Category.PivotalBalancingBasic

/-! # Actual underlying double-dual comparisons for Frobenius modules -/
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

/-- Twice applying the actual perfect-cap comparison identifies the
underlying chosen module double dual with the ambient double dual. -/
def ambientDoubleDualIso (M : Mod_ C A) :
    (dual (Mod_ C A) (dual (Mod_ C A) M)).X ≅ dual C (dual C M.X) :=
  P.ambientDualIso (dual (Mod_ C A) M) ≪≫ (dualMapIso (P.ambientDualIso M)).symm

@[reassoc]
lemma ambientDoubleDualIso_naturality {M N : Mod_ C A} (f : M ⟶ N) :
    ((doubleDualFunctor (Mod_ C A)).map f).hom ≫ (P.ambientDoubleDualIso N).hom =
      (P.ambientDoubleDualIso M).hom ≫ (doubleDualFunctor C).map f.hom := by
  have hn := P.ambientDualIso_naturality f
  have hi : (P.ambientDualIso N).inv ≫ (dualMap (Mod_ C A) f).hom =
      dualMap C f.hom ≫ (P.ambientDualIso M).inv := by
    apply (cancel_mono (P.ambientDualIso M).hom).mp
    simp only [assoc, Iso.inv_hom_id, comp_id]
    rw [hn, Iso.inv_hom_id_assoc]
  dsimp only [ambientDoubleDualIso, Iso.trans_hom, Iso.symm_hom, dualMapIso]
  change (dualMap (Mod_ C A) (dualMap (Mod_ C A) f)).hom ≫
      (P.ambientDualIso (dual (Mod_ C A) N)).hom ≫ dualMap C (P.ambientDualIso N).inv = _
  rw [reassoc_of% (P.ambientDualIso_naturality (dualMap (Mod_ C A) f))]
  rw [← comp_rightAdjointMate, hi, comp_rightAdjointMate, assoc]
  rfl

/-- The actual comparisons form an actual natural isomorphism of the two
underlying double-dual functors. -/
def ambientDoubleDualNatIso :
    doubleDualFunctor (Mod_ C A) ⋙ Mod_.forget (D := C) A ≅
      Mod_.forget (D := C) A ⋙ doubleDualFunctor C :=
  NatIso.ofComponents P.ambientDoubleDualIso (fun f => P.ambientDoubleDualIso_naturality f)

/-- The candidate pivotal components are an actual natural isomorphism on
underlying objects, before their module linearity is proved. -/
def pivotalUnderlyingIso (J : PivotalStructure C) :
    Mod_.forget (D := C) A ≅ doubleDualFunctor (Mod_ C A) ⋙ Mod_.forget (D := C) A :=
  (Functor.rightUnitor (Mod_.forget (D := C) A)).symm ≪≫
    Functor.isoWhiskerLeft (Mod_.forget (D := C) A) J.j ≪≫ (P.ambientDoubleDualNatIso).symm

@[simp]
lemma pivotalUnderlyingIso_hom_app (J : PivotalStructure C) (M : Mod_ C A) :
    (P.pivotalUnderlyingIso J).hom.app M =
      J.j.hom.app M.X ≫ (P.ambientDoubleDualIso M).inv := by
  dsimp [pivotalUnderlyingIso, ambientDoubleDualNatIso]
  simp only [id_comp]

/-- The actual nondegenerate multiplication cap identifies the algebra
with its chosen ambient dual. -/
def algebraDualIso : A ≅ dual C A :=
  rightDualIso P.pairing (inferInstanceAs (ExactPairing A (dual C A)))

omit [BraidedCategory C] [HasCoequalizers C] [IsCommMonObj A]
  [RightRigidCategory (Mod_ C A)] in
@[reassoc]
lemma algebraDualIso_evaluation :
    (P.algebraDualIso).hom ▷ A ≫ ε_ A (dual C A) =
      @ExactPairing.evaluation C _ _ A A P.pairing :=
  rightDualIso_evaluation _ _

omit [HasCoequalizers C] [RightRigidCategory (Mod_ C A)] in
/-- A trivial algebra twist makes its actual symmetric multiplication
pairing compatible with the ambient pivotal structure. -/
lemma algebraDualIso_pivotal (J : PivotalStructure C)
    (hA : (J.twistIso A).hom = 𝟙 A) :
    J.j.hom.app A ≫ dualMap C (P.algebraDualIso).hom = (P.algebraDualIso).hom := by
  apply (dualCapEquiv A A (dual C A)).injective
  simp only [dualCapEquiv_apply, comp_whiskerRight, assoc]
  rw [rightAdjointMate_comp_evaluation]
  erw [← whisker_exchange_assoc]
  change (A ◁ (P.algebraDualIso).hom) ≫ J.leftEvaluation A =
    (P.algebraDualIso).hom ▷ A ≫ ε_ A (dual C A)
  rw [← J.twist_evaluation A, hA, id_whiskerRight, id_comp,
    braiding_naturality_right_assoc, P.algebraDualIso_evaluation]
  exact P.evaluation_braiding

end Paper18.Category.ModuleBalancing.MultiplicationPairing
