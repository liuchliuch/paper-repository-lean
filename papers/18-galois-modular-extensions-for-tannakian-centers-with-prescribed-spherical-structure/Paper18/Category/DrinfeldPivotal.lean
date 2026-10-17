import Paper18.Category.DrinfeldPivotalBasic
import Paper18.Category.DrinfeldLinear

/-!
# Actual pivotal and spherical structures on the Drinfeld center

The ambient category need not be braided. The pivotal components are
actual central morphisms by the double-transposition theorem. All unit,
tensor, and trace statements use the actual chosen central cups and caps.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [LeftRigidCategory C]

@[simp] lemma forget_evaluation (Z : Center C) :
    (Center.forget C).map (ε_ Z (dual (Center C) Z)) = ε_ Z.1 (dual C Z.1) := rfl

@[simp] lemma forget_coevaluation (Z : Center C) :
    (Center.forget C).map (η_ Z (dual (Center C) Z)) = η_ Z.1 (dual C Z.1) := rfl

@[simp] lemma center_dual_fst (Z : Center C) :
    (dual (Center C) Z).1 = dual C Z.1 := rfl

@[simp] lemma center_tensorUnit_fst : (𝟙_ (Center C)).1 = 𝟙_ C := rfl

@[simp] lemma evaluation_f (Z : Center C) :
    (ε_ Z (dual (Center C) Z)).f = ε_ Z.1 (dual C Z.1) := rfl

@[simp] lemma coevaluation_f (Z : Center C) :
    (η_ Z (dual (Center C) Z)).f = η_ Z.1 (dual C Z.1) := rfl

/-- Actual adjoint mates in the center have the actual ambient adjoint mates. -/
@[simp] lemma forget_dualMap {Z W : Center C} (f : Z ⟶ W) :
    (Center.forget C).map (dualMap (Center C) f) = dualMap C f.f := by
  simp [dualMap, rightAdjointMate]

@[simp] lemma dualMap_f {Z W : Center C} (f : Z ⟶ W) :
    (dualMap (Center C) f).f = dualMap C f.f := forget_dualMap f

@[simp] lemma forget_dualTensorTo (Z W : Center C) :
    (Center.forget C).map (dualTensorTo (Center C) Z W) = dualTensorTo C Z.1 W.1 := by
  simp [dualTensorTo, tensorCoevaluation]

@[simp] lemma dualTensorTo_f (Z W : Center C) :
    (dualTensorTo (Center C) Z W).f = dualTensorTo C Z.1 W.1 := forget_dualTensorTo Z W

@[simp] lemma forget_dualTensorFrom (Z W : Center C) :
    (Center.forget C).map (dualTensorFrom (Center C) Z W) = dualTensorFrom C Z.1 W.1 := by
  simp [dualTensorFrom, tensorEvaluation]

@[simp] lemma forget_doubleDualTensorHom (Z W : Center C) :
    (Center.forget C).map (doubleDualTensorHom (Center C) Z W) =
      doubleDualTensorHom C Z.1 W.1 := by
  simp only [doubleDualTensorHom, Functor.map_comp, forget_dualTensorFrom,
    forget_dualMap, center_dual_fst, dualTensorTo_f]

@[simp] lemma forget_doubleDualUnitHom :
    (Center.forget C).map (doubleDualUnitHom (Center C)) = doubleDualUnitHom C := by
  simp [doubleDualUnitHom, dualUnitFrom, dualUnitTo]

/-- Each prescribed pivotal component lifts to an actual central isomorphism. -/
def pivotalComponent (J : PivotalStructure C) (Z : Center C) :
    Z ≅ (doubleDualFunctor (Center C)).obj Z :=
  Center.isoMk ⟨J.j.hom.app Z.1, pivotalMap_central J Z⟩

@[simp] lemma pivotalComponent_hom_f (J : PivotalStructure C) (Z : Center C) :
    (pivotalComponent J Z).hom.f = J.j.hom.app Z.1 := rfl

/-- The prescribed pivotal natural isomorphism lifted to the actual center. -/
def pivotalNatIso (J : PivotalStructure C) :
    𝟭 (Center C) ≅ doubleDualFunctor (Center C) :=
  NatIso.ofComponents (pivotalComponent J) (by
    intro Z W f
    apply Center.ext
    change f.f ≫ J.j.hom.app W.1 =
      J.j.hom.app Z.1 ≫ (Center.forget C).map ((doubleDualFunctor (Center C)).map f)
    simp only [doubleDualFunctor, forget_dualMap, dualMap_f]
    exact J.j.hom.naturality f.f)

/-- The actual pivotal structure on the center. Its full unit and tensor
coherence is inherited through the actual central cups and caps. -/
def centerPivotal (J : PivotalStructure C) : PivotalStructure (Center C) where
  j := pivotalNatIso J
  unit := by
    apply Center.ext
    change J.j.hom.app (𝟙_ C) = (Center.forget C).map (doubleDualUnitHom (Center C))
    rw [forget_doubleDualUnitHom]
    exact J.unit
  tensor Z W := by
    apply Center.ext
    change J.j.hom.app (Z.1 ⊗ W.1) = (Center.forget C).map
      (((pivotalNatIso J).hom.app Z ⊗ₘ (pivotalNatIso J).hom.app W) ≫
        doubleDualTensorHom (Center C) Z W)
    rw [Functor.map_comp, forget_doubleDualTensorHom]
    exact J.tensor Z.1 W.1

/-- The canonical dual comparison of the center forgetful functor is the
identity because the central cap is the actual ambient cap. -/
@[simp] lemma forget_dualComparison (Z : Center C) :
    dualComparison (Center.forget C) Z = Iso.refl (dual C Z.1) := by
  apply Iso.ext
  apply pairing_hom_ext (inferInstanceAs (ExactPairing Z.1 (dual C Z.1)))
  have h := dualComparison_evaluation (Center.forget C) Z
  simp only [Center.forget_μ, Center.forget_η, id_comp, comp_id] at h
  change (dualComparison (Center.forget C) Z).hom ▷ Z.1 ≫ ε_ Z.1 (dual C Z.1) =
    𝟙 (dual C Z.1) ▷ Z.1 ≫ ε_ Z.1 (dual C Z.1)
  simpa only [id_whiskerRight, id_comp] using h

@[simp] lemma forget_doubleDualComparison_hom (Z : Center C) :
    (doubleDualComparison (Center.forget C) Z).hom = 𝟙 (dual C (dual C Z.1)) := by
  simp only [doubleDualComparison, forget_dualComparison, Iso.trans_hom, Iso.symm_hom,
    dualMapIso, Iso.refl_inv, Iso.refl_hom, dualMap]
  erw [rightAdjointMate_id, comp_id]
  rfl

/-- The canonical forgetful tensor functor preserves the actual lifted
pivotal structure through its canonical double-dual comparison. -/
theorem forget_preservesPivotal (J : PivotalStructure C) :
    PreservesPivotal (Center.forget C) (centerPivotal J) J := by
  intro Z
  rw [forget_doubleDualComparison_hom]
  erw [comp_id]
  rfl

/-- The lifted actual right trace forgets to the prescribed ambient trace. -/
lemma centerPivotal_rightTrace (J : PivotalStructure C) {Z : Center C} (f : Z ⟶ Z) :
    ((centerPivotal J).rightTrace f).f = J.rightTrace f.f := by
  have h := (forget_preservesPivotal J).rightTrace f
  simpa only [Center.forget_ε, Center.forget_η, id_comp, comp_id] using h

/-- The same equality holds for the actual left trace. -/
lemma centerPivotal_leftTrace (J : PivotalStructure C) {Z : Center C} (f : Z ⟶ Z) :
    ((centerPivotal J).leftTrace f).f = J.leftTrace f.f := by
  have h := (forget_preservesPivotal J).leftTrace f
  simpa only [Center.forget_ε, Center.forget_η, id_comp, comp_id] using h

/-- Prescribed ambient sphericality lifts to every actual central endomorphism. -/
theorem centerPivotal_spherical (J : PivotalStructure C) (hJ : J.Spherical) :
    (centerPivotal J).Spherical :=
  (forget_preservesPivotal J).spherical_of_faithful hJ

end Paper18.Category.Drinfeld
