import Paper18.Category.DrinfeldRigidLax
import Paper18.Category.PivotalFunctor
import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# Actual right duals in the Drinfeld center

The dual half-braiding is obtained by partial transposition and its
invertibility has been proved from rigidity. Evaluation and coevaluation
are the actual underlying cups and caps, and their centrality is derived.
-/
noncomputable section
universe v u
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] (Z : Center C)

/-- The partial transpose as a cup-and-cap diagram. -/
lemma dualHalfBraidingHom_eq (U : C) : dualHalfBraidingHom Z U =
    𝟙 (Z.1ᘁ ⊗ U) ⊗≫ (Z.1ᘁ ⊗ U) ◁ η_ Z.1 Z.1ᘁ ⊗≫
      (Z.1ᘁ : C) ◁ (Z.2.β U).inv ▷ Z.1ᘁ ⊗≫
        ε_ Z.1 Z.1ᘁ ▷ (U ⊗ Z.1ᘁ) ⊗≫ 𝟙 (U ⊗ Z.1ᘁ) := by
  dsimp [dualHalfBraidingHom, tensorRightHomEquiv, dualHalfBraidingCap]
  monoidal

/-- The same partial transpose also intertwines the actual coevaluation. -/
@[reassoc]
lemma dualHalfBraidingHom_cup (U : C) :
    η_ Z.1 Z.1ᘁ ▷ U ≫ (α_ Z.1 Z.1ᘁ U).hom ≫
      Z.1 ◁ dualHalfBraidingHom Z U =
    (λ_ U).hom ≫ (ρ_ U).inv ≫ U ◁ η_ Z.1 Z.1ᘁ ≫
      (α_ U Z.1 Z.1ᘁ).inv ≫ (Z.2.β U).inv ▷ Z.1ᘁ ≫ (α_ Z.1 U Z.1ᘁ).hom := by
  calc
    _ = 𝟙 ((𝟙_ C) ⊗ U) ⊗≫
        (η_ Z.1 Z.1ᘁ ▷ (U ⊗ 𝟙_ C) ≫ (Z.1 ⊗ Z.1ᘁ) ◁ (U ◁ η_ Z.1 Z.1ᘁ)) ⊗≫
        Z.1 ◁ (Z.1ᘁ : C) ◁ (Z.2.β U).inv ▷ Z.1ᘁ ⊗≫
        Z.1 ◁ ε_ Z.1 Z.1ᘁ ▷ (U ⊗ Z.1ᘁ) ⊗≫ 𝟙 (Z.1 ⊗ (U ⊗ Z.1ᘁ)) := by
      rw [dualHalfBraidingHom_eq]
      monoidal
    _ = 𝟙 ((𝟙_ C) ⊗ U) ⊗≫ U ◁ η_ Z.1 Z.1ᘁ ⊗≫
        (η_ Z.1 Z.1ᘁ ▷ (U ⊗ Z.1) ≫ (Z.1 ⊗ Z.1ᘁ) ◁ (Z.2.β U).inv) ▷ Z.1ᘁ ⊗≫
        Z.1 ◁ ε_ Z.1 Z.1ᘁ ▷ (U ⊗ Z.1ᘁ) ⊗≫ 𝟙 (Z.1 ⊗ (U ⊗ Z.1ᘁ)) := by
      rw [← whisker_exchange]
      monoidal
    _ = 𝟙 ((𝟙_ C) ⊗ U) ⊗≫ U ◁ η_ Z.1 Z.1ᘁ ⊗≫
        (Z.2.β U).inv ▷ Z.1ᘁ ⊗≫
        (η_ Z.1 Z.1ᘁ ▷ Z.1 ⊗≫ Z.1 ◁ ε_ Z.1 Z.1ᘁ) ▷ (U ⊗ Z.1ᘁ) ⊗≫
        𝟙 (Z.1 ⊗ (U ⊗ Z.1ᘁ)) := by
      rw [← whisker_exchange]
      monoidal
    _ = _ := by
      rw [ExactPairing.evaluation_coevaluation'']
      monoidal

variable [LeftRigidCategory C]

/-- The actual right dual central object, with constructed half-braiding. -/
def rightDualObj : Center C := ⟨Z.1ᘁ, (dualLaxHalfBraiding Z).toHalfBraiding⟩

@[simp] lemma rightDualObj_fst : (rightDualObj Z).1 = Z.1ᘁ := rfl

@[simp] lemma rightDualObj_halfBraiding (U : C) :
    ((rightDualObj Z).2.β U).hom = dualHalfBraidingHom Z U := rfl

/-- The actual underlying evaluation is a morphism in the center. -/
def rightEvaluation : rightDualObj Z ⊗ Z ⟶ 𝟙_ (Center C) where
  f := ε_ Z.1 Z.1ᘁ
  comm U := by
    simp only [Center.tensor_β, Center.tensorUnit_β, Iso.trans_hom, Iso.symm_hom,
      whiskerLeftIso_hom, whiskerRightIso_hom, rightDualObj_halfBraiding, rightDualObj_fst]
    simp only [assoc]
    change (ε_ Z.1 Z.1ᘁ ▷ U) ≫ (λ_ U).hom ≫ (ρ_ U).inv =
      (α_ Z.1ᘁ Z.1 U).hom ≫ (Z.1ᘁ : C) ◁ (Z.2.β U).hom ≫
        (α_ Z.1ᘁ U Z.1).inv ≫ dualHalfBraidingHom Z U ▷ Z.1 ≫
          (α_ U Z.1ᘁ Z.1).hom ≫ U ◁ ε_ Z.1 Z.1ᘁ
    apply (cancel_mono (ρ_ U).hom).mp
    simp only [assoc, Iso.inv_hom_id, comp_id]
    rw [dualHalfBraidingHom_cap]
    simp [dualHalfBraidingCap, ← whiskerLeft_comp_assoc]

/-- The actual underlying coevaluation is a morphism in the center. -/
def rightCoevaluation : 𝟙_ (Center C) ⟶ Z ⊗ rightDualObj Z where
  f := η_ Z.1 Z.1ᘁ
  comm U := by
    simp only [Center.tensor_β, Center.tensorUnit_β, Iso.trans_hom, Iso.symm_hom,
      whiskerLeftIso_hom, whiskerRightIso_hom, rightDualObj_halfBraiding, rightDualObj_fst]
    simp only [assoc]
    change (η_ Z.1 Z.1ᘁ ▷ U) ≫ (α_ Z.1 Z.1ᘁ U).hom ≫
      (Z.1 ◁ dualHalfBraidingHom Z U) ≫ (α_ Z.1 U Z.1ᘁ).inv ≫
        (Z.2.β U).hom ▷ Z.1ᘁ ≫ (α_ U Z.1 Z.1ᘁ).hom =
      (λ_ U).hom ≫ (ρ_ U).inv ≫ U ◁ η_ Z.1 Z.1ᘁ
    rw [dualHalfBraidingHom_cup_assoc]
    simp

/-- The two central cups and caps satisfy both triangle identities because
their actual underlying maps do and the forgetful functor is faithful. -/
def rightExactPairing : ExactPairing Z (rightDualObj Z) := by
  letI : (Center.forget C).Faithful := ⟨fun h => Center.ext _ _ h⟩
  letI : ExactPairing ((Center.forget C).obj Z)
      ((Center.forget C).obj (rightDualObj Z)) := by
    change ExactPairing Z.1 Z.1ᘁ
    infer_instance
  apply exactPairingOfFaithful (Center.forget C) (rightEvaluation Z) (rightCoevaluation Z)
  · simp only [Center.forget_δ, Center.forget_ε]
    erw [id_comp, comp_id]
    rfl
  · simp only [Center.forget_η, Center.forget_μ]
    erw [id_comp, comp_id]
    rfl

instance center_rightRigidCategory : RightRigidCategory (Center C) where
  rightDual Z := { rightDual := rightDualObj Z, exact := rightExactPairing Z }

end Paper18.Category.Drinfeld
