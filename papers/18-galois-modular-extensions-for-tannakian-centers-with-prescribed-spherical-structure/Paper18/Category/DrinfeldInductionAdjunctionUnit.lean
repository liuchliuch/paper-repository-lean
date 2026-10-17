import Paper18.Category.DrinfeldInductionAdjunctionBasic

/-! # The actual unit-component normalization for central induction -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  (J : PivotalStructure C)

omit [RightRigidCategory C] in
/-- Canonical comparison between left duals preserves the actual evaluation. -/
lemma leftDualIso_evaluation {A B Y : C} (p : ExactPairing A Y) (q : ExactPairing B Y) :
    Y ◁ (leftDualIso p q).hom ≫ @ExactPairing.evaluation _ _ _ B Y q =
      @ExactPairing.evaluation _ _ _ A Y p := by
  simpa only [leftDualIso, id_whiskerRight, id_comp] using
    (@leftAdjointMate_comp_evaluation C _ _ Y Y
      (@HasLeftDual.mk C _ _ Y B q) (@HasLeftDual.mk C _ _ Y A p) (𝟙 Y))

/-- The prescribed pivotal left pairing identifies the chosen dual of the
unit with the unit. No scalar normalization is assumed. -/
def pivotalUnitDualIso : (𝟙_ C)ᘁ ≅ 𝟙_ C :=
  leftDualIso (J.leftExactPairing (𝟙_ C)) CategoryTheory.exactPairingUnit

/-- Its evaluation equation is the precise normalization of the pivotal
unit cap needed for the induction augmentation. -/
lemma pivotalUnitDualIso_evaluation :
    (λ_ ((𝟙_ C)ᘁ)).hom ≫ (pivotalUnitDualIso J).hom = J.leftEvaluation (𝟙_ C) := by
  have h := leftDualIso_evaluation (J.leftExactPairing (𝟙_ C))
    (CategoryTheory.exactPairingUnit (C := C))
  change (𝟙_ C) ◁ (pivotalUnitDualIso J).hom ≫ (ρ_ (𝟙_ C)).hom =
    J.leftEvaluation (𝟙_ C) at h
  calc
    _ = (𝟙_ C) ◁ (pivotalUnitDualIso J).hom ≫ (ρ_ (𝟙_ C)).hom := by monoidal
    _ = _ := h

/-- The actual insertion into the tensor-unit term of the induction coend.
After composing with the universal inclusion it becomes the adjunction unit. -/
def inductionAdjunctionUnitComponent (X : C) :
    X ⟶ ((𝟙_ C) ⊗ X) ⊗ (𝟙_ C)ᘁ :=
  (λ_ X).inv ≫ (ρ_ ((𝟙_ C) ⊗ X)).inv ≫
    ((𝟙_ C) ⊗ X) ◁ (pivotalUnitDualIso J).inv

/-- Closing the actual unit component returns exactly the original map.
This verifies the prospective left-adjoint orientation by an actual equation. -/
lemma inductionAdjunctionUnitComponent_augmentation {X : C} (Z : Center C) (f : X ⟶ Z.1) :
    inductionAdjunctionUnitComponent J X ≫ inductionAugmentationComponent J Z f (𝟙_ C) = f := by
  have hb : Z.2.β (𝟙_ C) = ρ_ Z.1 ≪≫ (λ_ Z.1).symm := by
    apply Iso.ext
    exact halfBraiding_unit Z.1 Z.2
  calc
    _ = (ρ_ X).inv ≫ X ◁ (pivotalUnitDualIso J).inv ≫
        f ▷ ((𝟙_ C)ᘁ) ≫ Z.1 ◁ (pivotalUnitDualIso J).hom ≫ (ρ_ Z.1).hom := by
      dsimp [inductionAdjunctionUnitComponent, inductionAugmentationComponent,
        inductionAugmentationCap]
      rw [hb, ← pivotalUnitDualIso_evaluation J]
      simp only [Iso.trans_inv, Iso.symm_inv]
      monoidal
    _ = (ρ_ X).inv ≫ f ▷ (𝟙_ C) ≫ Z.1 ◁
        ((pivotalUnitDualIso J).inv ≫ (pivotalUnitDualIso J).hom) ≫ (ρ_ Z.1).hom := by
      rw [← whisker_exchange_assoc, ← whiskerLeft_comp_assoc]
      simp
    _ = f := by simp

end Paper18.Category.Drinfeld
