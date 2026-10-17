import Paper18.Category.DrinfeldInductionAdjunctionCentrality
import Paper18.Category.DrinfeldInductionUnit

/-! # Generation of actual induction morphisms by the adjunction unit -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  (J : PivotalStructure C)

/-- Pivotal coherence at the unit identifies the left-pairing and
right-pairing comparisons with the unit. -/
lemma pivotalUnitDualIso_eq_dualUnitIso : pivotalUnitDualIso J = dualUnitIso := by
  apply Iso.ext
  apply (cancel_epi (λ_ ((𝟙_ C)ᘁ)).hom).mp
  rw [pivotalUnitDualIso_evaluation]
  change (pivotalMap J (𝟙_ C) ▷ (𝟙_ C)ᘁ) ≫
    ε_ ((𝟙_ C)ᘁ) (dual C ((𝟙_ C)ᘁ)) = _
  rw [pivotalMap_unit, comp_whiskerRight_assoc]
  change (dualUnitIso (C := C)).inv ▷ (𝟙_ C)ᘁ ≫
    rightAdjointMate (dualUnitIso (C := C)).hom ▷ (𝟙_ C)ᘁ ≫ _ = _
  rw [rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc,
    dualUnitIso_inv_evaluation]
  monoidal

/-- The inverse dual comparison at a unit factor is the actual dual of
the right unitor, after the unit dual is identified. -/
lemma inductionGenerationUnitDualComparison (A : C) :
    ((dualUnitIso (C := C)).inv ▷ dual C A) ≫ (dualTensorIso A (𝟙_ C)).inv =
      (λ_ (dual C A)).hom ≫ dualMap C (ρ_ A).hom := by
  apply (cancel_mono (dualTensorIso A (𝟙_ C)).hom).mp
  rw [assoc, Iso.inv_hom_id, comp_id, assoc, dualTensorIso_rightUnitor]
  simp


/-- A pivotal left cap cancels the right cup on the dual, leaving exactly
the pivotal component on the original strand. -/
lemma pivotalLeftEvaluation_coevaluation (T : C) :
    𝟙 T ⊗≫ T ◁ η_ Tᘁ (dual C Tᘁ) ⊗≫
      J.leftEvaluation T ▷ dual C Tᘁ ⊗≫ 𝟙 (dual C Tᘁ) = pivotalMap J T := by
  calc
    _ = 𝟙 T ⊗≫
        (T ◁ η_ Tᘁ (dual C Tᘁ) ≫ pivotalMap J T ▷ (Tᘁ ⊗ dual C Tᘁ)) ⊗≫
        ε_ Tᘁ (dual C Tᘁ) ▷ dual C Tᘁ ⊗≫ 𝟙 (dual C Tᘁ) := by
      dsimp [PivotalStructure.leftEvaluation, pivotalMap]
      monoidal
    _ = pivotalMap J T ⊗≫
        (dual C Tᘁ ◁ η_ Tᘁ (dual C Tᘁ) ⊗≫
          ε_ Tᘁ (dual C Tᘁ) ▷ dual C Tᘁ) ⊗≫ 𝟙 (dual C Tᘁ) := by
      rw [whisker_exchange]
      monoidal
    _ = _ := by
      rw [ExactPairing.coevaluation_evaluation'']
      monoidal

/-- Closing the outer strand of the actual insertion at the dual produces
the two pivotal components, with no scalar factor. -/
lemma pivotalInsertionClosure (T X : C) :
    𝟙 ((T ⊗ X) ⊗ Tᘁ) ⊗≫ T ◁ rigidInsertion J Tᘁ X ⊗≫
      J.leftEvaluation T ▷ ((dual C Tᘁ ⊗ X) ⊗ dual C (dual C Tᘁ)) ⊗≫
        𝟙 ((dual C Tᘁ ⊗ X) ⊗ dual C (dual C Tᘁ)) =
      (pivotalMap J T ▷ X) ▷ Tᘁ ≫ (dual C Tᘁ ⊗ X) ◁ pivotalMap J Tᘁ := by
  calc
    _ = 𝟙 ((T ⊗ X) ⊗ Tᘁ) ⊗≫
        (T ◁ η_ Tᘁ (dual C Tᘁ)) ▷ (X ⊗ Tᘁ) ⊗≫
        (((T ⊗ Tᘁ) ◁ ((dual C Tᘁ ⊗ X) ◁ pivotalMap J Tᘁ)) ≫
          J.leftEvaluation T ▷ ((dual C Tᘁ ⊗ X) ⊗ dual C (dual C Tᘁ))) ⊗≫
        𝟙 ((dual C Tᘁ ⊗ X) ⊗ dual C (dual C Tᘁ)) := by
      dsimp [rigidInsertion]
      monoidal
    _ = 𝟙 ((T ⊗ X) ⊗ Tᘁ) ⊗≫
        (𝟙 T ⊗≫ T ◁ η_ Tᘁ (dual C Tᘁ) ⊗≫
          J.leftEvaluation T ▷ dual C Tᘁ ⊗≫ 𝟙 (dual C Tᘁ)) ▷ (X ⊗ Tᘁ) ⊗≫
        (dual C Tᘁ ⊗ X) ◁ pivotalMap J Tᘁ := by
      rw [whisker_exchange]
      monoidal
    _ = _ := by
      rw [pivotalLeftEvaluation_coevaluation]
      monoidal

section Coend
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The actual unit term reduces the braiding tail to its remaining label. -/
lemma inductionBraidingTail_unit_term (X U : C) :
    ((Uᘁ ◁ inductionAdjunctionUnitComponent J X) ▷ dual C (dual C U)) ≫
      inductionBraidingTail S X U (𝟙_ C) = inductionι S X Uᘁ := by
  calc
    _ = 𝟙 ((Uᘁ ⊗ X) ⊗ dual C (dual C U)) ⊗≫
        (((ρ_ Uᘁ).inv ▷ X) ▷ dual C (dual C U)) ⊗≫
        (((Uᘁ ⊗ (𝟙_ C)) ⊗ X) ◁
          (((dualUnitIso (C := C)).inv ▷ dual C (dual C U)) ≫
            (dualTensorIso Uᘁ (𝟙_ C)).inv)) ⊗≫
        inductionι S X (Uᘁ ⊗ (𝟙_ C)) := by
      dsimp [inductionAdjunctionUnitComponent, inductionBraidingTail]
      rw [pivotalUnitDualIso_eq_dualUnitIso]
      monoidal
    _ = 𝟙 ((Uᘁ ⊗ X) ⊗ dual C (dual C U)) ⊗≫
        (((ρ_ Uᘁ).inv ▷ X) ▷ dual C (dual C U)) ⊗≫
        ((((Uᘁ ⊗ (𝟙_ C)) ⊗ X) ◁ dualMap C (ρ_ Uᘁ).hom) ≫
          inductionι S X (Uᘁ ⊗ (𝟙_ C))) := by
      rw [inductionGenerationUnitDualComparison]
      monoidal
    _ = _ := by
      rw [inductionι_dinatural]
      monoidal

/-- Crossing the adjunction unit is exactly the universal cup insertion
followed by the remaining dual-labelled coend component. -/
lemma inductionAdjunctionUnit_halfBraiding (X U : C) :
    (inductionAdjunctionUnit J S X ▷ U) ≫ inductionHalfBraidingHom S J X U =
      rigidInsertion J U X ≫ U ◁ inductionι S X Uᘁ := by
  rw [inductionAdjunctionUnit, comp_whiskerRight_assoc, inductionHalfBraidingHom_ι,
    inductionHalfBraidingComponent, ← assoc, rigidInsertion_naturality, assoc,
    ← whiskerLeft_comp, inductionBraidingTail_unit_term]


/-- Changing a coend label by the pivotal isomorphism leaves the actual
universal component unchanged after the matching dual change. -/
lemma inductionι_pivotal (X T : C) :
    ((pivotalMap J T ▷ X) ▷ Tᘁ) ≫
      (dual C Tᘁ ⊗ X) ◁ pivotalMap J Tᘁ ≫ inductionι S X (dual C Tᘁ) =
        inductionι S X T := by
  rw [← whisker_exchange_assoc, ← inductionι_dinatural, ← whiskerLeft_comp_assoc]
  change (T ⊗ X) ◁
    (J.j.hom.app (dual C T) ≫ dualMap C (J.j.hom.app T)) ≫ inductionι S X T = _
  rw [J.dual_compatibility]
  simp

/-- Every universal coend component is generated by crossing the actual
adjunction unit and closing with the pivotal cap. -/
lemma inductionι_generated (X T : C) :
    𝟙 ((T ⊗ X) ⊗ Tᘁ) ⊗≫
      T ◁ ((inductionAdjunctionUnit J S X ▷ Tᘁ) ≫
        inductionHalfBraidingHom S J X Tᘁ) ⊗≫
      J.leftEvaluation T ▷ inductionUnderlying S X ⊗≫
        𝟙 (inductionUnderlying S X) = inductionι S X T := by
  calc
    _ = 𝟙 ((T ⊗ X) ⊗ Tᘁ) ⊗≫ T ◁ rigidInsertion J Tᘁ X ⊗≫
        (((T ⊗ Tᘁ) ◁ inductionι S X (dual C Tᘁ)) ≫
          J.leftEvaluation T ▷ inductionUnderlying S X) ⊗≫
        𝟙 (inductionUnderlying S X) := by
      rw [inductionAdjunctionUnit_halfBraiding]
      monoidal
    _ = (𝟙 ((T ⊗ X) ⊗ Tᘁ) ⊗≫ T ◁ rigidInsertion J Tᘁ X ⊗≫
        J.leftEvaluation T ▷ ((dual C Tᘁ ⊗ X) ⊗ dual C (dual C Tᘁ)) ⊗≫
          𝟙 ((dual C Tᘁ ⊗ X) ⊗ dual C (dual C Tᘁ))) ≫
            inductionι S X (dual C Tᘁ) := by
      rw [whisker_exchange]
      monoidal
    _ = _ := by
      rw [pivotalInsertionClosure, assoc]
      exact inductionι_pivotal J S X T

end Coend
end Paper18.Category.Drinfeld
