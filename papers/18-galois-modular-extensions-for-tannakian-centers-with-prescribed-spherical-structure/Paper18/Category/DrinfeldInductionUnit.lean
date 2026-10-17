import Paper18.Category.DrinfeldInductionNaturality

/-! # The unit equation for the actual central-induction commutation maps -/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

lemma unitCoevaluation_eq : η_ (𝟙_ C) (dual C (𝟙_ C)) =
    (dualUnitIso (C := C)).inv ≫ (λ_ (dual C (𝟙_ C))).inv := by
  rw [dualUnitIso_inv]
  dsimp [dualUnitFrom]
  simp

lemma pivotalMap_unit (J : PivotalStructure C) :
    pivotalMap J (𝟙_ C) =
      (dualUnitIso (C := C)).inv ≫ dualMap C (dualUnitIso (C := C)).hom := by
  change J.j.hom.app (𝟙_ C) = _
  rw [J.unit, dualUnitIso_inv, dualUnitIso_hom]
  rfl

lemma rigidInsertion_unit (J : PivotalStructure C) (A : C) :
    rigidInsertion J (𝟙_ C) A =
      𝟙 (A ⊗ (𝟙_ C)) ⊗≫ (dualUnitIso (C := C)).inv ▷ A ⊗≫
        (dual C (𝟙_ C) ⊗ A) ◁
          ((dualUnitIso (C := C)).inv ≫ dualMap C (dualUnitIso (C := C)).hom) ⊗≫
        𝟙 ((𝟙_ C) ⊗ ((dual C (𝟙_ C) ⊗ A) ⊗ dual C (dual C (𝟙_ C)))) := by
  dsimp only [rigidInsertion]
  rw [unitCoevaluation_eq, pivotalMap_unit]
  monoidal

/-- The canonical tensor dual comparison at the unit reduces the pivotal
unit strand to the mate of the actual unit-identification map. -/
lemma inductionUnitDualComparison (T : C) :
    (dual C T ◁ ((dualUnitIso (C := C)).inv ≫
      dualMap C (dualUnitIso (C := C)).hom)) ≫
        (dualTensorIso (dual C (𝟙_ C)) T).inv =
      (ρ_ (dual C T)).hom ≫
        dualMap C (((dualUnitIso (C := C)).hom ▷ T) ≫ (λ_ T).hom) := by
  have hu : (dual C T ◁ (dualUnitIso (C := C)).inv) ≫
      (dualTensorIso (𝟙_ C) T).inv =
        (ρ_ (dual C T)).hom ≫ dualMap C (λ_ T).hom := by
    apply (cancel_mono (dualTensorIso (𝟙_ C) T).hom).mp
    rw [assoc, Iso.inv_hom_id, comp_id, assoc, dualTensorIso_leftUnitor]
    simp only [Iso.hom_inv_id_assoc]
  rw [whiskerLeft_comp, assoc, dualTensorIso_inv_naturality_left, ← assoc, hu, assoc]
  simp only [dualMap, comp_rightAdjointMate]

section Coend
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

lemma inductionHalfBraidingComponent_unit (J : PivotalStructure C) (X T : C) :
    inductionHalfBraidingComponent S J X (𝟙_ C) T =
      (ρ_ ((T ⊗ X) ⊗ dual C T)).hom ≫ inductionι S X T ≫
        (λ_ (inductionUnderlying S X)).inv := by
  let g : dual C (𝟙_ C) ⊗ T ⟶ T :=
    (dualUnitIso (C := C)).hom ▷ T ≫ (λ_ T).hom
  calc
    _ = 𝟙 (((T ⊗ X) ⊗ dual C T) ⊗ (𝟙_ C)) ⊗≫
        (dualUnitIso (C := C)).inv ▷ ((T ⊗ X) ⊗ dual C T) ⊗≫
        (((dual C (𝟙_ C) ⊗ T) ⊗ X) ◁
          ((dual C T ◁ ((dualUnitIso (C := C)).inv ≫
            dualMap C (dualUnitIso (C := C)).hom)) ≫
            (dualTensorIso (dual C (𝟙_ C)) T).inv)) ⊗≫
        inductionι S X (dual C (𝟙_ C) ⊗ T) ⊗≫
        𝟙 ((𝟙_ C) ⊗ inductionUnderlying S X) := by
      unfold inductionHalfBraidingComponent
      rw [rigidInsertion_unit]
      dsimp [inductionBraidingTail]
      monoidal
    _ = 𝟙 (((T ⊗ X) ⊗ dual C T) ⊗ (𝟙_ C)) ⊗≫
        (dualUnitIso (C := C)).inv ▷ ((T ⊗ X) ⊗ dual C T) ⊗≫
        ((((dual C (𝟙_ C) ⊗ T) ⊗ X) ◁ dualMap C g) ≫
          inductionι S X (dual C (𝟙_ C) ⊗ T)) ⊗≫
        𝟙 ((𝟙_ C) ⊗ inductionUnderlying S X) := by
      rw [inductionUnitDualComparison]
      dsimp [g]
      monoidal
    _ = 𝟙 (((T ⊗ X) ⊗ dual C T) ⊗ (𝟙_ C)) ⊗≫
        ((((dualUnitIso (C := C)).inv ≫ (dualUnitIso (C := C)).hom) ▷ T) ▷ X) ▷
          dual C T ⊗≫ inductionι S X T ⊗≫
        𝟙 ((𝟙_ C) ⊗ inductionUnderlying S X) := by
      rw [inductionι_dinatural]
      dsimp [g]
      monoidal
    _ = _ := by
      rw [Iso.inv_hom_id]
      simp only [id_whiskerRight]
      monoidal

/-- The actual coend commutation map has the required tensor-unit component. -/
lemma inductionHalfBraidingHom_unit (J : PivotalStructure C) (X : C) :
    inductionHalfBraidingHom S J X (𝟙_ C) =
      (ρ_ (inductionUnderlying S X)).hom ≫ (λ_ (inductionUnderlying S X)).inv := by
  letI := inductionHasCoend S X
  apply mappedCoend_hom_ext (inductionDiagram X) (tensorRight (𝟙_ C))
  intro T
  change (inductionι S X T ▷ (𝟙_ C)) ≫ _ = (inductionι S X T ▷ (𝟙_ C)) ≫ _
  rw [inductionHalfBraidingHom_ι, inductionHalfBraidingComponent_unit]
  rw [rightUnitor_naturality_assoc]

end Coend
end Paper18.Category.Drinfeld
