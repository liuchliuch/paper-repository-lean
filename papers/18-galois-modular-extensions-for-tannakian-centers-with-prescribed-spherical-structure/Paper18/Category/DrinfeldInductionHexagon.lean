import Paper18.Category.DrinfeldInductionTensor

/-! # The tensor hexagon for the actual central-induction maps -/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The comparison preceding the actual induction coend inclusion. -/
def inductionBraidingComparison (X U T : C) :
    (dual C U ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗ dual C (dual C U) ⟶
      ((dual C U ⊗ T) ⊗ X) ⊗ dual C (dual C U ⊗ T) :=
  𝟙 ((dual C U ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗ dual C (dual C U)) ⊗≫
    ((dual C U ⊗ T) ⊗ X) ◁ (dualTensorIso (dual C U) T).inv

section Coend
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

lemma inductionBraidingComparison_ι (X U T : C) :
    inductionBraidingComparison X U T ≫ inductionι S X (dual C U ⊗ T) =
      inductionBraidingTail S X U T := by
  dsimp only [inductionBraidingComparison, inductionBraidingTail]
  monoidal

/-- The two tails agree by the genuine dinaturality relation at the canonical
index comparison, together with associativity of the chosen duals. -/
lemma inductionBraidingTail_tensor (X U V T : C) :
    rigidInsertionTensorTail U V ((T ⊗ X) ⊗ dual C T) ≫
        inductionBraidingTail S X (U ⊗ V) T =
      ((dual C V ◁ inductionBraidingComparison X U T) ▷ dual C (dual C V)) ≫
        inductionBraidingTail S X V (dual C U ⊗ T) := by
  let k : dual C V ⊗ (dual C U ⊗ T) ⟶ dual C (U ⊗ V) ⊗ T :=
    (α_ (dual C V) (dual C U) T).inv ≫ (dualTensorIso U V).inv ▷ T
  let d : dual C T ⊗ (dual C (dual C U) ⊗ dual C (dual C V)) ⟶
      dual C (dual C (U ⊗ V) ⊗ T) :=
    dual C T ◁ doubleDualTensorMap U V ≫
      (dualTensorIso (dual C (U ⊗ V)) T).inv
  calc
    _ = 𝟙 ((dual C V ⊗ ((dual C U ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗
        dual C (dual C U))) ⊗ dual C (dual C V)) ⊗≫
        ((((k ▷ X) ▷ (dual C T ⊗ (dual C (dual C U) ⊗ dual C (dual C V))))) ≫
          ((dual C (U ⊗ V) ⊗ T) ⊗ X) ◁ d) ⊗≫
        inductionι S X (dual C (U ⊗ V) ⊗ T) := by
      dsimp only [rigidInsertionTensorTail, inductionBraidingTail, k, d]
      monoidal
    _ = 𝟙 ((dual C V ⊗ ((dual C U ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗
        dual C (dual C U))) ⊗ dual C (dual C V)) ⊗≫
        ((dual C V ⊗ (dual C U ⊗ T)) ⊗ X) ◁ d ⊗≫
        (((k ▷ X) ▷ dual C (dual C (U ⊗ V) ⊗ T)) ≫
          inductionι S X (dual C (U ⊗ V) ⊗ T)) := by
      rw [← whisker_exchange]
      monoidal
    _ = 𝟙 ((dual C V ⊗ ((dual C U ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗
        dual C (dual C U))) ⊗ dual C (dual C V)) ⊗≫
        ((dual C V ⊗ (dual C U ⊗ T)) ⊗ X) ◁ (d ≫ dualMap C k) ⊗≫
        inductionι S X (dual C V ⊗ (dual C U ⊗ T)) := by
      rw [← inductionι_dinatural]
      monoidal
    _ = _ := by
      have hd : (α_ (dual C T) (dual C (dual C U)) (dual C (dual C V))).hom ≫
          d ≫ dualMap C k =
          ((dualTensorIso (dual C U) T).inv ▷ dual C (dual C V)) ≫
            (dualTensorIso (dual C V) (dual C U ⊗ T)).inv := by
        dsimp only [d, k]
        simpa only [assoc] using (inductionTensorDualComparison U V T).symm
      calc
        _ = 𝟙 ((dual C V ⊗ ((dual C U ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗
            dual C (dual C U))) ⊗ dual C (dual C V)) ⊗≫
            ((dual C V ⊗ (dual C U ⊗ T)) ⊗ X) ◁
              ((α_ (dual C T) (dual C (dual C U)) (dual C (dual C V))).hom ≫
                d ≫ dualMap C k) ⊗≫
            inductionι S X (dual C V ⊗ (dual C U ⊗ T)) := by monoidal
        _ = _ := by
          rw [hd]
          dsimp only [inductionBraidingComparison, inductionBraidingTail]
          monoidal

lemma inductionHalfBraidingComponent_tensor (J : PivotalStructure C) (X U V T : C) :
    inductionHalfBraidingComponent S J X (U ⊗ V) T =
      𝟙 (((T ⊗ X) ⊗ dual C T) ⊗ (U ⊗ V)) ⊗≫
        inductionHalfBraidingComponent S J X U T ▷ V ⊗≫
        U ◁ inductionHalfBraidingHom S J X V ⊗≫
          𝟙 ((U ⊗ V) ⊗ inductionUnderlying S X) := by
  symm
  calc
    _ = 𝟙 (((T ⊗ X) ⊗ dual C T) ⊗ (U ⊗ V)) ⊗≫
        rigidInsertion J U ((T ⊗ X) ⊗ dual C T) ▷ V ⊗≫
        U ◁ (inductionBraidingComparison X U T ▷ V) ⊗≫
        U ◁ ((inductionι S X (dual C U ⊗ T) ▷ V) ≫
          inductionHalfBraidingHom S J X V) ⊗≫
          𝟙 ((U ⊗ V) ⊗ inductionUnderlying S X) := by
      dsimp only [inductionHalfBraidingComponent]
      rw [← inductionBraidingComparison_ι]
      monoidal
    _ = 𝟙 (((T ⊗ X) ⊗ dual C T) ⊗ (U ⊗ V)) ⊗≫
        rigidInsertion J U ((T ⊗ X) ⊗ dual C T) ▷ V ⊗≫
        U ◁ ((inductionBraidingComparison X U T ▷ V) ≫
          rigidInsertion J V (((dual C U ⊗ T) ⊗ X) ⊗ dual C (dual C U ⊗ T))) ⊗≫
        (U ⊗ V) ◁ inductionBraidingTail S X V (dual C U ⊗ T) ⊗≫
          𝟙 ((U ⊗ V) ⊗ inductionUnderlying S X) := by
      rw [inductionHalfBraidingHom_ι]
      dsimp only [inductionHalfBraidingComponent]
      monoidal
    _ = 𝟙 (((T ⊗ X) ⊗ dual C T) ⊗ (U ⊗ V)) ⊗≫
        rigidInsertion J U ((T ⊗ X) ⊗ dual C T) ▷ V ⊗≫
        U ◁ rigidInsertion J V ((dual C U ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗
          dual C (dual C U)) ⊗≫
        (U ⊗ V) ◁ (((dual C V ◁ inductionBraidingComparison X U T) ▷
          dual C (dual C V)) ≫ inductionBraidingTail S X V (dual C U ⊗ T)) ⊗≫
          𝟙 ((U ⊗ V) ⊗ inductionUnderlying S X) := by
      rw [rigidInsertion_naturality]
      monoidal
    _ = _ := by
      rw [← inductionBraidingTail_tensor]
      dsimp only [inductionHalfBraidingComponent]
      rw [rigidInsertion_tensor]
      monoidal

/-- The universal induction commutation maps satisfy the actual half-braiding
tensor hexagon. -/
lemma inductionHalfBraidingHom_tensor (J : PivotalStructure C) (X U V : C) :
    inductionHalfBraidingHom S J X (U ⊗ V) =
      (α_ (inductionUnderlying S X) U V).inv ≫
        (inductionHalfBraidingHom S J X U ▷ V) ≫
        (α_ U (inductionUnderlying S X) V).hom ≫
        U ◁ inductionHalfBraidingHom S J X V ≫
        (α_ U V (inductionUnderlying S X)).inv := by
  letI := inductionHasCoend S X
  apply mappedCoend_hom_ext (inductionDiagram X) (tensorRight (U ⊗ V))
  intro T
  change (inductionι S X T ▷ (U ⊗ V)) ≫ _ = (inductionι S X T ▷ (U ⊗ V)) ≫ _
  rw [inductionHalfBraidingHom_ι, inductionHalfBraidingComponent_tensor]
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
    inductionHalfBraidingHom_ι]
  monoidal

end Coend
end Paper18.Category.Drinfeld
