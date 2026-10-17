import Paper18.Category.DrinfeldLoopTraceBasic

/-! # Actual annular components of the induction loop -/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The actual open annular diagram before its universal coend inclusion. -/
def inductionLoopOpenDiagram (J : PivotalStructure C) (T A : C) :
    (T ⊗ (𝟙_ C)) ⊗ dual C T ⟶
      ((dual C (dual C T) ⊗ A) ⊗ (𝟙_ C)) ⊗ dual C (dual C (dual C T) ⊗ A) :=
  𝟙 ((T ⊗ (𝟙_ C)) ⊗ dual C T) ⊗≫
    (T ◁ (η_ A (dual C A) ≫ (ρ_ A).inv ▷ dual C A)) ▷ dual C T ⊗≫
    T ◁ rigidInsertion J (dual C T) ((A ⊗ (𝟙_ C)) ⊗ dual C A) ⊗≫
    (T ⊗ dual C T) ◁ inductionBraidingComparison (𝟙_ C) (dual C T) A ⊗≫
    J.leftEvaluation T ▷
      (((dual C (dual C T) ⊗ A) ⊗ (𝟙_ C)) ⊗ dual C (dual C (dual C T) ⊗ A)) ⊗≫
      𝟙 (((dual C (dual C T) ⊗ A) ⊗ (𝟙_ C)) ⊗ dual C (dual C (dual C T) ⊗ A))

/-- A single actual annular matrix endomorphism. Its two matrix entries
are actual maps into and out of the double-dual tensor index. -/
def inductionLoopAnnularTerm (J : PivotalStructure C) (T A : C)
    (u : T ⟶ dual C (dual C T) ⊗ A) (p : dual C (dual C T) ⊗ A ⟶ T) :
    (T ⊗ (𝟙_ C)) ⊗ dual C T ⟶ (T ⊗ (𝟙_ C)) ⊗ dual C T :=
  inductionLoopOpenDiagram J T A ≫ ((p ▷ (𝟙_ C)) ▷ dual C (dual C (dual C T) ⊗ A)) ≫
    (T ⊗ (𝟙_ C)) ◁ dualMap C u

section Coend
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- The annular diagram is derived from the actual adjunction loop by
the proved forward cap identity and the actual coend half-braiding formula. -/
lemma inductionι_loop_open (T A : C) :
    inductionι S (𝟙_ C) T ≫ (inductionLoop S J A).f =
      inductionLoopOpenDiagram J T A ≫
        inductionι S (𝟙_ C) (dual C (dual C T) ⊗ A) := by
  rw [inductionLoop_f, inductionι_augmentation]
  calc
    _ = 𝟙 ((T ⊗ (𝟙_ C)) ⊗ dual C T) ⊗≫
        (T ◁ (η_ A (dual C A) ≫ (ρ_ A).inv ▷ dual C A)) ▷ dual C T ⊗≫
        T ◁ ((inductionι S (𝟙_ C) A ▷ dual C T) ≫
          inductionHalfBraidingHom S J (𝟙_ C) (dual C T)) ⊗≫
        J.leftEvaluation T ▷ inductionUnderlying S (𝟙_ C) ⊗≫
          𝟙 (inductionUnderlying S (𝟙_ C)) := by
      dsimp only [inductionAugmentationComponent, inductionCup]
      rw [← inductionAugmentationCap_forward]
      simp only [inductionObj_halfBraiding_hom]
      monoidal
    _ = _ := by
      rw [inductionHalfBraidingHom_ι]
      dsimp only [inductionHalfBraidingComponent]
      rw [← inductionBraidingComparison_ι]
      calc
        _ = 𝟙 ((T ⊗ (𝟙_ C)) ⊗ dual C T) ⊗≫
            (T ◁ (η_ A (dual C A) ≫ (ρ_ A).inv ▷ dual C A)) ▷ dual C T ⊗≫
            T ◁ rigidInsertion J (dual C T) ((A ⊗ (𝟙_ C)) ⊗ dual C A) ⊗≫
            (T ⊗ dual C T) ◁ inductionBraidingComparison (𝟙_ C) (dual C T) A ⊗≫
            (((T ⊗ dual C T) ◁ inductionι S (𝟙_ C) (dual C (dual C T) ⊗ A)) ≫
              J.leftEvaluation T ▷ inductionUnderlying S (𝟙_ C)) ⊗≫
              𝟙 (inductionUnderlying S (𝟙_ C)) := by monoidal
        _ = _ := by
          rw [whisker_exchange]
          dsimp only [inductionLoopOpenDiagram]
          monoidal

end Coend
end Paper18.Category.Drinfeld
