import Paper18.Category.DrinfeldSemisimpleSlideDiagramBasic

/-! # Closing the actual central averaging core diagram -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The actual pivotal cap encountered when the tensor-dual comparison is closed. -/
def averagingSlideEvaluation (J : PivotalStructure C) (U A : C) :
    (dual C A ⊗ U) ⊗ (dual C U ⊗ A) ⟶ 𝟙_ C :=
  ((dual C A ◁ pivotalMap J U) ▷ (dual C U ⊗ A)) ≫
    (dualTensorIso (dual C U) A).inv ▷ (dual C U ⊗ A) ≫
      ε_ (dual C U ⊗ A) (dual C (dual C U ⊗ A))

lemma averagingSlideEvaluation_nested (J : PivotalStructure C) (U A : C) :
    averagingSlideEvaluation J U A =
      𝟙 ((dual C A ⊗ U) ⊗ (dual C U ⊗ A)) ⊗≫
        dual C A ◁ (J.leftEvaluation U ▷ A) ⊗≫
          ε_ A (dual C A) := by
  unfold averagingSlideEvaluation
  rw [dualTensorIso_inv_evaluation]
  dsimp only [tensorEvaluation, PivotalStructure.leftEvaluation, pivotalMap]
  monoidal

/-- The actual averaging diagram before resolving its new coend label. -/
def averagingSlideCore (J : PivotalStructure C) (Z : Center C) (U A : C) :
    Z.1 ⊗ U ⟶ U ⊗ (((dual C U ⊗ A) ⊗ Z.1) ⊗ dual C (dual C U ⊗ A)) :=
  (inductionSectionComponent Z A ▷ U) ≫
    rigidInsertion J U ((A ⊗ Z.1) ⊗ dual C A) ≫
      U ◁ inductionBraidingComparison Z.1 U A

/-- Closing its last dual strand yields precisely the downward rotation,
original half-braiding, and upward rotation. -/
lemma averagingSlideCore_close (J : PivotalStructure C) (Z : Center C) (U A : C) :
    averagingSlideClose U (dual C U ⊗ A) Z.1 (averagingSlideCore J Z U A) =
      (α_ Z.1 U (dual C U ⊗ A)).hom ≫
        Z.1 ◁ averagingRotationDown J U A (dual C U ⊗ A) (𝟙 _) ≫
        (Z.2.β A).hom ≫
        averagingRotationUp U A (dual C U ⊗ A) (𝟙 _) ▷ Z.1 ≫
          (α_ U (dual C U ⊗ A) Z.1).hom := by
  let K := dual C U ⊗ A
  let M := (A ⊗ Z.1) ⊗ dual C A
  let d : U ⊗ K ⟶ A := averagingRotationDown J U A K (𝟙 K)
  let c : A ⟶ U ⊗ K := averagingRotationUp U A K (𝟙 K)
  let t : M ⊗ A ⟶ A ⊗ Z.1 :=
    (α_ (A ⊗ Z.1) (dual C A) A).hom ≫
      (A ⊗ Z.1) ◁ ε_ A (dual C A) ≫ (ρ_ (A ⊗ Z.1)).hom
  have ht : inductionSectionComponent Z A ▷ A ≫ t = (Z.2.β A).hom :=
    inductionSectionComponent_evaluation Z A
  calc
    _ = 𝟙 ((Z.1 ⊗ U) ⊗ K) ⊗≫
        inductionSectionComponent Z A ▷ (U ⊗ K) ⊗≫
        η_ U (dual C U) ▷ (M ⊗ (U ⊗ K)) ⊗≫
        (U ⊗ (K ⊗ Z.1)) ◁ averagingSlideEvaluation J U A ⊗≫
          𝟙 (U ⊗ (K ⊗ Z.1)) := by
      rw [averagingSlideClose_eq]
      dsimp [averagingSlideCore, rigidInsertion, inductionBraidingComparison,
        averagingSlideEvaluation, K, M]
      monoidal
    _ = 𝟙 ((Z.1 ⊗ U) ⊗ K) ⊗≫
        inductionSectionComponent Z A ▷ (U ⊗ K) ⊗≫
        (η_ U (dual C U) ▷ (M ⊗ (U ⊗ K)) ≫
          (U ⊗ dual C U) ◁ (M ◁ d)) ⊗≫
        (U ⊗ dual C U) ◁ t ⊗≫ 𝟙 (U ⊗ (K ⊗ Z.1)) := by
      rw [averagingSlideEvaluation_nested]
      dsimp [d, t, averagingRotationDown, K, M]
      simp only [whiskerLeft_id]
      monoidal
    _ = 𝟙 ((Z.1 ⊗ U) ⊗ K) ⊗≫
        ((inductionSectionComponent Z A ▷ (U ⊗ K)) ≫ M ◁ d) ⊗≫
        (η_ U (dual C U) ▷ (M ⊗ A) ≫ (U ⊗ dual C U) ◁ t) ⊗≫
          𝟙 (U ⊗ (K ⊗ Z.1)) := by
      rw [← whisker_exchange]
      monoidal
    _ = (α_ Z.1 U K).hom ≫ Z.1 ◁ d ≫
        (inductionSectionComponent Z A ▷ A ≫ t) ≫
          c ▷ Z.1 ≫ (α_ U K Z.1).hom := by
      rw [← whisker_exchange, ← whisker_exchange]
      dsimp [c, averagingRotationUp, K, M]
      simp only [whiskerLeft_id]
      monoidal
    _ = _ := by rw [ht]

end Paper18.Category.Drinfeld
