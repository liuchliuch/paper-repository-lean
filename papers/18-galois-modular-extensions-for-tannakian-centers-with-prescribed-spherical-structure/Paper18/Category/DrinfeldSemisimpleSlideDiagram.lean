import Paper18.Category.DrinfeldSemisimpleSlideDiagramCore
import Paper18.Category.DrinfeldSemisimpleSummation

/-! # Actual centrality slide for the weighted induction section -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- Closing the resolved slide returns the half-braiding of the two
adjacent strands followed by its actual endomorphism. -/
lemma averagingSlideEndMap_close (Z : Center C) (U B : C) (e : U ⊗ B ⟶ U ⊗ B) :
    averagingSlideClose U B Z.1 (averagingSlideEndMap Z U B e) =
      (α_ Z.1 U B).hom ≫ (Z.2.β (U ⊗ B)).hom ≫
        e ▷ Z.1 ≫ (α_ U B Z.1).hom := by
  let t : ((B ⊗ Z.1) ⊗ dual C B) ⊗ B ⟶ B ⊗ Z.1 :=
    (α_ (B ⊗ Z.1) (dual C B) B).hom ≫
      (B ⊗ Z.1) ◁ ε_ B (dual C B) ≫ (ρ_ (B ⊗ Z.1)).hom
  have ht : inductionSectionComponent Z B ▷ B ≫ t = (Z.2.β B).hom :=
    inductionSectionComponent_evaluation Z B
  calc
    _ = 𝟙 ((Z.1 ⊗ U) ⊗ B) ⊗≫ (Z.2.β U).hom ▷ B ⊗≫
        U ◁ (inductionSectionComponent Z B ▷ B) ⊗≫
        (e ▷ (Z.1 ⊗ (dual C B ⊗ B)) ≫
          (U ⊗ B) ◁ (Z.1 ◁ ε_ B (dual C B))) ⊗≫ 𝟙 (U ⊗ (B ⊗ Z.1)) := by
      rw [averagingSlideClose_eq]
      dsimp only [averagingSlideEndMap]
      monoidal
    _ = 𝟙 ((Z.1 ⊗ U) ⊗ B) ⊗≫ (Z.2.β U).hom ▷ B ⊗≫
        U ◁ (inductionSectionComponent Z B ▷ B ≫ t) ⊗≫
        e ▷ Z.1 ⊗≫ 𝟙 (U ⊗ (B ⊗ Z.1)) := by
      rw [← whisker_exchange]
      dsimp only [t]
      monoidal
    _ = _ := by
      rw [ht, Z.2.monoidal]
      monoidal

/-- The actual coend resolution slide, proved from rigidity and the
naturality of the given central object's half-braiding. -/
lemma averagingSlideMap_eq_endMap (J : PivotalStructure C) (Z : Center C) (U A B : C)
    (u : B ⟶ dual C U ⊗ A) (p : dual C U ⊗ A ⟶ B) :
    averagingSlideMap J Z U A B u p =
      averagingSlideEndMap Z U B
        (averagingRotationDown J U A B u ≫ averagingRotationUp U A B p) := by
  apply averagingSlideClose_injective U B Z.1
  have hmap : averagingSlideMap J Z U A B u p =
      averagingSlideCore J Z U A ≫
        U ◁ (((p ▷ Z.1) ▷ dual C (dual C U ⊗ A)) ≫
          (B ⊗ Z.1) ◁ dualMap C u) := by
    dsimp only [averagingSlideMap, averagingSlideCore]
    monoidal
  rw [hmap, averagingSlideClose_naturality, averagingSlideCore_close,
    averagingSlideEndMap_close]
  calc
    _ = (α_ Z.1 U B).hom ≫ Z.1 ◁ averagingRotationDown J U A B u ≫
        (Z.2.β A).hom ≫ averagingRotationUp U A B p ▷ Z.1 ≫
          (α_ U B Z.1).hom := by
      dsimp only [averagingRotationDown, averagingRotationUp]
      simp only [whiskerLeft_id]
      monoidal
    _ = _ := by
      rw [Z.2.naturality_assoc]
      simp only [comp_whiskerRight, assoc]

end Paper18.Category.Drinfeld
