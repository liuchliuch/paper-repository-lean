import Paper18.Category.RelativeCenterAveragingBasic

/-! # Actual reciprocal slide for relative half-braidings -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.RelativeCenter
open Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {P : ObjectProperty C} [P.IsMonoidal]

/-- The actual averaging diagram before resolving its new coend label. -/
def slideCore (J : PivotalStructure C) (Z : RelativeCenter P) (U A : C) (hA : P A) :
    Z.1 ⊗ U ⟶ U ⊗ (((dual C U ⊗ A) ⊗ Z.1) ⊗ dual C (dual C U ⊗ A)) :=
  (sectionComponent Z A hA ▷ U) ≫
    rigidInsertion J U ((A ⊗ Z.1) ⊗ dual C A) ≫
      U ◁ inductionBraidingComparison Z.1 U A

/-- Closing its last dual strand yields precisely the downward rotation,
original half-braiding, and upward rotation. -/
lemma slideCore_close (J : PivotalStructure C) (Z : RelativeCenter P) (U A : C) (hA : P A) :
    averagingSlideClose U (dual C U ⊗ A) Z.1 (slideCore J Z U A hA) =
      (α_ Z.1 U (dual C U ⊗ A)).hom ≫
        Z.1 ◁ averagingRotationDown J U A (dual C U ⊗ A) (𝟙 _) ≫
        (Z.2.β A hA).hom ≫
        averagingRotationUp U A (dual C U ⊗ A) (𝟙 _) ▷ Z.1 ≫
          (α_ U (dual C U ⊗ A) Z.1).hom := by
  let K := dual C U ⊗ A
  let M := (A ⊗ Z.1) ⊗ dual C A
  let d : U ⊗ K ⟶ A := averagingRotationDown J U A K (𝟙 K)
  let c : A ⟶ U ⊗ K := averagingRotationUp U A K (𝟙 K)
  let t : M ⊗ A ⟶ A ⊗ Z.1 :=
    (α_ (A ⊗ Z.1) (dual C A) A).hom ≫
      (A ⊗ Z.1) ◁ ε_ A (dual C A) ≫ (ρ_ (A ⊗ Z.1)).hom
  have ht : sectionComponent Z A hA ▷ A ≫ t = (Z.2.β A hA).hom :=
    sectionComponent_evaluation Z A hA
  calc
    _ = 𝟙 ((Z.1 ⊗ U) ⊗ K) ⊗≫
        sectionComponent Z A hA ▷ (U ⊗ K) ⊗≫
        η_ U (dual C U) ▷ (M ⊗ (U ⊗ K)) ⊗≫
        (U ⊗ (K ⊗ Z.1)) ◁ averagingSlideEvaluation J U A ⊗≫
          𝟙 (U ⊗ (K ⊗ Z.1)) := by
      rw [averagingSlideClose_eq]
      dsimp [slideCore, rigidInsertion, inductionBraidingComparison,
        averagingSlideEvaluation, K, M]
      monoidal
    _ = 𝟙 ((Z.1 ⊗ U) ⊗ K) ⊗≫
        sectionComponent Z A hA ▷ (U ⊗ K) ⊗≫
        (η_ U (dual C U) ▷ (M ⊗ (U ⊗ K)) ≫
          (U ⊗ dual C U) ◁ (M ◁ d)) ⊗≫
        (U ⊗ dual C U) ◁ t ⊗≫ 𝟙 (U ⊗ (K ⊗ Z.1)) := by
      rw [averagingSlideEvaluation_nested]
      dsimp [d, t, averagingRotationDown, K, M]
      simp only [whiskerLeft_id]
      monoidal
    _ = 𝟙 ((Z.1 ⊗ U) ⊗ K) ⊗≫
        ((sectionComponent Z A hA ▷ (U ⊗ K)) ≫ M ◁ d) ⊗≫
        (η_ U (dual C U) ▷ (M ⊗ A) ≫ (U ⊗ dual C U) ◁ t) ⊗≫
          𝟙 (U ⊗ (K ⊗ Z.1)) := by
      rw [← whisker_exchange]
      monoidal
    _ = (α_ Z.1 U K).hom ≫ Z.1 ◁ d ≫
        (sectionComponent Z A hA ▷ A ≫ t) ≫
          c ▷ Z.1 ≫ (α_ U K Z.1).hom := by
      rw [← whisker_exchange, ← whisker_exchange]
      dsimp [c, averagingRotationUp, K, M]
      simp only [whiskerLeft_id]
      monoidal
    _ = _ := by rw [ht]

/-- The individual actual diagram appearing after the reciprocal resolution
of the tensor-dual coend index. -/
def slideMap (J : PivotalStructure C) (Z : RelativeCenter P) (U A B : C) (hA : P A)
    (u : B ⟶ dual C U ⊗ A) (p : dual C U ⊗ A ⟶ B) :
    Z.1 ⊗ U ⟶ U ⊗ ((B ⊗ Z.1) ⊗ dual C B) :=
  𝟙 (Z.1 ⊗ U) ⊗≫ (sectionComponent Z A hA ▷ U) ⊗≫
    rigidInsertion J U ((A ⊗ Z.1) ⊗ dual C A) ⊗≫
    U ◁ inductionBraidingComparison Z.1 U A ⊗≫
    U ◁ (((p ▷ Z.1) ▷ dual C (dual C U ⊗ A)) ≫
      (B ⊗ Z.1) ◁ dualMap C u) ⊗≫ 𝟙 (U ⊗ ((B ⊗ Z.1) ⊗ dual C B))

/-- The resolved diagram after sliding, linear in the actual endomorphism
of the two adjacent strands. -/
def slideEndMap (Z : RelativeCenter P) (U B : C) (hU : P U) (hB : P B) (e : U ⊗ B ⟶ U ⊗ B) :
    Z.1 ⊗ U ⟶ U ⊗ ((B ⊗ Z.1) ⊗ dual C B) :=
  𝟙 (Z.1 ⊗ U) ⊗≫ (Z.2.β U hU).hom ⊗≫ U ◁ sectionComponent Z B hB ⊗≫
    (e ▷ Z.1) ▷ dual C B ⊗≫ 𝟙 (U ⊗ ((B ⊗ Z.1) ⊗ dual C B))

lemma slideEndMap_id (Z : RelativeCenter P) (U B : C) (hU : P U) (hB : P B) :
    slideEndMap Z U B hU hB (𝟙 (U ⊗ B)) =
      (Z.2.β U hU).hom ≫ U ◁ sectionComponent Z B hB := by
  dsimp only [slideEndMap]
  simp only [id_whiskerRight]
  monoidal

/-- Closing the resolved slide returns the half-braiding of the two
adjacent strands followed by its actual endomorphism. -/
lemma slideEndMap_close (Z : RelativeCenter P) (U B : C) (hU : P U) (hB : P B) (e : U ⊗ B ⟶ U ⊗ B) :
    averagingSlideClose U B Z.1 (slideEndMap Z U B hU hB e) =
      (α_ Z.1 U B).hom ≫ (Z.2.β (U ⊗ B) (ObjectProperty.prop_tensor hU hB)).hom ≫
        e ▷ Z.1 ≫ (α_ U B Z.1).hom := by
  let t : ((B ⊗ Z.1) ⊗ dual C B) ⊗ B ⟶ B ⊗ Z.1 :=
    (α_ (B ⊗ Z.1) (dual C B) B).hom ≫
      (B ⊗ Z.1) ◁ ε_ B (dual C B) ≫ (ρ_ (B ⊗ Z.1)).hom
  have ht : sectionComponent Z B hB ▷ B ≫ t = (Z.2.β B hB).hom :=
    sectionComponent_evaluation Z B hB
  calc
    _ = 𝟙 ((Z.1 ⊗ U) ⊗ B) ⊗≫ (Z.2.β U hU).hom ▷ B ⊗≫
        U ◁ (sectionComponent Z B hB ▷ B) ⊗≫
        (e ▷ (Z.1 ⊗ (dual C B ⊗ B)) ≫
          (U ⊗ B) ◁ (Z.1 ◁ ε_ B (dual C B))) ⊗≫ 𝟙 (U ⊗ (B ⊗ Z.1)) := by
      rw [averagingSlideClose_eq]
      dsimp only [slideEndMap]
      monoidal
    _ = 𝟙 ((Z.1 ⊗ U) ⊗ B) ⊗≫ (Z.2.β U hU).hom ▷ B ⊗≫
        U ◁ (sectionComponent Z B hB ▷ B ≫ t) ⊗≫
        e ▷ Z.1 ⊗≫ 𝟙 (U ⊗ (B ⊗ Z.1)) := by
      rw [← whisker_exchange]
      dsimp only [t]
      monoidal
    _ = _ := by
      rw [ht, Z.2.monoidal U B hU hB]
      monoidal

/-- The actual coend resolution slide, proved from rigidity and the
naturality of the given central object's half-braiding. -/
lemma slideMap_eq_endMap (J : PivotalStructure C) (Z : RelativeCenter P) (U A B : C) (hU : P U) (hA : P A) (hB : P B)
    (u : B ⟶ dual C U ⊗ A) (p : dual C U ⊗ A ⟶ B) :
    slideMap J Z U A B hA u p =
      slideEndMap Z U B hU hB
        (averagingRotationDown J U A B u ≫ averagingRotationUp U A B p) := by
  apply averagingSlideClose_injective U B Z.1
  have hmap : slideMap J Z U A B hA u p =
      slideCore J Z U A hA ≫
        U ◁ (((p ▷ Z.1) ▷ dual C (dual C U ⊗ A)) ≫
          (B ⊗ Z.1) ◁ dualMap C u) := by
    dsimp only [slideMap, slideCore]
    monoidal
  rw [hmap, averagingSlideClose_naturality, slideCore_close (hA := hA),
    slideEndMap_close (hU := hU) (hB := hB)]
  calc
    _ = (α_ Z.1 U B).hom ≫ Z.1 ◁ averagingRotationDown J U A B u ≫
        (Z.2.β A hA).hom ≫ averagingRotationUp U A B p ▷ Z.1 ≫
          (α_ U B Z.1).hom := by
      dsimp only [averagingRotationDown, averagingRotationUp]
      simp only [whiskerLeft_id]
      monoidal
    _ = _ := by
      rw [Z.2.naturality_assoc (ObjectProperty.prop_tensor hU hB) hA]
      simp only [comp_whiskerRight, assoc]

end Paper18.Category.RelativeCenter
