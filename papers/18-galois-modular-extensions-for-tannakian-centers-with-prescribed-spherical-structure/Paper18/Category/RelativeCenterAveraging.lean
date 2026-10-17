import Paper18.Category.RelativeCenterAveragingSection
import Paper18.Category.RelativeCenterAugmentationCentral

/-! # Actual relative averaging and categorical splittings -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.RelativeCenter
open Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {P : ObjectProperty C} [P.IsMonoidal] [IsAdditiveFullProperty P]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

@[reassoc]
lemma weightedSection_naturality {Z W : RelativeCenter P} (f : Z ⟶ W) :
    f.f ≫ weightedSection S J W = weightedSection S J Z ≫ inductionUnderlyingMap S f.f := by
  simp only [weightedSection, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : P (S.simpleObject i)
  · simp only [dif_pos hi, Linear.comp_smul, Linear.smul_comp, assoc]
    rw [sectionComponent_naturality_assoc f _ hi, inductionUnderlyingMap_ι]
  · simp only [dif_neg hi, comp_zero, zero_comp]

def normalizedSection (Z : RelativeCenter P) : Z.1 ⟶ inductionUnderlying S Z.1 :=
  (S.supportGlobalDimension J P)⁻¹ • weightedSection S J Z

@[reassoc]
lemma normalizedSection_naturality {Z W : RelativeCenter P} (f : Z ⟶ W) :
    f.f ≫ normalizedSection S J W = normalizedSection S J Z ≫ inductionUnderlyingMap S f.f := by
  simp only [normalizedSection, Linear.comp_smul, Linear.smul_comp, weightedSection_naturality]

/-- The actual normalized relative section is an actual relative-central morphism. -/
def normalizedSectionHom (Z : RelativeCenter P) : Z ⟶ (restriction P).obj (inductionObj S J Z.1) where
  f := normalizedSection S J Z
  comm U hU := by
    change ((S.supportGlobalDimension J P)⁻¹ • weightedSection S J Z) ▷ U ≫
      inductionHalfBraidingHom S J Z.1 U = _
    simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp, weightedSection_central S J Z U hU,
      normalizedSection, MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]

@[reassoc]
lemma normalizedSection_augmentation (Z : RelativeCenter P) :
    normalizedSection S J Z ≫ augmentation S J Z (𝟙 Z.1) = 𝟙 Z.1 := by
  rw [normalizedSection, Linear.smul_comp, weightedSection_augmentation, smul_smul,
    inv_mul_cancel₀ (S.supportGlobalDimension_ne_zero J P), one_smul]

@[reassoc]
lemma normalizedSectionHom_augmentation (Z : RelativeCenter P) :
    normalizedSectionHom S J Z ≫ augmentationHom S J Z (𝟙 Z.1) = 𝟙 Z := by
  apply ext P
  exact normalizedSection_augmentation S J Z

/-- Every actual relative-central object is an actual retract of the
restriction of an actual ambient central-induction object. -/
def restrictionRetract (Z : RelativeCenter P) :
    Retract Z ((restriction P).obj (inductionObj S J Z.1)) where
  i := normalizedSectionHom S J Z
  r := augmentationHom S J Z (𝟙 Z.1)
  retract := normalizedSectionHom_augmentation S J Z

include S J in
/-- Restriction of actual ambient central objects is dominant onto the
actual relative center, by the constructed actual retract. -/
lemma restriction_dominant (Z : RelativeCenter P) :
    ∃ W : Center C, Nonempty (Retract Z ((restriction P).obj W)) :=
  ⟨inductionObj S J Z.1, ⟨restrictionRetract S J Z⟩⟩

/-- Actual relative averaging of an arbitrary underlying morphism. -/
def average {Z W : RelativeCenter P} (f : Z.1 ⟶ W.1) : Z ⟶ W :=
  normalizedSectionHom S J Z ≫ (restriction P).map ((inductionFunctor S J).map f) ≫
    augmentationHom S J W (𝟙 W.1)

@[simp]
lemma average_central_map {Z W : RelativeCenter P} (f : Z ⟶ W) : average S J f.f = f := by
  apply ext P
  change normalizedSection S J Z ≫ inductionUnderlyingMap S f.f ≫
    augmentation S J W (𝟙 W.1) = f.f
  rw [← normalizedSection_naturality_assoc S J f, normalizedSection_augmentation, comp_id]

/-- Every actual monomorphism in the relative center splits, by averaging
its actual underlying semisimple splitting. -/
def splitMono {Z W : RelativeCenter P} (f : Z ⟶ W) [Mono f] : SplitMono f := by
  letI : Mono f.f := inferInstanceAs (Mono ((forget P).map f))
  let s := S.splitMono f.f
  refine ⟨average S J s.retraction, ?_⟩
  apply ext P
  change f.f ≫ (normalizedSection S J W ≫ inductionUnderlyingMap S s.retraction ≫
    augmentation S J Z (𝟙 Z.1)) = 𝟙 Z.1
  calc
    _ = normalizedSection S J Z ≫ inductionUnderlyingMap S (f.f ≫ s.retraction) ≫
        augmentation S J Z (𝟙 Z.1) := by
      rw [normalizedSection_naturality_assoc S J f, inductionUnderlyingMap_comp, assoc]
    _ = _ := by
      rw [s.id, inductionUnderlyingMap_id, id_comp, normalizedSection_augmentation]

end Paper18.Category.RelativeCenter
