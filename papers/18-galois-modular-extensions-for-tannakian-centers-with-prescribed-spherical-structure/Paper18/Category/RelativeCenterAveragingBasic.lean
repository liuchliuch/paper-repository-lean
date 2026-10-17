import Paper18.Category.RelativeCenterExact
import Paper18.Category.DrinfeldSemisimpleSlideDiagram

/-! # Actual cups and caps for averaging relative half-braidings -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.RelativeCenter
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {P : ObjectProperty C} [P.IsMonoidal]

/-- Insert an actual right cup and apply the actual relative half-braiding. -/
def sectionComponent (Z : RelativeCenter P) (T : C) (hT : P T) :
    Z.1 ⟶ (T ⊗ Z.1) ⊗ dual C T :=
  tensorRightHomEquiv Z.1 T (dual C T) (T ⊗ Z.1) (Z.2.β T hT).hom

lemma sectionComponent_eq (Z : RelativeCenter P) (T : C) (hT : P T) :
    sectionComponent Z T hT = (ρ_ Z.1).inv ≫ Z.1 ◁ η_ T (dual C T) ≫
      (α_ Z.1 T (dual C T)).inv ≫ (Z.2.β T hT).hom ▷ dual C T := by
  rfl

/-- The actual evaluation closure characterizes the relative cup component. -/
lemma sectionComponent_evaluation (Z : RelativeCenter P) (T : C) (hT : P T) :
    sectionComponent Z T hT ▷ T ≫ (α_ (T ⊗ Z.1) (dual C T) T).hom ≫
      (T ⊗ Z.1) ◁ ε_ T (dual C T) ≫ (ρ_ (T ⊗ Z.1)).hom = (Z.2.β T hT).hom :=
  (tensorRightHomEquiv Z.1 T (dual C T) (T ⊗ Z.1)).symm_apply_apply _

/-- Close a relative half-braiding by the actual pivotal left cap. -/
def augmentationCap (J : PivotalStructure C) (Z : RelativeCenter P) (T : C) (hT : P T) :
    (T ⊗ Z.1) ⊗ dual C T ⟶ Z.1 :=
  (Z.2.β T hT).inv ▷ dual C T ≫ (α_ Z.1 T (dual C T)).hom ≫
    Z.1 ◁ J.leftEvaluation T ≫ (ρ_ Z.1).hom

lemma sectionComponent_cap (J : PivotalStructure C) (Z : RelativeCenter P) (T : C) (hT : P T) :
    sectionComponent Z T hT ≫ augmentationCap J Z T hT =
      (ρ_ Z.1).inv ≫ Z.1 ◁ J.rightDimension T ≫ (ρ_ Z.1).hom := by
  rw [sectionComponent_eq]
  dsimp only [augmentationCap, PivotalStructure.rightDimension, PivotalStructure.rightTrace]
  simp only [assoc, ← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, id_comp,
    Iso.inv_hom_id_assoc]
  monoidal

@[reassoc]
lemma sectionComponent_naturality {Z W : RelativeCenter P} (f : Z ⟶ W) (T : C) (hT : P T) :
    f.f ≫ sectionComponent W T hT = sectionComponent Z T hT ≫ ((T ◁ f.f) ▷ dual C T) := by
  rw [sectionComponent_eq, sectionComponent_eq]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left_assoc, ← comp_whiskerRight, f.comm T hT,
    comp_whiskerRight]
  simp only [assoc]

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι]

lemma sectionComponent_cap_scalar (J : PivotalStructure C) (Z : RelativeCenter P) (T : C) (hT : P T) :
    sectionComponent Z T hT ≫ augmentationCap J Z T hT = J.rightDim T • 𝟙 Z.1 := by
  rw [sectionComponent_cap, ← unitScalarEquiv_spec (J.rightDimension T)]
  simp only [PivotalStructure.rightDim, MonoidalLinear.whiskerLeft_smul,
    whiskerLeft_id, Linear.comp_smul, Linear.smul_comp, id_comp, Iso.inv_hom_id]

/-- The actual relative cup sum has support only in the given fusion subcategory. -/
def weightedSection (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C) (Z : RelativeCenter P) :
    Z.1 ⟶ Drinfeld.inductionUnderlying S Z.1 :=
  ∑ i, if hi : P (S.simpleObject i) then J.rightDim (dual C (S.simpleObject i)) •
    (sectionComponent Z (S.simpleObject i) hi ≫ Drinfeld.inductionι S Z.1 (S.simpleObject i)) else 0

/-- The actual cap on the finite simple diagonal, supported on the relative subcategory. -/
def augmentation (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)
    (Z : RelativeCenter P) {X : C} (f : X ⟶ Z.1) :
    Drinfeld.inductionUnderlying S X ⟶ Z.1 :=
  (Drinfeld.inductionUnderlyingIso S X).hom ≫ biproduct.desc (fun i =>
    if hi : P (S.simpleObject i) then ((S.simpleObject i ◁ f) ▷ dual C (S.simpleObject i)) ≫
      augmentationCap J Z (S.simpleObject i) hi else 0)

@[reassoc (attr := simp)]
lemma inductionι_augmentation_simple (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)
    (Z : RelativeCenter P) {X : C} (f : X ⟶ Z.1) (i : ι) :
    Drinfeld.inductionι S X (S.simpleObject i) ≫ augmentation S J Z f =
      if hi : P (S.simpleObject i) then ((S.simpleObject i ◁ f) ▷ dual C (S.simpleObject i)) ≫
        augmentationCap J Z (S.simpleObject i) hi else 0 := by
  have hi : Drinfeld.inductionι S X (S.simpleObject i) ≫
      (Drinfeld.inductionUnderlyingIso S X).hom =
        biproduct.ι (fun j => (S.simpleObject j ⊗ X) ⊗ dual C (S.simpleObject j)) i :=
    S.semisimpleCoendIso_ι_simple (Drinfeld.inductionDiagram X) i
  rw [augmentation, ← assoc, hi, biproduct.ι_desc]

lemma weightedSection_augmentation (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)
    (Z : RelativeCenter P) :
    weightedSection S J Z ≫ augmentation S J Z (𝟙 Z.1) = S.supportGlobalDimension J P • 𝟙 Z.1 := by
  rw [weightedSection, Preadditive.sum_comp, S.supportGlobalDimension_eq, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : P (S.simpleObject i)
  · rw [dif_pos hi, Linear.smul_comp, assoc, inductionι_augmentation_simple, dif_pos hi]
    rw [whiskerLeft_id, id_whiskerRight, id_comp, sectionComponent_cap_scalar, smul_smul,
      J.rightDim_iso (S.dualIso i).symm, if_pos hi]
  · simp only [dif_neg hi, zero_comp, if_neg hi, zero_smul]

end Paper18.Category.RelativeCenter
