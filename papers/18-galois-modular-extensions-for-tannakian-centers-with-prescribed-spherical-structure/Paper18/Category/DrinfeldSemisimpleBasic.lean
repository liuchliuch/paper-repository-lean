import Paper18.Category.DrinfeldInductionAdjunctionFunctor
import Paper18.Category.PivotalDimensionFusion
import Paper18.Fusion.ComplexDimensions

/-!
# Actual cup components for averaging in the center

The components below are actual underlying morphisms. Closing them by the
actual induction counit computes a pivotal trace. Their weighted sum will
provide the normalized section once its centrality is proved.
-/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- Insert an actual cup, then use the inverse half-braiding to place the
central object between the two dual strands. -/
def inductionSectionComponent (Z : Center C) (T : C) :
    Z.1 ⟶ (T ⊗ Z.1) ⊗ dual C T :=
  𝟙 Z.1 ⊗≫ η_ T (dual C T) ▷ Z.1 ⊗≫
    T ◁ (Z.2.β (dual C T)).inv ⊗≫ 𝟙 ((T ⊗ Z.1) ⊗ dual C T)

omit [RightRigidCategory C] in
lemma halfBraiding_inv_unit {X : C} (b : HalfBraiding X) :
    (b.β (𝟙_ C)).inv = (λ_ X).hom ≫ (ρ_ X).inv := by
  apply (cancel_epi (b.β (𝟙_ C)).hom).mp
  rw [Iso.hom_inv_id, halfBraiding_unit]
  simp only [Iso.hom_inv_id, assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]

/-- Closing a cup component with the actual augmentation is the actual
right pivotal dimension acting on the central object. -/
lemma inductionSectionComponent_cap (J : PivotalStructure C) (Z : Center C) (T : C) :
    inductionSectionComponent Z T ≫ inductionAugmentationCap J Z T =
      (ρ_ Z.1).inv ≫ Z.1 ◁ J.rightDimension T ≫ (ρ_ Z.1).hom := by
  calc
    _ = 𝟙 Z.1 ⊗≫ (η_ T (dual C T) ▷ Z.1 ≫
        (Z.2.β (T ⊗ dual C T)).inv) ⊗≫
        Z.1 ◁ J.leftEvaluation T ⊗≫ 𝟙 Z.1 := by
      dsimp only [inductionSectionComponent, inductionAugmentationCap]
      rw [halfBraiding_inv_monoidal]
      monoidal
    _ = _ := by
      rw [halfBraiding_inv_naturality, halfBraiding_inv_unit]
      dsimp only [PivotalStructure.rightDimension, PivotalStructure.rightTrace]
      simp only [id_whiskerRight, id_comp]
      monoidal

section Linear
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

omit [HasFiniteBiproducts C] in
lemma inductionSectionComponent_cap_scalar (Z : Center C) (T : C) :
    inductionSectionComponent Z T ≫ inductionAugmentationCap J Z T =
      J.rightDim T • 𝟙 Z.1 := by
  rw [inductionSectionComponent_cap,
    ← unitScalarEquiv_spec (J.rightDimension T)]
  simp only [PivotalStructure.rightDim, MonoidalLinear.whiskerLeft_smul,
    whiskerLeft_id, Linear.comp_smul, Linear.smul_comp, id_comp, Iso.inv_hom_id]

/-- The unnormalized actual underlying section, weighted by the dual pivotal
dimensions. Centrality is a separate theorem to be derived. -/
def inductionWeightedSection (Z : Center C) : Z.1 ⟶ inductionUnderlying S Z.1 :=
  ∑ i, J.rightDim (dual C (S.simpleObject i)) •
    (inductionSectionComponent Z (S.simpleObject i) ≫ inductionι S Z.1 (S.simpleObject i))

/-- The actual counit closes the weighted cup sum to global categorical
dimension times the identity. -/
lemma inductionWeightedSection_counit (Z : Center C) :
    inductionWeightedSection S J Z ≫ (inductionCounit S J Z).f =
      (J.pivotalData S).globalDimension • 𝟙 Z.1 := by
  simp only [inductionWeightedSection, Preadditive.sum_comp, Linear.smul_comp,
    assoc, inductionCounit, inductionAugmentationHom_f, inductionι_augmentation,
    inductionAugmentationComponent, whiskerLeft_id, id_whiskerRight, id_comp,
    inductionSectionComponent_cap_scalar, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  change (∑ i, J.rightDim (dual C (S.simpleObject i)) * J.rightDim (S.simpleObject i)) =
    ∑ i, (J.pivotalData S).ndim i
  apply Finset.sum_congr rfl
  intro i hi
  rw [Paper18.PivotalData.ndim]
  change _ = J.rightDim (S.simpleObject i) * J.rightDim (S.simpleObject (S.dualLabel i))
  rw [J.rightDim_iso (S.dualIso i)]
  exact mul_comm _ _

/-- The global dimension used in normalization is derived to be nonzero
from actual pivotal dimensions of the finite semisimple category. -/
lemma inductionGlobalDimension_ne_zero : (J.pivotalData S).globalDimension ≠ 0 :=
  (J.pivotalData S).globalDimension_ne_zero

/-- Normalize the actual weighted cup sum by the proved nonzero global
dimension. At this stage it is an underlying morphism. -/
def inductionNormalizedSection (Z : Center C) : Z.1 ⟶ inductionUnderlying S Z.1 :=
  ((J.pivotalData S).globalDimension)⁻¹ • inductionWeightedSection S J Z

@[reassoc (attr := simp)]
lemma inductionNormalizedSection_counit (Z : Center C) :
    inductionNormalizedSection S J Z ≫ (inductionCounit S J Z).f = 𝟙 Z.1 := by
  rw [inductionNormalizedSection, Linear.smul_comp, inductionWeightedSection_counit,
    smul_smul, inv_mul_cancel₀ (inductionGlobalDimension_ne_zero S J), one_smul]

end Linear
end Paper18.Category.Drinfeld
