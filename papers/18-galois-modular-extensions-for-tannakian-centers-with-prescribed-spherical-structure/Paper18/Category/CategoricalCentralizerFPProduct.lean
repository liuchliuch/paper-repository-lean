import Paper18.Category.CategoricalCentralizerFPProductBasic
import Paper18.Category.DrinfeldSemisimple
import Paper18.Category.DrinfeldGeneralNondegenerate
import Paper18.Category.DrinfeldPivotal
import Paper18.Category.DrinfeldExact

/-!
# The general FP dimension product for an actual braided fusion image

The actual positive embedding into the actual Drinfeld center supplies a
nondegenerate ambient category. Its pivotal structure and complete finite
simple skeleton are constructed from the given actual pivotal source.
Transporting centralizer reciprocity gives the general product, including
the intersection with the actual Müger center. The embedded source needs
no pivotal structure, and the ambient category need not be nondegenerate.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {B : Type u'} [Category.{v'} B] [MonoidalCategory B] [RightRigidCategory B]
  [Preadditive B] [Linear ℂ B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
  [HasKernels B] [HasFiniteBiproducts B] [Simple (𝟙_ B)] [BraidedCategory B]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton B κ)
  (H : B ⥤ C) [H.Braided] [H.Additive] [H.Linear ℂ] [H.Full] [H.Faithful]

/-- The actual image-centralizer FP product in an arbitrary braided pivotal
fusion category. All support dimensions are computed from actual simples;
no image dimension, centralizer dimension, or nondegeneracy certificate
is supplied. The embedded source requires no pivotal structure. -/
theorem image_centralizerFPdim_mul (J : PivotalStructure C) :
    T.fusionBasis.totalFPdim * S.centralizerFPdim (Set.range H.obj) =
      S.fusionBasis.totalFPdim *
        S.supportFPdim (fun X => H.essImage X ∧ X ∈ mugerCenter) := by
  exact image_centralizerFPdim_mul_of_nondegenerate_embedding H (Drinfeld.positive C)
    S T (Drinfeld.centerSkeleton S J) (Drinfeld.centerPivotal J)
      (Drinfeld.center_nondegenerate S J)

end Paper18.Category.FiniteSemisimpleSkeleton
