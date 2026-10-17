import Paper18.Category.SphericalizationGlobalDimensionPreimage
import Paper18.Category.CategoricalCentralizerGlobalDimensionUnit
import Paper18.Category.CategoricalCentralizerGlobalDimensionImage

/-! # The actual no-pivotal global dimension product for a nondegenerate extension -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {N : Type u} [Category.{v} N] [MonoidalCategory N] [RightRigidCategory N]
  [Preadditive N] [Linear ℂ N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [HasKernels N] [HasFiniteBiproducts N] [Simple (𝟙_ N)] [BraidedCategory N]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton N ι)
  {B : Type u'} [Category.{v'} B] [MonoidalCategory B] [RightRigidCategory B]
  [Preadditive B] [Linear ℂ B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
  [HasKernels B] [HasFiniteBiproducts B] [Simple (𝟙_ B)] [BraidedCategory B]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton B κ)
  (J : PivotalStructure B) (hJ : J.Positive)
  (F : B ⥤ N) [F.Braided] [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]

include J hJ

/-- No pivotal structure on the ambient extension is assumed. Actual positive
structures on the source and on its actual categorical centralizer give the
actual global-dimension product through the canonical sphericalization. -/
theorem canonical_globalDimension_extension_product (hN : IsNondegenerate (C := N))
    (K : letI := S.fullSubcategoryRightRigid (centralizerProperty (Set.range F.obj))
      PivotalStructure (CentralizerCategory (Set.range F.obj)))
    (hK : letI := S.fullSubcategoryRightRigid (centralizerProperty (Set.range F.obj))
      letI := S.fullSubcategoryHasKernels (centralizerProperty (Set.range F.obj))
      letI := S.fullSubcategorySimpleUnit (centralizerProperty (Set.range F.obj))
      K.Positive) :
    ((pivotalStructure (C := N)).pivotalData (skeleton S)).globalDimension =
      2 * (T.fusionBasis.totalFPdim : ℂ) * (S.centralizerFPdim (Set.range F.obj) : ℂ) := by
  let hSphere := J.spherical_of_positive T hJ
  let H := embedding T J hSphere F
  let P := centralizerProperty (Set.range F.obj)
  have hc : centralizerProperty (H.essImage : Set (Sphericalized N)) = preimageProperty P := by
    funext X
    apply propext
    change X ∈ centralizer (H.essImage : Set (Sphericalized N)) ↔
      forget.obj X ∈ centralizer (Set.range F.obj)
    rw [RelativeTensor.centralizer_essImage H]
    exact centralizer_forget_iso_iff F H (Iso.refl F) X
  have hi := supportGlobalDimension_essImage_of_positive T (skeleton S) H J
    (pivotalStructure (C := N)) (embedding_preservesPivotal T J hSphere F) hJ
  have hp := supportGlobalDimension_preimage_eq_twice_of_positive S P K hK
  have hu := embedding_transparent_globalDimension T J hSphere F S hN
  have he := (skeleton S).supportGlobalDimension_mul_centralizer_general pivotalStructure H.essImage
  rw [hi, hc, hp, hu, mul_one] at he
  rw [← he]
  change (T.fusionBasis.totalFPdim : ℂ) * (2 * (S.centralizerFPdim (Set.range F.obj) : ℂ)) = _
  ring

/-- The no-pivotal global dimension itself is the actual product of the
positive source and positive actual centralizer FP dimensions. -/
theorem noPivotalGlobalDimension_extension_product (hN : IsNondegenerate (C := N))
    (K : letI := S.fullSubcategoryRightRigid (centralizerProperty (Set.range F.obj))
      PivotalStructure (CentralizerCategory (Set.range F.obj)))
    (hK : letI := S.fullSubcategoryRightRigid (centralizerProperty (Set.range F.obj))
      letI := S.fullSubcategoryHasKernels (centralizerProperty (Set.range F.obj))
      letI := S.fullSubcategorySimpleUnit (centralizerProperty (Set.range F.obj))
      K.Positive) :
    noPivotalGlobalDimension S =
      (T.fusionBasis.totalFPdim : ℂ) * (S.centralizerFPdim (Set.range F.obj) : ℂ) := by
  unfold noPivotalGlobalDimension
  rw [canonical_globalDimension_extension_product S T J hJ F hN K hK]
  ring

end Paper18.Category.Sphericalized
