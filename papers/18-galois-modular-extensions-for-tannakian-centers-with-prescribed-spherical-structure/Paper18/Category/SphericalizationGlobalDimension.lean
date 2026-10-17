import Paper18.Category.SphericalizationGlobalDimensionExtension
import Paper18.Category.CategoricalCentralizerFPProduct
import Paper18.Category.ENOPseudounitaryWithoutPivotal

/-! # Positive pivotal existence for a nondegenerate extension

Actual positive structures on the source and its actual centralizer imply
positivity of the ambient category. The ambient pivotal structure is
constructed only after the canonical sphericalization global dimension is
proved equal to its FP dimension.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category
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
  (hN : IsNondegenerate (C := N))
  (K : letI := S.fullSubcategoryRightRigid (centralizerProperty (Set.range F.obj))
    PivotalStructure (CentralizerCategory (Set.range F.obj)))
  (hK : letI := S.fullSubcategoryRightRigid (centralizerProperty (Set.range F.obj))
    letI := S.fullSubcategoryHasKernels (centralizerProperty (Set.range F.obj))
    letI := S.fullSubcategorySimpleUnit (centralizerProperty (Set.range F.obj))
    K.Positive)

include T J hJ F hN K hK in
/-- The actual source/centralizer hypotheses force the canonical
sphericalization dimension equality, without any ambient pivotal input. -/
theorem Sphericalized.canonical_globalDimension_eq_FPdim_of_positive_extension :
    ((Sphericalized.pivotalStructure (C := N)).pivotalData (Sphericalized.skeleton S)).globalDimension.re =
      (Sphericalized.skeleton S).fusionBasis.totalFPdim := by
  let hSphere := J.spherical_of_positive T hJ
  let H := Sphericalized.embedding T J hSphere F
  have hfp := (Sphericalized.skeleton S).image_centralizerFPdim_mul T H
    (Sphericalized.pivotalStructure (C := N))
  rw [Sphericalized.centralizerFPdim_eq_twice S F H (Iso.refl F),
    Sphericalized.embedding_transparent_FPdim T J hSphere F S hN, mul_one] at hfp
  rw [Sphericalized.canonical_globalDimension_extension_product S T J hJ F hN K hK]
  calc
    _ = T.fusionBasis.totalFPdim * (2 * S.centralizerFPdim (Set.range F.obj)) := by
      norm_num [Complex.mul_re] <;> ring
    _ = _ := hfp

namespace FiniteSemisimpleSkeleton
include T J hJ F hN K hK

/-- Literal positive-existence conclusion: an actual nondegenerate braided
extension of a positive category with positive actual centralizer admits an
actual positive pivotal structure. No pivotal structure on the extension,
global-dimension equality, or dimension product is an input. -/
theorem exists_positive_of_positive_source_centralizer :
    ∃ L : PivotalStructure N, L.Positive :=
  S.exists_positive_of_sphericalizationGlobalEq
    (Sphericalized.canonical_globalDimension_eq_FPdim_of_positive_extension S T J hJ F hN K hK)

end FiniteSemisimpleSkeleton
end Paper18.Category
