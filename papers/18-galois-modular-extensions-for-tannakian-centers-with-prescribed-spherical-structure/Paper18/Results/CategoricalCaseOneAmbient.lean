import Paper18.Results.CategoricalCaseOneTannakian
import Paper18.Results.CategoricalCentralizerTannakian
import Paper18.Category.NondegenerateExtension
import Paper18.Category.SemisimpleAbelian
import Paper18.Category.MonodromyWeakIntegrality

/-! # The actual ambient conclusion in Case 1

The Tannakian center of the actual ambient centralizer is constructed by
double centralizers. Case 1 integrality then gives the actual prescribed
modular extension on that ambient category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [BraidedCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D] [RightRigidCategory D] [Simple (𝟙_ D)]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ] (S : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Braided] [F.Full] [F.Faithful]
  {G : Type} [Group G] (T : TannakianCenter C G)

include T in
/-- Case 1 on the actual ambient centralizer. Its Tannakian center,
positive spherical structure, descended category and odd invertible are
all constructed by the preceding actual-category theorems. -/
theorem centralizer_integral_case_one
    (J : PivotalStructure D) (hJ : J.Spherical) (hD : IsNondegenerate (C := D)) :
    letI := S.fullSubcategoryHasKernels (centralizerProperty (Set.range F.obj))
    letI := S.fullSubcategoryRightRigid (centralizerProperty (Set.range F.obj))
    letI := S.fullSubcategorySimpleUnit (centralizerProperty (Set.range F.obj))
    ∀ {e : CentralizerCategory (Set.range F.obj)} (E : TensorInverse e)
    (he : e ⊗ e ≅ 𝟙_ (CentralizerCategory (Set.range F.obj)))
    (hI : (S.centralizerSkeleton (Set.range F.obj)).CentralizerIntegral {e}),
    let hweak := (S.centralizerSkeleton (Set.range F.obj)).weaklyIntegral_of_orderTwo_centralizerIntegral E he hI
    ∀ (hcenter : ∀ X ∈ mugerCenter (C := CentralizerCategory (Set.range F.obj)),
      ((S.centralizerPivotal (Set.range F.obj) J).ratio
        ((S.centralizerPivotal (Set.range F.obj) J).canonicalPositive
          (S.centralizerSkeleton (Set.range F.obj))
          (S.fullSubcategoryPivotal_spherical (centralizerProperty (Set.range F.obj)) J hJ)
          hweak)).hom.app X = 𝟙 X)
    (hd : (S.centralizerPivotal (Set.range F.obj) J).rightDim e = -1),
    S.CentralizerIntegral (Set.range F.obj) := by
  letI := S.fullSubcategoryHasKernels (centralizerProperty (Set.range F.obj))
  letI := S.fullSubcategoryRightRigid (centralizerProperty (Set.range F.obj))
  letI := S.fullSubcategorySimpleUnit (centralizerProperty (Set.range F.obj))
  letI := (S.centralizerSkeleton (Set.range F.obj)).abelian
  intro e E he hI hweak hcenter hd
  exact integral_case_one_canonical (S.centralizerSkeleton (Set.range F.obj))
    (S.centralizerPivotal (Set.range F.obj) J)
    (S.fullSubcategoryPivotal_spherical (centralizerProperty (Set.range F.obj)) J hJ)
    hweak (T.centralizerCenter F S J hD) hcenter E he hd hI

end Paper18.Category
