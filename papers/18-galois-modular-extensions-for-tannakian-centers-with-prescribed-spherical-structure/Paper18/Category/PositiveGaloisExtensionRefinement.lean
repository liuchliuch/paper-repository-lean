import Paper18.Category.PositiveGaloisExtension
import Paper18.Category.ENOPseudounitaryWithoutPivotal
import Paper18.Category.SphericalizationGlobalDimension

/-! # Actual positive structures for the Galois-extension refinement

The integral actual centralizer has an actual positive pivotal structure,
constructed without any ambient pivotal premise. Once the ambient positive
structure is constructed, its actual inclusion preserves the prescribed
source positive pivotal structure by uniqueness.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [RightRigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (E : GaloisBraidedExtension.{v,u,v',u',w'} C)

instance GaloisBraidedExtension.centralizerFiniteDimensional
    (X Y : CentralizerCategory (Set.range E.inclusion.obj)) :
    FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))

/-- Actual integrality constructs actual positive pivotal data for the
entire centralizer, with no pivotal structure on the ambient category. -/
theorem GaloisBraidedExtension.exists_positive_centralizer :
    letI := E.skeleton.fullSubcategoryHasKernels (centralizerProperty (Set.range E.inclusion.obj))
    letI := E.skeleton.fullSubcategoryRightRigid (centralizerProperty (Set.range E.inclusion.obj))
    letI := E.skeleton.fullSubcategorySimpleUnit (centralizerProperty (Set.range E.inclusion.obj))
    ∃ K : PivotalStructure (CentralizerCategory (Set.range E.inclusion.obj)), K.Positive := by
  letI := E.skeleton.fullSubcategoryHasKernels (centralizerProperty (Set.range E.inclusion.obj))
  letI := E.skeleton.fullSubcategoryRightRigid (centralizerProperty (Set.range E.inclusion.obj))
  letI := E.skeleton.fullSubcategorySimpleUnit (centralizerProperty (Set.range E.inclusion.obj))
  have h := (E.skeleton.centralizerSkeleton (Set.range E.inclusion.obj)).exists_unique_positive_of_integral_withoutPivotal E.integralCentralizer
  exact h.exists

/-- Actual source and ambient positivity force the required actual pivotal
comparison on the inclusion. This merely packages the constructed data. -/
def GaloisBraidedExtension.positiveRefinement
    (J : PivotalStructure C) (hJ : J.Positive)
    (K : PivotalStructure E.ambient) (hK : K.Positive) :
    PositiveGaloisExtension.{v,u,v',u',w'} J where
  toGaloisBraidedExtension := E
  pivotal := K
  positive := hK
  preserves := preservesPivotal_of_positive_fullyFaithful E.inclusion J K S E.skeleton hJ hK


include S E in
/-- The actual positive Galois refinement follows from actual integral
centralizer positivity and literal JF Proposition 2.4. The pivotal
structure on the fixed ambient category is constructed internally. -/
theorem GaloisBraidedExtension.exists_positiveRefinement
    (J : PivotalStructure C) (hJ : J.Positive) :
    Nonempty (PositiveGaloisExtension.{v,u,v',u',w'} J) := by
  letI := E.skeleton.fullSubcategoryHasKernels (centralizerProperty (Set.range E.inclusion.obj))
  letI := E.skeleton.fullSubcategoryRightRigid (centralizerProperty (Set.range E.inclusion.obj))
  letI := E.skeleton.fullSubcategorySimpleUnit (centralizerProperty (Set.range E.inclusion.obj))
  obtain ⟨K, hK⟩ := E.exists_positive_centralizer
  obtain ⟨L, hL⟩ := E.skeleton.exists_positive_of_positive_source_centralizer
    S J hJ E.inclusion E.nondegenerate K hK
  exact ⟨E.positiveRefinement S J hJ L hL⟩

end Paper18.Category
