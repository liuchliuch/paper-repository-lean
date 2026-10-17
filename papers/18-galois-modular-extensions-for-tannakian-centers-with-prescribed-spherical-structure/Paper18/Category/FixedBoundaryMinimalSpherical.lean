import Paper18.Category.FixedBoundaryMinimalClassification
import Paper18.Results.CategoricalProp22C2

/-! # Every actual minimal C₂ extension carries the prescribed spherical structure

The actual specified-boundary rigidity theorem is applied to the genuine
double-dual boundary pair. Its actual trivialization yields the pivotal
structure, and the original negative-boson exclusion proves sphericality.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (T : TannakianCenter C (Multiplicative (ZMod 2)))

/-- Every actual minimal extension has an actual spherical pivotal
structure extending the prescribed source structure. The fixed-boundary
comparison is constructed internally for the actual double-dual pair. -/
theorem spherical_extension_of_c2_minimal
    (J : PivotalStructure C) (hJ : J.Spherical) (hd : J.rightDim T.c2Generator = -1)
    (E : MinimalBraidedExtension.{v,u,w,v',u',w'} S) :
    ∃ K : PivotalStructure E.ambient, K.Spherical ∧ PreservesPivotal E.inclusion J K := by
  obtain ⟨b⟩ := FixedBoundary.minimalBoundary_trivializable S T E
    (pivotalBoundary E.inclusion J)
  exact spherical_extension_of_c2_boundary S T J hJ hd E b

end Paper18.Category
