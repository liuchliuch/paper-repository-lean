import Paper18.Results.CategoricalProp22Minimal
import Paper18.Category.TannakianC2GeneratorBasic

/-! # The original C2-center interface for the spherical extension step -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (T : TannakianCenter C (Multiplicative (ZMod 2)))

/-- The actual C2-center supplies every order-two boson hypothesis. The
only remaining input is the actual fixed-boundary morphism whose existence
is the categorical assertion of Lemma A.1. -/
theorem spherical_extension_of_c2_boundary
    (J : PivotalStructure C) (hJ : J.Spherical) (hd : J.rightDim T.c2Generator = -1)
    (E : MinimalBraidedExtension.{v,u,w,v',u',w'} S)
    (b : BoundaryIso E.inclusion (pivotalBoundary E.inclusion J)
      (BoundaryAutoequivalence.identity E.inclusion)) :
    ∃ K : PivotalStructure E.ambient, K.Spherical ∧ PreservesPivotal E.inclusion J K :=
  spherical_of_minimal_pivotal_boundary S E.skeleton E.inclusion J hJ E.nondegenerate
    E.minimal T.c2GeneratorTensorInverse T.c2GeneratorSquareIso
    T.c2Generator_selfBraiding hd T.c2Generator_transparent b

end Paper18.Category
