import Paper18.Category.PivotalConjugate
import Paper18.Category.SphericalComparison
import Paper18.Category.PivotalDimensionFusion

/-!
# The slope as an actual tensor automorphism

The quotient of a pivotal structure and its Radford conjugate is a monoidal
natural automorphism of the identity. Its simple components are the dimension
ratios in Lemma 2.1. Multiplication of those ratios on fusion constituents is
therefore derived from categorical naturality and tensor coherence.
-/
noncomputable section
open Classical
universe v u w
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual

namespace PivotalStructure
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C] (J : PivotalStructure C)

/-- The categorical slope of a pivotal structure. -/
def slope : 𝟭 C ≅ 𝟭 C := J.ratio J.conjugate

instance slope_isMonoidal : NatTrans.IsMonoidal J.slope.hom := by
  dsimp only [slope]
  infer_instance

variable [Preadditive C] [Linear ℂ C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [Simple (𝟙_ C)]

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
lemma conjugate_rightDim (X : C) : J.conjugate.rightDim X = J.leftDim X :=
  congrArg (unitScalarEquiv (C := C)) (J.conjugate_rightDimension X)

lemma conjugate_rightDim_dual (X : C) :
    J.conjugate.rightDim X = J.rightDim (dual C X) := by
  rw [J.conjugate_rightDim, J.rightDim_dual]

variable [HasFiniteBiproducts C] {ι : Type w} [Fintype ι]
  (S : FiniteSemisimpleSkeleton C ι)
include S

/-- The Schur scalar of the actual slope component is the ratio of right
dimensions of the object and its chosen rigid dual. -/
lemma slope_scalar (X : C) [Simple X] :
    TensorAutomorphism.scalar J.slope X = J.rightDim X / J.rightDim (dual C X) := by
  change J.comparisonScalar J.conjugate X = _
  rw [J.comparisonScalar_eq_dimension_ratio J.conjugate S,
    J.conjugate_rightDim_dual]

/-- The numerical slope appearing in the paper is extracted from the actual
monoidal natural automorphism, with no character law assumed. -/
lemma slope_scalar_gamma (i : ι) :
    TensorAutomorphism.scalar J.slope (S.simpleObject i) = (J.pivotalData S).gamma i := by
  rw [J.slope_scalar S]
  change J.rightDim (S.simpleObject i) / J.rightDim (dual C (S.simpleObject i)) =
    J.rightDim (S.simpleObject i) / J.rightDim (S.simpleObject (S.dualLabel i))
  rw [J.rightDim_iso (S.dualIso i)]

/-- An actual slope component on a simple is the dimension ratio times its
identity morphism. -/
lemma slope_hom_app_simple (X : C) [Simple X] :
    J.slope.hom.app X = (J.rightDim X / J.rightDim (dual C X)) • 𝟙 X := by
  rw [← TensorAutomorphism.scalar_spec J.slope X, J.slope_scalar S]

/-- The ratio is multiplicative on every actual fusion constituent, proved
by applying naturality of the categorical slope to a nonzero constituent map. -/
lemma gamma_fusion (i j k : ι) (h : 0 < S.fusionCoeff i j k) :
    (J.pivotalData S).gamma k =
      (J.pivotalData S).gamma i * (J.pivotalData S).gamma j := by
  simpa only [J.slope_scalar_gamma S] using
    TensorAutomorphism.scalar_fusion J.slope S i j k h

/-- Vanishing of the categorical slope is equivalent to actual sphericality
on every endomorphism. -/
theorem slope_eq_refl_iff_spherical : J.slope = Iso.refl (𝟭 C) ↔ J.Spherical := by
  constructor
  · intro h
    apply (J.pivotalData_spherical_iff S).mp
    intro i
    rw [← J.slope_scalar_gamma S, h, TensorAutomorphism.scalar_refl]
  · intro h
    apply TensorAutomorphism.ext_simple J.slope (Iso.refl (𝟭 C)) S
    intro i
    rw [J.slope_scalar_gamma S, TensorAutomorphism.scalar_refl]
    exact J.pivotalData_spherical S h i

end PivotalStructure
end Paper18.Category
