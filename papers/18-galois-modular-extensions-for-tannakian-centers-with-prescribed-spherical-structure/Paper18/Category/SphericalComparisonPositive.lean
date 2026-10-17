import Paper18.Category.SphericalComparison
import Paper18.Category.PivotalDimensionFusion

/-!
# Positive pivotal dimensions and the FP character

Positivity here is a property of the actual categorical trace. The comparison
with FP dimension is proved by uniqueness of a positive normalized character.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
namespace PivotalStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  (J K : PivotalStructure C)
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Positivity refers to the real scalar of the actual trace of each simple. -/
def Positive : Prop := ∀ X : C, Simple X → 0 < (J.rightDim X).re ∧ (J.rightDim X).im = 0

/-- Positive actual pivotal dimensions give a positive dimension character;
its tensor law is derived from the actual categorical trace. -/
def positiveDimension (h : J.Positive) : Paper18.FusionBasis.PositiveDimension S.fusionBasis where
  dim i := (J.rightDim (S.simpleObject i)).re
  pos i := (h _ (S.simple i)).1
  unit := by
    change (J.rightDim (S.simpleObject S.unitLabel)).re = 1
    rw [J.rightDim_iso S.unitIso, J.rightDim_unit S]
    rfl
  tensor i j := by
    have hm := congrArg Complex.re ((J.pivotalData S).jdim_tensor i j)
    have hr (k : ι) : (J.rightDim (S.simpleObject k)).im = 0 := (h _ (S.simple k)).2
    simpa [pivotalData, Complex.mul_re, hr] using hm.symm

/-- Positivity identifies each actual simple dimension with the FP dimension. -/
lemma rightDim_simple_eq_fpdim (h : J.Positive) (i : ι) :
    J.rightDim (S.simpleObject i) = (S.fusionBasis.fpdim i : ℂ) := by
  apply Complex.ext
  · exact (J.positiveDimension S h).eq_fpdim i
  · simpa using (h _ (S.simple i)).2

/-- The identification extends to every actual object by its categorical
biproduct decomposition. -/
lemma rightDim_eq_fpdim (h : J.Positive) (X : C) : J.rightDim X = (S.fpdim X : ℂ) := by
  rw [J.rightDim_eq_sum_multiplicity S X]
  simp only [J.rightDim_simple_eq_fpdim S h]
  simp [FiniteSemisimpleSkeleton.fpdim]

include S in
/-- A positive pivotal structure is spherical on every endomorphism. This
uses the proved rigid dual trace identity and actual simple decompositions. -/
lemma spherical_of_positive (h : J.Positive) : J.Spherical := by
  apply J.spherical_of_simple_dimensions S
  intro i
  calc
    J.leftDim (S.simpleObject i) = J.rightDim (dual C (S.simpleObject i)) :=
      (J.rightDim_dual _).symm
    _ = J.rightDim (S.simpleObject (S.dualLabel i)) :=
      (J.rightDim_iso (S.dualIso i)).symm
    _ = (S.fusionBasis.fpdim (S.dualLabel i) : ℂ) := J.rightDim_simple_eq_fpdim S h _
    _ = (S.fusionBasis.fpdim i : ℂ) := by
      rw [← S.fusionBasis_dual, S.fusionBasis.fpdim_dual]
    _ = J.rightDim (S.simpleObject i) := (J.rightDim_simple_eq_fpdim S h i).symm

/-- Relative to a positive spherical structure, every prescribed spherical
dimension is the FP dimension with the derived sign. -/
lemma rightDim_eq_sign_mul_fpdim (hK : K.Positive) (i : ι) :
    J.rightDim (S.simpleObject i) = J.comparisonScalar K (S.simpleObject i) *
      (S.fusionBasis.fpdim i : ℂ) := by
  rw [J.rightDim_comparison K, K.rightDim_simple_eq_fpdim S hK]

include S in
/-- Two positive spherical structures have comparison scalar one. -/
lemma comparisonScalar_eq_one_of_positive
    (hJ : J.Spherical) (hK : K.Spherical) (pJ : J.Positive) (pK : K.Positive)
    (X : C) [Simple X] : J.comparisonScalar K X = 1 := by
  rcases J.comparisonScalar_sign K S hJ hK X with hp | hn
  · exact hp
  · have hd := congrArg Complex.re (J.rightDim_comparison K X)
    rw [hn, neg_one_mul, Complex.neg_re] at hd
    have hj := (pJ X inferInstance).1
    have hk := (pK X inferInstance).1
    linarith

include S in
/-- Positive pivotal structure, when it exists, is unique as an actual
coherent natural isomorphism, not merely at the level of dimensions. -/
lemma eq_of_positive (pJ : J.Positive) (pK : K.Positive) : J = K := by
  apply J.eq_of_comparisonScalar_eq_one K S
  intro i
  exact J.comparisonScalar_eq_one_of_positive K S
    (J.spherical_of_positive S pJ) (K.spherical_of_positive S pK) pJ pK _

end PivotalStructure
end Paper18.Category
