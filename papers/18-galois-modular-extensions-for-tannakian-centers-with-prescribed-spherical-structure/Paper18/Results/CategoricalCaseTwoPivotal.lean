import Paper18.Category.SignKernel
import Paper18.Category.ModuleBalancingPositive
import Paper18.Results.CategoricalSigns

/-! # The inherited spherical structure is positive on the actual sign kernel -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J K : PivotalStructure C)

include S in
/-- The actual inherited pivotal structure on the actual positive kernel
has positive categorical dimensions. The inclusion's actual simplicity and
canonical pivotal comparison are used, with no positivity premise on the
inherited structure. -/
theorem ratio_positive_kernel_positive (hK : K.Positive) :
    letI := SignKernel.hasKernels (J.ratio K) S
    letI := SignKernel.rightRigid (J.ratio K) S
    letI := SignKernel.simpleUnit (J.ratio K) S
    (SignKernel.pivotal (J.ratio K) S J).Positive := by
  let χ := J.ratio K
  letI := SignKernel.hasKernels χ S
  letI := SignKernel.rightRigid χ S
  letI := SignKernel.simpleUnit χ S
  intro X hX
  letI := hX
  letI : Simple X.obj := S.simple_map (SignKernel.inclusion χ) X
  have hc : J.comparisonScalar K X.obj = 1 := by
    apply smul_left_injective ℂ (CategoryTheory.id_nonzero X.obj)
    exact (TensorAutomorphism.scalar_spec χ X.obj).trans
      (((SignKernel.mem_positive χ X.obj).mp X.property).trans (one_smul ℂ (𝟙 X.obj)).symm)
  have hd : J.rightDim X.obj = K.rightDim X.obj := by
    rw [J.rightDim_comparison K X.obj, hc, one_mul]
  have hp := SignKernel.inclusion_preservesPivotal χ S J
  have hx := hp.rightDim_scalar X
  change J.rightDim X.obj = (SignKernel.pivotal χ S J).rightDim X at hx
  change 0 < ((SignKernel.pivotal χ S J).rightDim X).re ∧
    ((SignKernel.pivotal χ S J).rightDim X).im = 0
  rw [← hx, hd]
  exact hK X.obj inferInstance

end Paper18.Category
