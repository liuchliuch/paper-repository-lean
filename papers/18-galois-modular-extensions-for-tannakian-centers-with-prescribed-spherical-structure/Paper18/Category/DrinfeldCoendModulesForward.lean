import Paper18.Category.DrinfeldCoendModulesAssociativityCriterion
import Paper18.Category.DrinfeldCoendModulesDoubleTensor
import Paper18.Category.DrinfeldCoendModulesAlgebraProduct
import Paper18.Category.DrinfeldCoendModulesHolonomy
import Paper18.Category.DrinfeldCoendModulesUnit

/-! # Actual central objects as modules for the actual coend algebra

The module laws follow from the actual cap multiplication and the actual
half-braiding hexagon. No module law is included as an input.
-/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [Simple (𝟙_ D)] in
/-- The actual central caps obey the actual product rule. -/
lemma actionComponent_mul (Z : Center D) (X Y : D) :
    productKernel X Y ▷ Z.1 ≫ actionComponent Z (Y ⊗ X) =
      (α_ (dual D X ⊗ X) (dual D Y ⊗ Y) Z.1).hom ≫
        (dual D X ⊗ X) ◁ actionComponent Z Y ≫ actionComponent Z X := by
  exact (cap_associativity_iff_tensor Z.1 (fun T => (holonomy Z T).hom)
    (holonomy_naturality Z) X Y).mpr (holonomy_tensor Z X Y)

/-- The actual annular action satisfies actual module associativity. -/
lemma action_mul (Z : Center D) :
    μ[algebra S] ▷ Z.1 ≫ action S Z =
      (α_ (algebra S) (algebra S) Z.1).hom ≫
        algebra S ◁ action S Z ≫ action S Z := by
  apply injection_double_tensor_hom_ext S
  intro X Y
  have hp : (injection S X ⊗ₘ injection S Y) ≫ μ[algebra S] =
      productKernel X Y ≫ injection S (Y ⊗ X) := by
    simpa only [productKernel, assoc] using injection_mul S X Y
  rw [← comp_whiskerRight_assoc, hp, comp_whiskerRight_assoc, injection_action]
  change productKernel X Y ▷ Z.1 ≫ actionComponent Z (Y ⊗ X) = _
  rw [actionComponent_mul]
  rw [MonoidalCategory.tensorHom_def, comp_whiskerRight]
  simp only [assoc]
  rw [associator_naturality_middle_assoc, associator_naturality_left_assoc,
    ← whiskerLeft_comp_assoc, ← whisker_exchange_assoc]
  simp only [injection_action]

/-- A central object carries an actual module structure for the actual
separable coend algebra. -/
def centralModObj (Z : Center D) : ModObj (algebra S) Z.1 where
  smul := action S Z
  one_smul' := action_one S Z
  mul_smul' := action_mul S Z

/-- The actual central object regarded as an actual internal module. -/
def toModulesObj (Z : Center D) : Mod_ D (algebra S) :=
  letI := centralModObj S Z
  ⟨Z.1⟩

end Paper18.Category.DrinfeldCoendModules
