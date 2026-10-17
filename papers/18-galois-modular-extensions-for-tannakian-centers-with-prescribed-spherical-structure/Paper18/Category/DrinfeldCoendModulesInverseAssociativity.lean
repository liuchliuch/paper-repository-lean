import Paper18.Category.DrinfeldCoendModulesInverseBasic
import Paper18.Category.DrinfeldCoendModulesAlgebraProduct

/-! # Actual module associativity on the specified coend cap generators -/
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

/-- The actual module multiplication law restricts to the actual product
of arbitrary cap generators. -/
lemma moduleCap_tensor (M : Mod_ D (algebra S)) (X Y : D) :
    (@tensorμ D _ _ (reverseBraiding D) (dual D X) X (dual D Y) Y ≫
        ((dualTensorIso Y X).inv ⊗ₘ (β_ Y X).inv)) ▷ M.X ≫ moduleCap S M (Y ⊗ X) =
      (α_ (dual D X ⊗ X) (dual D Y ⊗ Y) M.X).hom ≫
        (dual D X ⊗ X) ◁ moduleCap S M Y ≫ moduleCap S M X := by
  have hm : μ[algebra S] ▷ M.X ≫ γ[algebra S,M.X] =
      (α_ (algebra S) (algebra S) M.X).hom ≫
        algebra S ◁ γ[algebra S,M.X] ≫ γ[algebra S,M.X] := ModObj.mul_smul (M := algebra S) M.X
  dsimp only [moduleCap]
  rw [← comp_whiskerRight_assoc, assoc, ← injection_mul S X Y,
    comp_whiskerRight_assoc, hm]
  rw [MonoidalCategory.tensorHom_def, comp_whiskerRight]
  simp only [assoc]
  rw [associator_naturality_middle_assoc, associator_naturality_left_assoc,
    ← whiskerLeft_comp_assoc, ← whisker_exchange_assoc]

end Paper18.Category.DrinfeldCoendModules
