import Paper18.Category.LinearTensorMonoidal
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! # Actual duals in the linear tensor category -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe v u v' u'
namespace Paper18.Category.LinearTensor
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory C] [RightRigidCategory D]

local instance (priority := 2000) (X : C) : HasRightDual X :=
  RightRigidCategory.rightDual X
local instance (priority := 2000) (X : D) : HasRightDual X :=
  RightRigidCategory.rightDual X

def dualObject (X : LinearTensor C D) : LinearTensor C D := ⟨X.leftᘁ, X.rightᘁ⟩

instance exactPairing (X : LinearTensor C D) : ExactPairing X (dualObject X) where
  coevaluation' := (η_ X.left X.leftᘁ) ⊗ₜ[ℂ] (η_ X.right X.rightᘁ)
  evaluation' := (ε_ X.left X.leftᘁ) ⊗ₜ[ℂ] (ε_ X.right X.rightᘁ)
  coevaluation_evaluation' := by
    change ((𝟙 X.leftᘁ ⊗ₘ η_ X.left X.leftᘁ) ≫
        (α_ X.leftᘁ X.left X.leftᘁ).inv ≫
        (ε_ X.left X.leftᘁ ⊗ₘ 𝟙 X.leftᘁ)) ⊗ₜ[ℂ]
      ((𝟙 X.rightᘁ ⊗ₘ η_ X.right X.rightᘁ) ≫
        (α_ X.rightᘁ X.right X.rightᘁ).inv ≫
        (ε_ X.right X.rightᘁ ⊗ₘ 𝟙 X.rightᘁ)) =
      ((ρ_ X.leftᘁ).hom ≫ (λ_ X.leftᘁ).inv) ⊗ₜ[ℂ]
        ((ρ_ X.rightᘁ).hom ≫ (λ_ X.rightᘁ).inv)
    simpa only [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id] using
      congrArg₂ (TensorProduct.tmul ℂ)
        (ExactPairing.coevaluation_evaluation X.left X.leftᘁ)
        (ExactPairing.coevaluation_evaluation X.right X.rightᘁ)
  evaluation_coevaluation' := by
    change ((η_ X.left X.leftᘁ ⊗ₘ 𝟙 X.left) ≫
        (α_ X.left X.leftᘁ X.left).hom ≫
        (𝟙 X.left ⊗ₘ ε_ X.left X.leftᘁ)) ⊗ₜ[ℂ]
      ((η_ X.right X.rightᘁ ⊗ₘ 𝟙 X.right) ≫
        (α_ X.right X.rightᘁ X.right).hom ≫
        (𝟙 X.right ⊗ₘ ε_ X.right X.rightᘁ)) =
      ((λ_ X.left).hom ≫ (ρ_ X.left).inv) ⊗ₜ[ℂ]
        ((λ_ X.right).hom ≫ (ρ_ X.right).inv)
    simpa only [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id] using
      congrArg₂ (TensorProduct.tmul ℂ)
        (ExactPairing.evaluation_coevaluation X.left X.leftᘁ)
        (ExactPairing.evaluation_coevaluation X.right X.rightᘁ)

instance : RightRigidCategory (LinearTensor C D) where
  rightDual X := ⟨dualObject X⟩

end Paper18.Category.LinearTensor
