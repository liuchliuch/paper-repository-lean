import Paper18.Category.LinearTensorMonoidal
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # The componentwise braiding of the linear tensor category -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open scoped TensorProduct
universe v u v' u'
namespace Paper18.Category.LinearTensor
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] [BraidedCategory D]

instance : BraidedCategory (LinearTensor C D) where
  braiding X Y := isoOfPair (β_ X.left Y.left) (β_ X.right Y.right)
  braiding_naturality_right X {Y Z} f := by
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      change ((𝟙 X.left ⊗ₘ f) ≫ (β_ X.left Z.left).hom) ⊗ₜ[ℂ]
          ((𝟙 X.right ⊗ₘ g) ≫ (β_ X.right Z.right).hom) =
        ((β_ X.left Y.left).hom ≫ (f ⊗ₘ 𝟙 X.left)) ⊗ₜ[ℂ]
          ((β_ X.right Y.right).hom ≫ (g ⊗ₘ 𝟙 X.right))
      simp [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id]
    | add f g hf hg => simp_all [whiskerLeft_raw, whiskerRight_raw]
  braiding_naturality_left {X Y} f Z := by
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      change ((f ⊗ₘ 𝟙 Z.left) ≫ (β_ Y.left Z.left).hom) ⊗ₜ[ℂ]
          ((g ⊗ₘ 𝟙 Z.right) ≫ (β_ Y.right Z.right).hom) =
        ((β_ X.left Z.left).hom ≫ (𝟙 Z.left ⊗ₘ f)) ⊗ₜ[ℂ]
          ((β_ X.right Z.right).hom ≫ (𝟙 Z.right ⊗ₘ g))
      simp [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id]
    | add f g hf hg => simp_all [whiskerLeft_raw, whiskerRight_raw]
  hexagon_forward X Y Z := by
    change ((α_ X.left Y.left Z.left).hom ≫ (β_ X.left (Y.left ⊗ Z.left)).hom ≫
        (α_ Y.left Z.left X.left).hom) ⊗ₜ[ℂ]
      ((α_ X.right Y.right Z.right).hom ≫ (β_ X.right (Y.right ⊗ Z.right)).hom ≫
        (α_ Y.right Z.right X.right).hom) =
      (((β_ X.left Y.left).hom ⊗ₘ 𝟙 Z.left) ≫ (α_ Y.left X.left Z.left).hom ≫
        (𝟙 Y.left ⊗ₘ (β_ X.left Z.left).hom)) ⊗ₜ[ℂ]
      (((β_ X.right Y.right).hom ⊗ₘ 𝟙 Z.right) ≫ (α_ Y.right X.right Z.right).hom ≫
        (𝟙 Y.right ⊗ₘ (β_ X.right Z.right).hom))
    simpa only [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id] using
      congrArg₂ (TensorProduct.tmul ℂ) (BraidedCategory.hexagon_forward X.left Y.left Z.left)
        (BraidedCategory.hexagon_forward X.right Y.right Z.right)
  hexagon_reverse X Y Z := by
    change ((α_ X.left Y.left Z.left).inv ≫ (β_ (X.left ⊗ Y.left) Z.left).hom ≫
        (α_ Z.left X.left Y.left).inv) ⊗ₜ[ℂ]
      ((α_ X.right Y.right Z.right).inv ≫ (β_ (X.right ⊗ Y.right) Z.right).hom ≫
        (α_ Z.right X.right Y.right).inv) =
      ((𝟙 X.left ⊗ₘ (β_ Y.left Z.left).hom) ≫ (α_ X.left Z.left Y.left).inv ≫
        ((β_ X.left Z.left).hom ⊗ₘ 𝟙 Y.left)) ⊗ₜ[ℂ]
      ((𝟙 X.right ⊗ₘ (β_ Y.right Z.right).hom) ≫ (α_ X.right Z.right Y.right).inv ≫
        ((β_ X.right Z.right).hom ⊗ₘ 𝟙 Y.right))
    simpa only [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id] using
      congrArg₂ (TensorProduct.tmul ℂ) (BraidedCategory.hexagon_reverse X.left Y.left Z.left)
        (BraidedCategory.hexagon_reverse X.right Y.right Z.right)

end Paper18.Category.LinearTensor
