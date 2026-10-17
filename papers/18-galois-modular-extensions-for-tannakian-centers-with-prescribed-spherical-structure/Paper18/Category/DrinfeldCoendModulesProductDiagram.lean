import Paper18.Category.DrinfeldCoendModulesBasic

/-! # The actual negative crossing cap identity for the coend product -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
universe v u
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D]

/-- The reverse crossing tensorator, followed by the reverse product cap,
is exactly the tensor product of the original actual caps. -/
lemma negative_tensor_cap (X Y : D) :
    @tensorμ D _ _ (reverseBraiding D) (dual D X) X (dual D Y) Y ≫
      (dual D X ⊗ dual D Y) ◁ (β_ Y X).inv ≫ tensorEvaluation D Y X =
      (ε_ X (dual D X) ⊗ₘ ε_ Y (dual D Y)) ≫ (λ_ (𝟙_ D)).hom := by
  calc
    _ = (α_ (dual D X) X (dual D Y ⊗ Y)).hom ≫
        dual D X ◁ ((β_ (dual D Y ⊗ Y) X).inv ≫
          ε_ Y (dual D Y) ▷ X ≫ (λ_ X).hom) ≫ ε_ X (dual D X) := by
      rw [braiding_tensor_left_inv]
      dsimp [tensorμ, reverseBraiding, tensorEvaluation]
      monoidal
    _ = (α_ (dual D X) X (dual D Y ⊗ Y)).hom ≫
        dual D X ◁ (X ◁ ε_ Y (dual D Y) ≫
          (β_ (𝟙_ D) X).inv ≫ (λ_ X).hom) ≫ ε_ X (dual D X) := by
      rw [← braiding_inv_naturality_right_assoc]
    _ = (dual D X ⊗ X) ◁ ε_ Y (dual D Y) ≫
        (ρ_ (dual D X ⊗ X)).hom ≫ ε_ X (dual D X) := by
      rw [braiding_inv_tensorUnit_left]
      monoidal
    _ = _ := by
      rw [← rightUnitor_naturality]
      rw [whisker_exchange_assoc]
      rw [← MonoidalCategory.tensorHom_def_assoc, unitors_equal]

end Paper18.Category.DrinfeldCoendModules
