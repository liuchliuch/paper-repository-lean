import Paper18.Category.DrinfeldCoendModulesCapInterchange
import Paper18.Category.DrinfeldCoendModulesOrderedProduct

/-! # The actual tensor transpose of an annular cap composition -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
universe v u
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D]

/-- The actual cabled annular operator. -/
def annularTensor (X Y M : D) (hx : X ⊗ M ⟶ X ⊗ M) (hy : Y ⊗ M ⟶ Y ⊗ M) :
    (X ⊗ Y) ⊗ M ⟶ (X ⊗ Y) ⊗ M :=
  (α_ X Y M).hom ≫ X ◁ hy ≫ X ◁ (β_ Y M).hom ≫ (α_ X M Y).inv ≫
    hx ▷ Y ≫ (α_ X M Y).hom ≫ X ◁ (β_ Y M).inv ≫ (α_ X Y M).inv

/-- Capping the actual cabled operator is the actual composition of the
two cap operations. This is a generic rigid braided graph identity. -/
lemma capOf_annularTensor (X Y M : D)
    (hx : X ⊗ M ⟶ X ⊗ M) (hy : Y ⊗ M ⟶ Y ⊗ M) :
    orderedProductKernel X Y ▷ M ≫ capOf (X ⊗ Y) M (annularTensor X Y M hx hy) =
      (α_ (dual D X ⊗ X) (dual D Y ⊗ Y) M).hom ≫
        (dual D X ⊗ X) ◁ capOf Y M hy ≫ capOf X M hx := by
  calc
    _ = 𝟙 (((dual D X ⊗ X) ⊗ (dual D Y ⊗ Y)) ⊗ M) ⊗≫
        (β_ (dual D Y) (dual D X ⊗ X)).inv ▷ (Y ⊗ M) ⊗≫
        dual D Y ◁ ((dual D X ⊗ X) ◁ hy) ⊗≫
        dual D Y ◁ ((dual D X ⊗ X) ◁ (β_ Y M).hom) ⊗≫
        dual D Y ◁ ((dual D X ◁ hx) ▷ Y) ⊗≫
        dual D Y ◁ (((dual D X ⊗ X) ◁ (β_ Y M).inv) ≫
          ε_ X (dual D X) ▷ (Y ⊗ M)) ⊗≫ ε_ Y (dual D Y) ▷ M ⊗≫ 𝟙 M := by
      dsimp only [orderedProductKernel]
      simp only [comp_whiskerRight, assoc]
      rw [capOf_tensorDual]
      dsimp only [annularTensor, tensorEvaluation]
      simp only [braiding_tensor_right_inv]
      dsimp [tensorμ, reverseBraiding]
      monoidal
    _ = 𝟙 (((dual D X ⊗ X) ⊗ (dual D Y ⊗ Y)) ⊗ M) ⊗≫
        (β_ (dual D Y) (dual D X ⊗ X)).inv ▷ (Y ⊗ M) ⊗≫
        dual D Y ◁ ((dual D X ⊗ X) ◁ hy) ⊗≫
        dual D Y ◁ ((dual D X ⊗ X) ◁ (β_ Y M).hom) ⊗≫
        dual D Y ◁ ((dual D X ◁ hx) ▷ Y) ⊗≫
        dual D Y ◁ ((ε_ X (dual D X) ▷ (M ⊗ Y)) ≫
          (𝟙_ D) ◁ (β_ Y M).inv) ⊗≫ ε_ Y (dual D Y) ▷ M ⊗≫ 𝟙 M := by
      rw [whisker_exchange]
    _ = 𝟙 (((dual D X ⊗ X) ⊗ (dual D Y ⊗ Y)) ⊗ M) ⊗≫
        (β_ (dual D Y) (dual D X ⊗ X)).inv ▷ (Y ⊗ M) ⊗≫
        dual D Y ◁ ((dual D X ⊗ X) ◁ hy) ⊗≫
        dual D Y ◁ ((dual D X ⊗ X) ◁ (β_ Y M).hom) ⊗≫
        dual D Y ◁ (capOf X M hx ▷ Y) ⊗≫
        dual D Y ◁ (β_ Y M).inv ⊗≫ ε_ Y (dual D Y) ▷ M ⊗≫ 𝟙 M := by
      rw [capOf_def]
      monoidal
    _ = _ := by
      have ht := braided_cap_interchange
        (dual D X ⊗ X) (dual D Y) Y M (ε_ Y (dual D Y)) hy (capOf X M hx)
      convert ht using 1 <;> monoidal

end Paper18.Category.DrinfeldCoendModules
