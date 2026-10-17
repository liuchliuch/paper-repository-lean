import Paper18.Category.DrinfeldCoendModulesActionComponent
import Paper18.Category.RadfordDualBraiding

/-! # The annular component as its actual crossing and cap diagram -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
universe v u
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D]

/-- The transpose-normalized component is exactly the actual mixed
half-braiding/ambient-braiding cap diagram. -/
lemma actionComponent_cap (Z : Center D) (T : D) :
    actionComponent Z T =
      (α_ (dual D T) T Z.1).hom ≫ dual D T ◁ (Z.2.β T).inv ≫
        (α_ (dual D T) Z.1 T).inv ≫ (β_ (dual D T) Z.1).hom ▷ T ≫
          (α_ Z.1 (dual D T) T).hom ≫ Z.1 ◁ ε_ T (dual D T) ≫ (ρ_ Z.1).hom := by
  symm
  calc
    _ = (α_ (dual D T) T Z.1).hom ≫ dual D T ◁ (Z.2.β T).inv ≫
        (α_ (dual D T) Z.1 T).inv ≫
          (𝟙 ((dual D T ⊗ Z.1) ⊗ T) ⊗≫ (β_ (dual D T) Z.1).hom ▷ T ⊗≫
            Z.1 ◁ ε_ T (dual D T) ⊗≫ 𝟙 Z.1) := by monoidal
    _ = (α_ (dual D T) T Z.1).hom ≫ dual D T ◁ (Z.2.β T).inv ≫
        (α_ (dual D T) Z.1 T).inv ≫
          (𝟙 ((dual D T ⊗ Z.1) ⊗ T) ⊗≫ dual D T ◁ (β_ T Z.1).inv ⊗≫
            ε_ T (dual D T) ▷ Z.1 ⊗≫ 𝟙 Z.1) := by
      rw [braid_cap_slide_left]
    _ = _ := by
      rw [actionComponent_def]
      dsimp only [holonomy, Iso.trans_hom, Iso.symm_hom]
      monoidal

end Paper18.Category.DrinfeldCoendModules
