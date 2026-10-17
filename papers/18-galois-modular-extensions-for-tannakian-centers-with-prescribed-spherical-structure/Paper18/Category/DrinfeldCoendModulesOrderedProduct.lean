import Paper18.Category.DrinfeldCoendModulesFamily
import Paper18.Category.RadfordDualBraiding

/-! # Ordering the actual coend product by actual dinaturality -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
universe v u
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D]

lemma dualTensorIso_inv_braiding_inv (X Y : D) :
    (dualTensorIso Y X).inv ≫ dualMap D (β_ Y X).inv =
      (β_ (dual D Y) (dual D X)).inv ≫ (dualTensorIso X Y).inv := by
  have he : dualMapIso (β_ Y X) ≪≫ dualTensorIso Y X =
      dualTensorIso X Y ≪≫ β_ (dual D Y) (dual D X) := by
    apply Iso.ext
    exact dualTensorIso_braiding Y X
  have hi := congrArg Iso.inv he
  exact hi

/-- The actual canonical product kernel in its multiplication order. -/
def productKernel (X Y : D) :
    (dual D X ⊗ X) ⊗ (dual D Y ⊗ Y) ⟶ dual D (Y ⊗ X) ⊗ (Y ⊗ X) :=
  @tensorμ D _ _ (reverseBraiding D) (dual D X) X (dual D Y) Y ≫
    ((dualTensorIso Y X).inv ⊗ₘ (β_ Y X).inv)

/-- The actual same product kernel with its coend label reordered. -/
def orderedProductKernel (X Y : D) :
    (dual D X ⊗ X) ⊗ (dual D Y ⊗ Y) ⟶ dual D (X ⊗ Y) ⊗ (X ⊗ Y) :=
  @tensorμ D _ _ (reverseBraiding D) (dual D X) X (dual D Y) Y ≫
    (β_ (dual D Y) (dual D X)).inv ▷ (X ⊗ Y) ≫
      (dualTensorIso X Y).inv ▷ (X ⊗ Y)

/-- Actual label naturality changes multiplication order into ordered
coend caps. This is the needed normalization in both directions. -/
lemma natural_cap_product_reindex (M : D) (h : ∀ T : D, T ⊗ M ⟶ T ⊗ M)
    (hn : ∀ {T U : D} (f : T ⟶ U), f ▷ M ≫ h U = h T ≫ f ▷ M)
    (X Y : D) :
    productKernel X Y ▷ M ≫ capOf (Y ⊗ X) M (h (Y ⊗ X)) =
      orderedProductKernel X Y ▷ M ≫ capOf (X ⊗ Y) M (h (X ⊗ Y)) := by
  have hd := capOf_dinaturality M h hn (β_ Y X).inv
  dsimp only [productKernel, orderedProductKernel]
  rw [MonoidalCategory.tensorHom_def, comp_whiskerRight, comp_whiskerRight]
  simp only [assoc]
  rw [← hd]
  have hc := congrArg (fun q => (q ▷ (X ⊗ Y)) ▷ M)
    (dualTensorIso_inv_braiding_inv X Y)
  simp only [comp_whiskerRight, assoc] at hc ⊢
  rw [reassoc_of% hc]

end Paper18.Category.DrinfeldCoendModules
