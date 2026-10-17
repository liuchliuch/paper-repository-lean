import Paper18.Category.DrinfeldCoendModulesInverseCrossing
import Paper18.Category.DrinfeldCoendModulesFamily

/-! # Actual coend generation detects the recovered annular crossings -/
noncomputable section
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

/-- Actual rigid transposition and cap generation jointly detect an
arbitrary map out of the internal coend tensored with an object. -/
lemma annularTranspose_hom_ext (M : D) {a b : algebra S ⊗ M ⟶ M}
    (h : ∀ T : D,
      tensorLeftHomEquiv (T ⊗ M) T (dual D T) M
        ((α_ (dual D T) T M).inv ≫ injection S T ▷ M ≫ a) =
      tensorLeftHomEquiv (T ⊗ M) T (dual D T) M
        ((α_ (dual D T) T M).inv ≫ injection S T ▷ M ≫ b)) : a = b := by
  apply injection_tensor_hom_ext S
  intro T
  apply (cancel_epi (α_ (dual D T) T M).inv).mp
  exact (tensorLeftHomEquiv (T ⊗ M) T (dual D T) M).injective (h T)

omit [Simple (𝟙_ D)] in
/-- The actual cap of the recovered annular crossing is exactly the
restriction of the original actual module action. -/
lemma moduleCap_eq_capOf (M : Mod_ D (algebra S)) (T : D) :
    moduleCap S M T = capOf T M.X (moduleHolonomy S M T) :=
  (moduleHolonomy_cap S M T).symm

/-- Equality of actual recovered holonomies proves equality with the
actual center action by the coend generators. -/
lemma action_eq_of_holonomy (M : Mod_ D (algebra S)) (b : HalfBraiding M.X)
    (h : ∀ T : D, moduleHolonomy S M T = (holonomy ⟨M.X,b⟩ T).hom) :
    γ[algebra S,M.X] = action S ⟨M.X,b⟩ := by
  apply annularTranspose_hom_ext S M.X
  intro T
  have hi : injection S T ▷ M.X ≫ action S ⟨M.X,b⟩ = actionComponent ⟨M.X,b⟩ T :=
    injection_action S ⟨M.X,b⟩ T
  rw [hi]
  exact (h T).trans (actionComponent_transpose ⟨M.X,b⟩ T).symm

end Paper18.Category.DrinfeldCoendModules
