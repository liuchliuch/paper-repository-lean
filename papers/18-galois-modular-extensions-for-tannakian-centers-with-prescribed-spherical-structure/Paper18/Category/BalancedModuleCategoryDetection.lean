import Paper18.Category.BalancedModuleCategoryGenerators
import Mathlib.CategoryTheory.Whiskering

/-! # Actual split generators detect all functor comparison maps

The external tensor is proved dominant by explicit separable retractions.
Thus precomposition is faithful on actual natural transformations. This
is a consequence of the construction, not a universal-property hypothesis.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vE uE
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable (SA : SeparableAlgebra A) (SB : SeparableAlgebra B)
  {E : Type uE} [Category.{vE} E]

include SA SB in
/-- Actual comparison maps between native-product functors are determined
on external tensors, by the two actual separability splittings. -/
theorem natTrans_ext {F G : BimoduleRelativeTensor.Native A B ⥤ E}
    {τ σ : F ⟶ G}
    (h : ∀ M N, τ.app (externalObj M N) = σ.app (externalObj M N)) : τ = σ := by
  apply NatTrans.ext
  funext P
  let R := externalFreeRetract SA SB P
  have he := h (InternalModule.free A P.X.X) (Mod_.regular (mop B))
  calc
    τ.app P = F.map R.i ≫ τ.app _ ≫ G.map R.r := by
      rw [τ.naturality_assoc, ← G.map_comp, R.retract, G.map_id, comp_id]
    _ = F.map R.i ≫ σ.app _ ≫ G.map R.r := by rw [he]
    _ = σ.app P := by
      rw [σ.naturality_assoc, ← G.map_comp, R.retract, G.map_id, comp_id]

/-- Precomposition by the actual external tensor functor. -/
def precompose : (BimoduleRelativeTensor.Native A B ⥤ E) ⥤
    (Mod_ D A × RightModules B ⥤ E) :=
  (Functor.whiskeringLeft _ _ E).obj external

include SA SB in
theorem precompose_faithful :
    (precompose (A := A) (B := B) (E := E)).Faithful where
  map_injective {_F _G} τ σ h := by
    apply natTrans_ext SA SB
    intro M N
    exact congrArg (fun k => k.app (M, N)) h

end Paper18.Category.BalancedModuleCategory
