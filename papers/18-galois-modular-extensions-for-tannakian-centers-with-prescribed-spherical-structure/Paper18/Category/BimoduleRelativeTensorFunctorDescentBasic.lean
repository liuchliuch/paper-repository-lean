import Paper18.Category.BalancedModuleCategoryMonadDescent
import Mathlib.CategoryTheory.Monad.Adjunction

/-! # Restriction of an actual functor to an adjunction's free objects -/
noncomputable section
open CategoryTheory CategoryTheory.Category
universe vC uC vD uD vE uE
namespace Paper18.Category.BimoduleRelativeTensor.FunctorDescent
open BalancedModuleCategory
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E] {F : C ⥤ D} {U : D ⥤ C}
  (adj : F ⊣ U) (K : D ⥤ E)

/-- The actual adjunction counit gives the actual right monad action
on the restriction of any actual functor to free objects. -/
def rightModule : RightMonadModule (E := E) adj.toMonad where
  toFunctor := F ⋙ K
  action :=
    { app X := K.map (adj.counit.app (F.obj X))
      naturality {X Y} f := by
        change K.map (F.map (U.map (F.map f))) ≫ K.map (adj.counit.app (F.obj Y)) =
          K.map (adj.counit.app (F.obj X)) ≫ K.map (F.map f)
        rw [← K.map_comp, ← K.map_comp]
        exact congrArg K.map (adj.counit.naturality (F.map f)) }
  unit X := by
    change K.map (F.map (adj.unit.app X)) ≫ K.map (adj.counit.app (F.obj X)) = 𝟙 _
    rw [← K.map_comp, adj.left_triangle_components]
    exact K.map_id (F.obj X)
  assoc X := by
    change K.map (F.map (U.map (adj.counit.app (F.obj X)))) ≫
        K.map (adj.counit.app (F.obj X)) =
      K.map (adj.counit.app (F.obj (U.obj (F.obj X)))) ≫
        K.map (adj.counit.app (F.obj X))
    rw [← K.map_comp, ← K.map_comp]
    exact congrArg K.map (adj.counit.naturality (adj.counit.app (F.obj X)))

end Paper18.Category.BimoduleRelativeTensor.FunctorDescent
