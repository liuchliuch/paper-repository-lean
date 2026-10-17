import Paper18.Category.BalancedModuleCategoryUniversal
import Paper18.Category.BalancedModuleCategoryLinear

/-! # The actual coequalizer extension of a bilinear balanced functor is linear -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vE uE
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {E : Type uE} [Category.{vE} E] [Preadditive E] [Linear ℂ E] [HasCoequalizers E]
namespace BalancedFunctor
variable (F : BalancedFunctor (A := A) (B := B) E) [F.IsBilinear]

instance regularSlice_additive : F.regularSlice.Additive :=
  IsBilinear.left_additive (Mod_.regular (mop B))

instance regularSlice_linear : F.regularSlice.Linear ℂ :=
  IsBilinear.left_linear (Mod_.regular (mop B))

instance extension_additive : F.extension.Additive where
  map_add {P Q} f g := by
    apply (cancel_epi (F.rightMonadModule.descentπ (toAlgebraObj P))).mp
    change F.rightMonadModule.descentπ (toAlgebraObj P) ≫
        F.rightMonadModule.descentMap (toAlgebras.map (f + g)) =
      F.rightMonadModule.descentπ (toAlgebraObj P) ≫
        (F.rightMonadModule.descentMap (toAlgebras.map f) +
          F.rightMonadModule.descentMap (toAlgebras.map g))
    rw [Preadditive.comp_add, RightMonadModule.descentπ_map,
      RightMonadModule.descentπ_map, RightMonadModule.descentπ_map]
    change F.regularSlice.map (f.hom + g.hom) ≫ F.rightMonadModule.descentπ (toAlgebraObj Q) =
      F.regularSlice.map f.hom ≫ F.rightMonadModule.descentπ (toAlgebraObj Q) +
        F.regularSlice.map g.hom ≫ F.rightMonadModule.descentπ (toAlgebraObj Q)
    rw [F.regularSlice.map_add, Preadditive.add_comp]

instance extension_linear : F.extension.Linear ℂ where
  map_smul f z := by
    apply (cancel_epi (F.rightMonadModule.descentπ (toAlgebraObj _))).mp
    change F.rightMonadModule.descentπ (toAlgebraObj _) ≫
        F.rightMonadModule.descentMap (toAlgebras.map (z • f)) =
      F.rightMonadModule.descentπ (toAlgebraObj _) ≫
        (z • F.rightMonadModule.descentMap (toAlgebras.map f))
    rw [Linear.comp_smul, RightMonadModule.descentπ_map, RightMonadModule.descentπ_map]
    change F.regularSlice.map (z • f.hom) ≫ F.rightMonadModule.descentπ (toAlgebraObj _) =
      z • (F.regularSlice.map f.hom ≫ F.rightMonadModule.descentπ (toAlgebraObj _))
    rw [F.regularSlice.map_smul, Linear.smul_comp]

end BalancedFunctor
end Paper18.Category.BalancedModuleCategory
