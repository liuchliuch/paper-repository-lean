import Paper18.Category.ModuleFunctorAdjointNaturality
import Paper18.Category.ModuleFunctorFiniteBasic

/-! # Actual strong module inverses to ordinary equivalences

For an equivalence, the mate lineator is invertible because its unit,
counit, and original lineator are invertible. Rigidity is unnecessary.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.BimoduleRelativeTensor.ModuleInverse
open ModuleFunctor MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [MonoidalLeftAction C N]
  (e : M ≌ N) [e.functor.LeftLinear C]

/-- Actual adjunction mates give an actual strong inverse module functor. -/
def inverseLeftLinear : e.inverse.LeftLinear C := by
  letI := rightAdjointLaxLeftLinear (C := C) e.toAdjunction
  letI (c : C) (n : N) : IsIso (Functor.LaxLeftLinear.μₗ e.inverse c n) := by
    change IsIso (rightAdjointLineator e.toAdjunction c n)
    simp only [rightAdjointLineator, Adjunction.homEquiv_unit]
    infer_instance
  exact ModuleFunctor.leftLinearOfLax e.inverse

/-- The actual equivalence unit is module natural for the derived inverse. -/
def unit_moduleNatural :
    letI := inverseLeftLinear (C := C) e
    IsModuleNatural C e.unitIso.hom := by
  letI := inverseLeftLinear (C := C) e
  refine ⟨fun c m => ?_⟩
  change 𝟙 (c ⊙ₗ m) ≫ e.unitIso.hom.app (c ⊙ₗ m) =
    (c ⊴ₗ e.unitIso.hom.app m) ≫ rightAdjointLineator e.toAdjunction c (e.functor.obj m) ≫
      e.inverse.map (Functor.LaxLeftLinear.μₗ e.functor c m)
  simpa only [id_comp] using (rightAdjointLineator_unit e.functor e.toAdjunction c m).symm

/-- The actual equivalence counit is module natural for the derived inverse. -/
def counit_moduleNatural :
    letI := inverseLeftLinear (C := C) e
    IsModuleNatural C e.counitIso.hom := by
  letI := inverseLeftLinear (C := C) e
  refine ⟨fun c n => ?_⟩
  change (Functor.LaxLeftLinear.μₗ e.functor c (e.inverse.obj n) ≫
    e.functor.map (rightAdjointLineator e.toAdjunction c n)) ≫ e.counitIso.hom.app (c ⊙ₗ n) =
      c ⊴ₗ e.counitIso.hom.app n ≫ 𝟙 (c ⊙ₗ n)
  exact (assoc _ _ _).trans
    ((rightAdjointLineator_counit_module e.functor e.toAdjunction c n).trans (comp_id _).symm)

end Paper18.Category.BimoduleRelativeTensor.ModuleInverse

namespace Paper18.Category.BimoduleRelativeTensor.ModuleInverse
open ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N] [MonoidalLeftAction C N]

instance asEquivalenceLeftLinear (F : M ⥤ N) [F.LeftLinear C] [F.IsEquivalence] :
    F.asEquivalence.functor.LeftLinear C := by
  change F.LeftLinear C
  infer_instance

/-- A genuine additive linear strong module functor which is an ordinary
equivalence has a genuine additive linear strong module inverse. -/
def inverseBundled (F : Bundled C M N) [F.toFunctor.IsEquivalence] : Bundled C N M := by
  letI : F.toFunctor.asEquivalence.functor.Additive := by
    change F.toFunctor.Additive
    infer_instance
  letI : F.toFunctor.asEquivalence.functor.Linear ℂ := by
    change F.toFunctor.Linear ℂ
    infer_instance
  exact
    { toFunctor := F.toFunctor.asEquivalence.inverse
      leftLinear := inverseLeftLinear (C := C) F.toFunctor.asEquivalence
      additive := inferInstance
      linear := inferInstance }

end Paper18.Category.BimoduleRelativeTensor.ModuleInverse
