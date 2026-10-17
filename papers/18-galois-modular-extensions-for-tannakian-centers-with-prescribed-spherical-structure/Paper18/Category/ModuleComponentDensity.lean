import Paper18.Category.ModuleComponentConnected
import Paper18.Category.ModuleFunctorFiniteDensity

/-! # Actual one-object density on an action component -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM vN uN w
namespace Paper18.Category.ModuleComponent
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι) (i : ι)
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalLeftAction C N]

/-- Actual module natural transformations are detected on the chosen
actual simple generator, including noninvertible transformations. -/
theorem natTrans_ext (F G : Component (C := C) S i ⥤ N)
    [F.LeftLinear C] [G.LeftLinear C] [F.Additive]
    (τ σ : F ⟶ G) [ModuleFunctor.IsModuleNatural C τ] [ModuleFunctor.IsModuleNatural C σ]
    (h : τ.app (base (C := C) S i) = σ.app (base (C := C) S i)) : τ = σ := by
  apply ModuleFunctor.natTrans_ext_simples (skeleton (C := C) S i) F G τ σ
  intro j
  obtain ⟨X, ⟨R⟩⟩ := simple_retract_action_base S i j
  exact ModuleFunctor.natTrans_app_eq_of_retract τ σ R
    (ModuleFunctor.moduleNatTrans_app_action_eq τ σ X (base (C := C) S i) h)

section Bundled
variable [∀ X : C, (MonoidalLeftAction.actionLeft N X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Linear ℂ]

/-- Actual linear evaluation of module transformations on one generator. -/
def evaluation (F G : ModuleFunctor.Bundled C (Component (C := C) S i) N) :
    (F ⟶ G) →ₗ[ℂ]
      (F.toFunctor.obj (base (C := C) S i) ⟶ G.toFunctor.obj (base (C := C) S i)) where
  toFun τ := τ.val.app (base (C := C) S i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluation_injective (F G : ModuleFunctor.Bundled C (Component (C := C) S i) N) :
    Function.Injective (evaluation S i F G) := by
  intro τ σ h
  apply ModuleFunctor.bundled_hom_ext
  exact natTrans_ext S i F.toFunctor G.toFunctor τ.val σ.val h

theorem hom_finrank_le [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
    (F G : ModuleFunctor.Bundled C (Component (C := C) S i) N) :
    Module.finrank ℂ (F ⟶ G) ≤ Module.finrank ℂ
      (F.toFunctor.obj (base (C := C) S i) ⟶ G.toFunctor.obj (base (C := C) S i)) := by
  exact LinearMap.finrank_le_finrank_of_injective (evaluation_injective S i F G)

end Bundled
end Paper18.Category.ModuleComponent
