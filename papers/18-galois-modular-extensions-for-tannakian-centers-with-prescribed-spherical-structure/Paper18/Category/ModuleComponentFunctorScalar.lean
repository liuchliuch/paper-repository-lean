import Paper18.Category.ModuleComponentScalar
import Paper18.Category.FixedBoundaryModuleFaithful

/-! # Actual scalar automorphisms of module equivalences on components -/
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
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι) (i : ι)
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalLeftAction C N]
  (F : Component (C := C) S i ⥤ N) [F.Full] [F.Faithful] [F.Linear ℂ] [F.LeftLinear C]

/-- Actual full faithfulness pulls module automorphisms back to the
identity; the actual component theorem derives their unique scalar units. -/
theorem functorAut_unique_scalar
    (τ : F ≅ F) [ModuleFunctor.IsModuleNatural C τ.hom] :
    ∃! z : ℂˣ, ∀ X : Component (C := C) S i,
      τ.hom.app X = (z : ℂ) • 𝟙 (F.obj X) := by
  let σ := ModuleFunctor.fullyFaithfulModuleAut F τ
  obtain ⟨z, hz, hu⟩ := exists_unique_scalar_unit S i σ
  refine ⟨z, ?_, ?_⟩
  · intro X
    calc
      τ.hom.app X = F.map (σ.hom.app X) :=
        (ModuleFunctor.fullyFaithfulModuleAut_map F τ X).symm
      _ = F.map ((z : ℂ) • 𝟙 X) := congrArg (fun f => F.map f) (hz X)
      _ = _ := by rw [CategoryTheory.Functor.map_smul, F.map_id]
  · intro y hy
    apply hu y
    intro X
    apply F.map_injective
    calc
      F.map (σ.hom.app X) = τ.hom.app X := ModuleFunctor.fullyFaithfulModuleAut_map F τ X
      _ = (y : ℂ) • 𝟙 (F.obj X) := hy X
      _ = F.map ((y : ℂ) • 𝟙 X) := by rw [CategoryTheory.Functor.map_smul, F.map_id]

end Paper18.Category.ModuleComponent
