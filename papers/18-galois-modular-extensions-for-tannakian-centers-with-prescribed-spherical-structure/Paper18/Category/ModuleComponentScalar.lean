import Paper18.Category.ModuleComponentDensity
import Paper18.Category.TensorCharacters

/-! # Actual Schur scalars on an action component

Every simple of the component is an actual retract of an action on its
chosen simple. Module naturality and actual semisimple decompositions then
force a single scalar on every object of the component.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM w
namespace Paper18.Category.ModuleComponent
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι) (i : ι)

/-- The actual scalar extracted on the specified simple generator. -/
def scalar (τ : 𝟭 (Component (C := C) S i) ⟶ 𝟭 (Component (C := C) S i)) : ℂ :=
  simpleScalarEquiv (S.simpleObject i) (τ.app (base (C := C) S i))

theorem scalar_spec
    (τ : 𝟭 (Component (C := C) S i) ⟶ 𝟭 (Component (C := C) S i)) :
    scalar (C := C) S i τ • 𝟙 (base (C := C) S i) = τ.app (base (C := C) S i) :=
  simpleScalarEquiv_spec _ _

/-- Actual module-natural endomorphisms of the identity have the same
scalar on every object, by the actual one-object density theorem. -/
theorem app_eq_scalar
    (τ : 𝟭 (Component (C := C) S i) ⟶ 𝟭 (Component (C := C) S i))
    [ModuleFunctor.IsModuleNatural C τ] (X : Component (C := C) S i) :
    τ.app X = scalar (C := C) S i τ • 𝟙 X := by
  have h : τ = scalar (C := C) S i τ • (𝟙 (𝟭 (Component (C := C) S i))) := by
    apply natTrans_ext S i (𝟭 _) (𝟭 _)
    exact (scalar_spec (C := C) S i τ).symm
  exact congrArg (fun σ : 𝟭 (Component (C := C) S i) ⟶ 𝟭 _ => σ.app X) h

/-- In particular, the extracted scalar is the actual scalar on every
simple of the component. -/
theorem app_simple_eq_scalar
    (τ : 𝟭 (Component (C := C) S i) ⟶ 𝟭 (Component (C := C) S i))
    [ModuleFunctor.IsModuleNatural C τ]
    (j : {j : ι // property (C := C) S i (S.simpleObject j)}) :
    τ.app ((skeleton (C := C) S i).simpleObject j) =
      scalar (C := C) S i τ • 𝟙 _ :=
  app_eq_scalar S i τ _

theorem scalar_ne_zero
    (τ : 𝟭 (Component (C := C) S i) ≅ 𝟭 (Component (C := C) S i)) :
    scalar (C := C) S i τ.hom ≠ 0 := by
  intro hz
  have hh := τ.hom_inv_id_app (base (C := C) S i)
  rw [← scalar_spec (C := C) S i τ.hom, hz, zero_smul, zero_comp] at hh
  exact CategoryTheory.id_nonzero (base (C := C) S i) hh.symm

/-- The actual scalar coordinates of module-natural automorphisms are
unique units of the actual coefficient field. -/
theorem exists_unique_scalar_unit
    (τ : 𝟭 (Component (C := C) S i) ≅ 𝟭 (Component (C := C) S i))
    [ModuleFunctor.IsModuleNatural C τ.hom] :
    ∃! z : ℂˣ, ∀ X : Component (C := C) S i, τ.hom.app X = (z : ℂ) • 𝟙 X := by
  let z := Units.mk0 (scalar (C := C) S i τ.hom) (scalar_ne_zero S i τ)
  refine ⟨z, app_eq_scalar S i τ.hom, ?_⟩
  intro y hy
  apply Units.ext
  change (y : ℂ) = scalar (C := C) S i τ.hom
  apply smul_left_injective ℂ (CategoryTheory.id_nonzero (base (C := C) S i))
  exact (hy (base (C := C) S i)).symm.trans (scalar_spec (C := C) S i τ.hom).symm

end Paper18.Category.ModuleComponent
