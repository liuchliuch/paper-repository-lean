import Paper18.Category.ModuleFunctorDualDimensionCharacter
import Paper18.Category.ModuleFunctorDualDimensionUnderlying
import Paper18.Category.ModuleFunctorDualDimensionFree

/-! # Actual module endofunctor FP dimensions and underlying sizes -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators MonoidalLeftAction
universe v u vM uM w wM wE
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ c : C, (actionLeft M c).Additive]
  [∀ c : C, (actionLeft M c).Linear ℂ]
  [∀ X : M, (actionRight C X).Additive]
  {ι : Type w} [Fintype ι] (SC : FiniteSemisimpleSkeleton C ι)
  {κ : Type wM} [Fintype κ] (SM : FiniteSemisimpleSkeleton M κ)
  (j₀ : κ)
  [HasKernels (ModuleAlphaInduction.End C M)]
  [∀ F G : ModuleAlphaInduction.End C M, FiniteDimensional ℂ (F ⟶ G)]
  [RightRigidCategory (ModuleAlphaInduction.End C M)]
  [Simple (𝟙_ (ModuleAlphaInduction.End C M))]
  {ε : Type wE} [Fintype ε]
  (TE : FiniteSemisimpleSkeleton (ModuleAlphaInduction.End C M) ε)
  (U : M ⥤ C) [U.Additive] [U.Faithful] [U.LeftLinear C]

include j₀ in
/-- Actual orbit connectivity and the actual faithful strong forgetful functor
identify intrinsic End FP dimension as its actual underlying-size multiplier.
The input has no eigenvector, proportionality or dimension-equality field. -/
theorem moduleFunctor_fpdim_underlying
    (hconn : ∀ j k : κ, ∃ X : C, Nonempty (Retract (SM.simpleObject k) (X ⊙ₗ SM.simpleObject j)))
    (F : ModuleAlphaInduction.End C M) (X : M) :
    SC.fpdim (U.obj (F.toFunctor.obj X)) = TE.fpdim F * SC.fpdim (U.obj X) := by
  rw [fpdim_underlying_eq_weight SC SM U, fpdim_underlying_eq_weight SC SM U]
  exact moduleFunctor_fpdim_scales_weight SC SM (moduleUnderlyingWeight SC SM U) j₀ TE
    hconn SC.fusionBasis.fpdim (moduleUnderlyingWeight_pos SC SM U)
    (moduleUnderlyingWeight_action SC SM U) F X

end Paper18.Category.ModuleFunctor
