import Paper18.Category.GraphPicardMoritaProductFunctor
import Paper18.Category.FixedBoundaryModuleGeneralWatts

/-! # Actual residual-module structure on an external product factor

At a fixed left algebra-module object, the external product is actual
transport of algebra modules by the action-on-that-object functor. The
constructed residual lineators therefore make it an actual strong module
functor. Its comparison with the external balanced bifunctor has actual
identity underlying components.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction MonoidalOpposite
open scoped MonObj
universe v u
namespace Paper18.Category.GraphPicard.MoritaProduct
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  (R B : Mon D)
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual residual right ambient action on genuine right B-modules,
presented as a left action of the monoidal opposite. -/
def rightModulesResidualAction : MonoidalLeftAction Dᴹᵒᵖ
    (BalancedModuleCategory.RightModules B.X) :=
  negativeLiftedAction Dᴹᵒᵖ Dᴹᵒᵖ (mop B.X)

theorem rightModulesResidualAction_action (X : Dᴹᵒᵖ)
    (N : BalancedModuleCategory.RightModules B.X) :
    letI := rightModulesResidualAction B
    (γ[mop B.X,(X ⊙ₗ N).X]).unmop =
      (α_ N.X.unmop X.unmop B.X).hom ≫
        N.X.unmop ◁ (β_ X.unmop B.X).hom ≫
          (α_ N.X.unmop B.X X.unmop).inv ≫
            (γ[mop B.X,N.X]).unmop ▷ X.unmop := by
  letI := rightModulesResidualAction B
  change (Functor.LaxLeftLinear.μₗ
      ((ModuleAlphaInduction.negative Dᴹᵒᵖ Dᴹᵒᵖ).obj X).toFunctor (mop B.X) N.X ≫
        ((ModuleAlphaInduction.negative Dᴹᵒᵖ Dᴹᵒᵖ).obj X).toFunctor.map γ[mop B.X,N.X]).unmop = _
  rw [ModuleAlphaInduction.negative_μ]
  change ((α_ N.X.unmop X.unmop B.X).hom ≫
    N.X.unmop ◁ (β_ X.unmop B.X).hom ≫
      (α_ N.X.unmop B.X X.unmop).inv) ≫
        (γ[mop B.X,N.X]).unmop ▷ X.unmop = _
  simp only [Category.assoc]

/-- The actual residual action on genuine native (R,B)-bimodules. -/
def nativeResidualAction : MonoidalLeftAction Dᴹᵒᵖ
    (BimoduleRelativeTensor.Native R.X B.X) :=
  negativeLiftedAction Dᴹᵒᵖ (Mod_ D R.X) (mop B.X)

/-- The fixed-first-factor external tensor, defined by actual module
transport along the actual action-on-an-object functor. -/
def fixedExternalTransport (M : Mod_ D R.X) :
    BalancedModuleCategory.RightModules B.X ⥤ BimoduleRelativeTensor.Native R.X B.X :=
  ModuleFunctor.mapActionModules (A := mop B.X) (MonoidalLeftAction.actionRight Dᴹᵒᵖ M)

/-- The external tensor is an actual strong native module functor in
its second variable. Its coherence follows from actual transported
central-action naturality. -/
def fixedExternalTransport_leftLinear (M : Mod_ D R.X) :
    letI := rightModulesResidualAction B
    letI := nativeResidualAction R B
    (fixedExternalTransport R B M).LeftLinear Dᴹᵒᵖ :=
  transportResidualLeftLinear Dᴹᵒᵖ (mop B.X) (MonoidalLeftAction.actionRight Dᴹᵒᵖ M)

omit [BraidedCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
@[simp] theorem fixedExternalTransport_obj (M : Mod_ D R.X)
    (N : BalancedModuleCategory.RightModules B.X) :
    ((fixedExternalTransport R B M).obj N).X.X = M.X ⊗ N.X.unmop := rfl

omit [BraidedCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
@[simp] theorem fixedExternalTransport_map (M : Mod_ D R.X)
    {N N' : BalancedModuleCategory.RightModules B.X} (f : N ⟶ N') :
    ((fixedExternalTransport R B M).map f).hom.hom = M.X ◁ f.hom.unmop := rfl

/-- The strong-module presentation agrees with the actual external
balanced product by a genuine natural isomorphism. -/
def fixedExternalTransportIso (M : Mod_ D R.X) :
    fixedExternalTransport R B M ≅ BalancedModuleCategory.externalRight (B := B.X) M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro N N' f
    apply Mod_.Hom.ext
    apply Mod_.Hom.ext
    change M.X ◁ f.hom.unmop ≫ 𝟙 _ = 𝟙 _ ≫ (𝟙 M.X ⊗ₘ f.hom.unmop)
    rw [id_tensorHom, Category.comp_id, Category.id_comp])

end Paper18.Category.GraphPicard.MoritaProduct
