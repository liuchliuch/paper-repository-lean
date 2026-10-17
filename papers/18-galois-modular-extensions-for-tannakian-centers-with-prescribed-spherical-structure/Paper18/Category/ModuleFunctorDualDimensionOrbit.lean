import Paper18.Category.ModuleFunctorDualDimension
import Paper18.Category.ModuleFunctorSemisimpleOrbit

/-! # Concrete intrinsic FP dimensions on the actual separable-module orbit -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.SeparableAlgebra
variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [BraidedCategory D] [RightRigidCategory D] [Simple (𝟙_ D)]
  {R : D} [MonObj R] (S : SeparableAlgebra R)
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton D ι)
  (hR : (𝟙 R : R ⟶ R) ≠ 0)
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
attribute [local instance] MonoidalOppositeFusion.rightRigidCategory MonoidalOppositeFusion.simpleUnit

local instance orbitWeightKernels : HasKernels (S.OrbitComponent T hR) := S.orbitHasKernels T hR
local instance orbitWeightEndKernels :
    HasKernels (ModuleAlphaInduction.End Dᴹᵒᵖ (S.OrbitComponent T hR)) := S.orbitEndHasKernels T hR
local instance orbitWeightEndFiniteHom
    (F G : ModuleAlphaInduction.End Dᴹᵒᵖ (S.OrbitComponent T hR)) :
    FiniteDimensional ℂ (F ⟶ G) := S.orbitEndFiniteHom T hR F G
local instance orbitWeightEndRigid :
    RightRigidCategory (ModuleAlphaInduction.End Dᴹᵒᵖ (S.OrbitComponent T hR)) :=
  S.orbitEndRightRigid T hR
local instance orbitWeightEndSimple :
    Simple (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (S.OrbitComponent T hR))) := S.orbitEndSimpleUnit T hR

/-- The actual orbit inclusion followed by the actual strong forgetful functor. -/
def orbitUnderlying : S.OrbitComponent T hR ⥤ Dᴹᵒᵖ :=
  (ModuleFunctor.componentInclusion (S.skeleton T) (S.orbitLabel T hR)).toFunctor ⋙
    ModuleFunctor.wattsForget

instance orbitUnderlying_additive : (S.orbitUnderlying T hR).Additive := by
  unfold orbitUnderlying ModuleFunctor.wattsForget
  infer_instance
instance orbitUnderlying_linear : (S.orbitUnderlying T hR).Linear ℂ := by
  unfold orbitUnderlying ModuleFunctor.wattsForget
  infer_instance
instance orbitUnderlying_faithful : (S.orbitUnderlying T hR).Faithful := by
  unfold orbitUnderlying ModuleFunctor.wattsForget
  infer_instance
instance orbitUnderlying_leftLinear : (S.orbitUnderlying T hR).LeftLinear Dᴹᵒᵖ := by
  unfold orbitUnderlying
  infer_instance

/-- The actual End FP dimension scales actual ambient FP size on every
object of the actual chosen nonempty separable-module orbit. -/
theorem orbitEnd_fpdim_underlying
    (F : ModuleAlphaInduction.End Dᴹᵒᵖ (S.OrbitComponent T hR)) (X : S.OrbitComponent T hR) :
    T.fpdim (F.toFunctor.obj X).obj.X =
      (S.orbitEndSkeleton T hR).fpdim F * T.fpdim X.obj.X := by
  let j₀ : {j : S.SimpleIndex T // ModuleComponent.property (C := Dᴹᵒᵖ)
      (S.skeleton T) (S.orbitLabel T hR) ((S.skeleton T).simpleObject j)} :=
    ⟨S.orbitLabel T hR, ModuleComponent.property_base (S.skeleton T) (S.orbitLabel T hR)⟩
  have h := ModuleFunctor.moduleFunctor_fpdim_underlying (MonoidalOppositeFusion.skeleton T)
    (S.orbitSkeleton T hR) j₀ (S.orbitEndSkeleton T hR) (S.orbitUnderlying T hR)
    (ModuleFunctor.component_retract_connected (S.skeleton T) (S.orbitLabel T hR)) F X
  change (MonoidalOppositeFusion.skeleton T).fpdim (mop (F.toFunctor.obj X).obj.X) =
    (S.orbitEndSkeleton T hR).fpdim F *
      (MonoidalOppositeFusion.skeleton T).fpdim (mop X.obj.X) at h
  have hm (Y : D) : (MonoidalOppositeFusion.skeleton T).fpdim (mop Y) = T.fpdim Y :=
    T.fpdim_map (MonoidalOppositeFusion.skeleton T) (mopFunctor D) Y
  simpa only [hm] using h

end Paper18.Category.SeparableAlgebra
