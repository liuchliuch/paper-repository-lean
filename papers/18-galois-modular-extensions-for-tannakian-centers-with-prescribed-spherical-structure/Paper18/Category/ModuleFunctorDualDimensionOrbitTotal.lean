import Paper18.Category.ModuleFunctorDualDimensionTransportFP
import Paper18.Category.ModuleFunctorDualDimensionOrbit
import Paper18.Category.ModuleFunctorDualDimensionConnected
import Paper18.Category.ModuleFunctorDualDimensionBlockConnected
import Paper18.Category.BimoduleRelativeTensorBlockOrbit
import Paper18.Category.BimoduleRelativeTensorBlockRegularSimple
import Paper18.Category.FiniteSemisimpleLeftRigid
import Paper18.Category.SemisimpleCokernels

/-! # Actual total FP dimension of the selected separable-module orbit dual

The selected orbit is identified with modules over its genuinely constructed
separable algebra block. Actual connectedness of that module category follows
from simplicity of its actual regular bimodule. The true connected dual formula
then transports through the actual native module equivalence.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.SeparableAlgebra
variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D] [HasCoequalizers D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [BraidedCategory D] [LeftRigidCategory D] [RightRigidCategory D] [Simple (𝟙_ D)]
  {R : D} [MonObj R] (S : SeparableAlgebra R)
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton D ι)
  (hR : (𝟙 R : R ⟶ R) ≠ 0)
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
attribute [local instance] MonoidalOppositeFusion.rightRigidCategory MonoidalOppositeFusion.simpleUnit
attribute [local instance] Preadditive.hasEqualizers_of_hasKernels

/-- The actual fusion basis of the actual selected orbit dual. -/
def orbitEndFusionBasis : FusionBasis (S.OrbitEndSimpleIndex T hR) := by
  letI := S.orbitEndHasKernels T hR
  letI : ∀ F G : ModuleAlphaInduction.End Dᴹᵒᵖ (S.OrbitComponent T hR),
      FiniteDimensional ℂ (F ⟶ G) := S.orbitEndFiniteHom T hR
  letI := S.orbitEndRightRigid T hR
  letI := S.orbitEndSimpleUnit T hR
  exact (S.orbitEndSkeleton T hR).fusionBasis

/-- The actual selected orbit dual has the actual ambient total FP dimension.
No pivotal structure, dimension equality or categorical-existence field is an input. -/
theorem orbitEnd_totalFPdim : (S.orbitEndFusionBasis T hR).totalFPdim = T.fusionBasis.totalFPdim := by
  letI := S.orbitHasKernels T hR
  letI := S.orbitEndHasKernels T hR
  letI : ∀ F G : ModuleAlphaInduction.End Dᴹᵒᵖ (S.OrbitComponent T hR),
      FiniteDimensional ℂ (F ⟶ G) := S.orbitEndFiniteHom T hR
  letI := S.orbitEndRightRigid T hR
  letI := S.orbitEndSimpleUnit T hR
  change (S.orbitEndSkeleton T hR).fusionBasis.totalFPdim = _
  let j := S.orbitLabel T hR
  let B := BimoduleRelativeTensor.BlockOrbit.algebra S T j
  letI : MonObj B := BimoduleRelativeTensor.BlockOrbit.algebraMonObj S T j
  let SB := BimoduleRelativeTensor.BlockOrbit.separable S T j
  have hB : (𝟙 B : B ⟶ B) ≠ 0 := ModuleFunctor.orbitBlock_ne_zero S T j
  letI : Simple (ModuleFunctor.wattsRegular (R := B)) :=
    BimoduleRelativeTensor.Block.orbitRegular_simple T S j
  let hconn := ModuleFunctor.module_connected_of_regular_bimodule_simple SB T
  letI : HasFiniteLimits (Mod_ D B) := hasFiniteLimits_of_hasEqualizers_and_finite_products
  letI : ∀ F G : ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D B), FiniteDimensional ℂ (F ⟶ G) :=
    ModuleFunctor.finiteDimensionalHom (SB.skeleton T)
  letI : RightRigidCategory (ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D B)) :=
    ModuleFunctor.endRightRigidCategory (SB.skeleton T)
  letI : Simple (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D B))) :=
    ModuleFunctor.connected_moduleEndSimpleUnit (SB.skeleton T) (SB.orbitLabel T hB) hconn
      (ModuleFunctor.wattsEndSkeleton SB T)
  let SA := ModuleFunctor.wattsEndSkeleton SB T
  let e := BimoduleRelativeTensor.BlockOrbit.equivalence S T j
  let I : ModuleFunctor.Bundled Dᴹᵒᵖ (Mod_ D B) (S.OrbitComponent T hR) :=
    ⟨e.functor, inferInstance, inferInstance, inferInstance⟩
  let P : ModuleFunctor.Bundled Dᴹᵒᵖ (S.OrbitComponent T hR) (Mod_ D B) :=
    ⟨e.inverse, inferInstance, inferInstance, inferInstance⟩
  letI : I.toFunctor.Full := by change e.functor.Full; infer_instance
  letI : I.toFunctor.Faithful := by change e.functor.Faithful; infer_instance
  let adj : I.toFunctor ⊣ P.toFunctor := e.toAdjunction
  letI : ModuleFunctor.IsModuleNatural Dᴹᵒᵖ adj.unit :=
    inferInstanceAs (ModuleFunctor.IsModuleNatural Dᴹᵒᵖ e.unitIso.hom)
  letI : ModuleFunctor.IsModuleNatural Dᴹᵒᵖ adj.counit :=
    inferInstanceAs (ModuleFunctor.IsModuleNatural Dᴹᵒᵖ e.counitIso.hom)
  letI : IsIso adj.counit := inferInstanceAs (IsIso e.counitIso.hom)
  let k₀ : {k : S.SimpleIndex T // ModuleComponent.property (C := Dᴹᵒᵖ) (S.skeleton T) j
      ((S.skeleton T).simpleObject k)} := ⟨j, ModuleComponent.property_base (S.skeleton T) j⟩
  have he := ModuleFunctor.cornerEnd_totalFPdim (MonoidalOppositeFusion.skeleton T)
    (SB.skeleton T) (SB.orbitLabel T hB) (S.orbitSkeleton T hR) k₀
    SA (S.orbitEndSkeleton T hR) I P adj (S.orbitUnderlying T hR) hconn
    (ModuleFunctor.component_retract_connected (S.skeleton T) j)
  have ht := SB.connectedModuleEnd_totalFPdim T hB hconn
  change SA.fusionBasis.totalFPdim = T.fusionBasis.totalFPdim at ht
  exact he.symm.trans ht

omit [HasCoequalizers D] [LeftRigidCategory D] in
/-- The finite semisimple fusion data construct the extra native limit and
left-dual structures, so the result needs no additional structural premise. -/
theorem orbitEnd_totalFPdim_fusion :
    (S.orbitEndFusionBasis T hR).totalFPdim = T.fusionBasis.totalFPdim := by
  letI := T.hasCoequalizers
  letI := FiniteSemisimpleLeftRigid.leftRigidCategory T
  exact S.orbitEnd_totalFPdim T hR

end Paper18.Category.SeparableAlgebra
