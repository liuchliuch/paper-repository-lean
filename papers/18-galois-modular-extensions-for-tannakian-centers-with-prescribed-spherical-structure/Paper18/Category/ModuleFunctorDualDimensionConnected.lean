import Paper18.Category.ModuleFunctorDualDimension
import Paper18.Category.ModuleFunctorDualDimensionConnectedUnit
import Paper18.Category.ModuleFunctorDualDimensionEquivalence
import Paper18.Category.BimoduleRelativeTensorWatts
import Paper18.Category.ModuleFunctorSemisimpleOrbit

/-! # Genuine dual total dimension for an actual connected separable-module action

Connectivity is an actual retract condition on actual module simples. All End
fusion foundations and the total dimension equality are derived from it.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped BigOperators MonObj MonoidalLeftAction
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
variable (hconn : ∀ j k : S.SimpleIndex T, ∃ X : Dᴹᵒᵖ,
    Nonempty (Retract ((S.skeleton T).simpleObject k) (X ⊙ₗ (S.skeleton T).simpleObject j)))
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
attribute [local instance] MonoidalOppositeFusion.rightRigidCategory MonoidalOppositeFusion.simpleUnit
attribute [local instance] Preadditive.hasEqualizers_of_hasKernels

local instance connectedModuleFiniteLimits : HasFiniteLimits (Mod_ D R) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products
include hR hconn in
/-- The actual dual fusion basis, with simple unit derived from connectivity. -/
def connectedModuleEndFusionBasis : FusionBasis (ModuleFunctor.WattsSimpleIndex S T) := by
  letI : ∀ F G : ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D R), FiniteDimensional ℂ (F ⟶ G) :=
    ModuleFunctor.finiteDimensionalHom (S.skeleton T)
  letI : RightRigidCategory (ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D R)) :=
    ModuleFunctor.endRightRigidCategory (S.skeleton T)
  letI : Simple (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D R))) :=
    ModuleFunctor.connected_moduleEndSimpleUnit (S.skeleton T) (S.orbitLabel T hR) hconn
      (ModuleFunctor.wattsEndSkeleton S T)
  exact (ModuleFunctor.wattsEndSkeleton S T).fusionBasis

/-- True total FP dimension equality for the dual of an actual connected
separable-module category, with no numerical dimension premise. -/
theorem connectedModuleEnd_totalFPdim :
    (S.connectedModuleEndFusionBasis T hR hconn).totalFPdim = T.fusionBasis.totalFPdim := by
  letI : ∀ F G : ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D R), FiniteDimensional ℂ (F ⟶ G) :=
    ModuleFunctor.finiteDimensionalHom (S.skeleton T)
  letI : RightRigidCategory (ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D R)) :=
    ModuleFunctor.endRightRigidCategory (S.skeleton T)
  letI : Simple (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D R))) :=
    ModuleFunctor.connected_moduleEndSimpleUnit (S.skeleton T) (S.orbitLabel T hR) hconn
      (ModuleFunctor.wattsEndSkeleton S T)
  change (ModuleFunctor.wattsEndSkeleton S T).fusionBasis.totalFPdim = _
  let TE := ModuleFunctor.wattsEndSkeleton S T
  let TB := ModuleFunctor.bimoduleSkeleton S T
  letI : (ModuleFunctor.wattsForget (R := R)).Additive := by
    unfold ModuleFunctor.wattsForget
    infer_instance
  letI : (ModuleFunctor.wattsForget (R := R)).Faithful := by
    unfold ModuleFunctor.wattsForget
    infer_instance
  letI := ModuleFunctor.wattsEvaluation_full S
  letI := ModuleFunctor.wattsEvaluation_faithful S
  have hm (Y : D) : (MonoidalOppositeFusion.skeleton T).fpdim (mop Y) = T.fpdim Y :=
    T.fpdim_map (MonoidalOppositeFusion.skeleton T) (mopFunctor D) Y
  have hd (F : ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D R)) :
      T.fpdim (ModuleFunctor.wattsEvaluation.obj F).X.X = TE.fpdim F * T.fpdim R := by
    have h := ModuleFunctor.moduleFunctor_fpdim_underlying (MonoidalOppositeFusion.skeleton T)
      (S.skeleton T) (S.orbitLabel T hR) TE ModuleFunctor.wattsForget hconn F (Mod_.regular R)
    change (MonoidalOppositeFusion.skeleton T).fpdim (mop (F.toFunctor.obj (Mod_.regular R)).X) =
      TE.fpdim F * (MonoidalOppositeFusion.skeleton T).fpdim (mop R) at h
    simpa only [hm] using h
  have he := ModuleFunctor.weighted_simple_sum_equivalence TE TB ModuleFunctor.wattsEvaluation
    (fun P => T.fpdim P.X.X ^ 2) (fun e => by
      have h := T.fpdim_iso ((ModuleFunctor.bimoduleUnderlying (R := R)).mapIso e)
      exact congrArg (fun x : ℝ => x ^ 2) h)
  have htotal : T.fpdim R ^ 2 * TE.fusionBasis.totalFPdim =
      T.fpdim R ^ 2 * T.fusionBasis.totalFPdim := by
    calc
      _ = ∑ i, T.fpdim (ModuleFunctor.wattsEvaluation.obj (TE.simpleObject i)).X.X ^ 2 := by
        simp only [hd, TE.fpdim_simple, FusionBasis.totalFPdim, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ j, T.fpdim (TB.simpleObject j).X.X ^ 2 := he
      _ = _ := ModuleFunctor.bimodule_weighted_total T TB
  have hp : 0 < T.fpdim R := T.fpdim_pos_of_not_isZero R (by
    intro hz
    exact hR (hz.eq_zero_of_src _))
  exact mul_left_cancel₀ (pow_ne_zero 2 hp.ne') htotal

end Paper18.Category.SeparableAlgebra
