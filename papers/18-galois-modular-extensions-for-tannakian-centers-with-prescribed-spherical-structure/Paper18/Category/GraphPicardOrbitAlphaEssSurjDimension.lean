import Paper18.Category.GraphPicardDimension
import Paper18.Category.ModuleAlphaInduction

/-! # Actual alpha-induction dimensions on the graph orbit

Both native alpha inductions have the given actual right tensor action on
objects. Its genuine intrinsic End dimension is therefore the ambient FP
dimension, by the proved orbit multiplier formula and a nonzero simple base.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
local instance alphaEndKernels : HasKernels
    (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) := graphEndHasKernels S α
local instance alphaEndFiniteHom (F G : ModuleAlphaInduction.End Dᴹᵒᵖ
    (GraphLagrangian.ModuleOrbit S α)) : FiniteDimensional ℂ (F ⟶ G) := graphEndFiniteHom S α F G
local instance alphaEndRightRigid : RightRigidCategory
    (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) := graphEndRightRigid S α
local instance alphaEndSimpleUnit : Simple
    (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α))) := graphEndSimpleUnit S α

/-- The actual base of the graph orbit has strictly positive ambient FP size. -/
theorem graphOrbitBase_fpdim_pos :
    0 < S.fpdim (GraphLagrangian.moduleOrbitBase S α).obj.X := by
  letI : Simple (GraphLagrangian.moduleOrbitBase S α).obj :=
    (GraphLagrangian.moduleSkeleton S α).simple _
  apply S.fpdim_pos_of_not_isZero
  intro hz
  apply simpleModule_underlying_nonzero
    ((GraphLagrangian.moduleOrbitBase S α).obj)
  exact hz.eq_of_src _ _

/-- The actual End FP dimension of positive native alpha induction is its
actual ambient object FP dimension. -/
theorem graphPositive_fpdim (X : Dᴹᵒᵖ) :
    (graphEndSkeleton S α).fpdim ((graphPositive S α).obj X) = S.fpdim X.unmop := by
  have h := (GraphLagrangian.underlyingSeparableNoPivotal S α).orbitEnd_fpdim_underlying S
    (GraphLagrangian.underlying_id_ne_zero S α) ((graphPositive S α).obj X)
    (GraphLagrangian.moduleOrbitBase S α)
  change S.fpdim ((GraphLagrangian.moduleOrbitBase S α).obj.X ⊗ X.unmop) =
    (graphEndSkeleton S α).fpdim _ * S.fpdim (GraphLagrangian.moduleOrbitBase S α).obj.X at h
  rw [S.fpdim_tensor] at h
  nlinarith [graphOrbitBase_fpdim_pos S α]

/-- Negative native alpha induction has the same actual object action,
so its actual End FP dimension is the same ambient FP dimension. -/
theorem graphNegative_fpdim (X : Dᴹᵒᵖ) :
    (graphEndSkeleton S α).fpdim ((graphNegative S α).obj X) = S.fpdim X.unmop := by
  have h := (GraphLagrangian.underlyingSeparableNoPivotal S α).orbitEnd_fpdim_underlying S
    (GraphLagrangian.underlying_id_ne_zero S α) ((graphNegative S α).obj X)
    (GraphLagrangian.moduleOrbitBase S α)
  change S.fpdim ((GraphLagrangian.moduleOrbitBase S α).obj.X ⊗ X.unmop) =
    (graphEndSkeleton S α).fpdim _ * S.fpdim (GraphLagrangian.moduleOrbitBase S α).obj.X at h
  rw [S.fpdim_tensor] at h
  nlinarith [graphOrbitBase_fpdim_pos S α]

end Paper18.Category.GraphPicard
