import Paper18.Category.GraphLagrangianSpherical
import Paper18.Category.QuasiFusionCenter

/-! # Actual Lagrangian graph algebras for the constructed cocycle centers

Here the source category and its actual positive spherical structure have
already been constructed. Thus graph separability and both exact FP
dimension formulas require no external pivotal-existence assumption.
-/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
namespace Paper18.Category.GraphLagrangian.CocycleCenter
attribute [local instance 2000] RightRigidCategory.rightDual
open QuasiFusion
variable {G : Type} [Group G] [Fintype G] (ψ : ThreeCocycle G)

abbrev D := Center (CocycleVec ψ)

variable (α : D ψ ⥤ D ψ) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]

/-- The actual central graph algebra for a braided tensor autoequivalence
of the actual modular center of the actual cocycle category. -/
abbrev algebra : Center (D ψ) := GraphLagrangian.algebra (CocycleVec.centerSkeleton ψ) α

/-- Its actual separability section is constructed using the canonical
actual spherical structure already proved for this actual source category. -/
def separable : SeparableAlgebra (algebra ψ α) :=
  GraphLagrangian.separable (CocycleVec.centerSkeleton ψ) α
    (CocycleVec.centerPivotal ψ) (CocycleVec.centerPivotal_spherical ψ)

/-- Actual connectedness of the actual central graph algebra. -/
theorem connected : Module.finrank ℂ (𝟙_ (Center (D ψ)) ⟶ algebra ψ α) = 1 :=
  GraphLagrangian.connected (CocycleVec.centerSkeleton ψ) α
    (CocycleVec.center_nondegenerate ψ)

/-- The actual complete finite skeleton of the actual target center. -/
def targetSkeleton :=
  Drinfeld.centerSkeleton (CocycleVec.centerSkeleton ψ) (CocycleVec.centerPivotal ψ)

/-- The actual graph dimension is the actual dimension of its source,
computed explicitly from the finite grading group. -/
theorem fpdim : (targetSkeleton ψ).fpdim (algebra ψ α) = (Fintype.card G : ℝ) ^ 2 := by
  rw [GraphLagrangian.fpdim (CocycleVec.centerSkeleton ψ) α (targetSkeleton ψ)]
  exact CocycleVec.center_totalFPdim ψ

/-- The actual target center dimension is the square of the source
center dimension, hence the fourth power of the finite group's order. -/
theorem target_totalFPdim :
    (targetSkeleton ψ).fusionBasis.totalFPdim = (Fintype.card G : ℝ) ^ 4 := by
  change (Drinfeld.centerSkeleton (CocycleVec.centerSkeleton ψ)
    (CocycleVec.centerPivotal ψ)).fusionBasis.totalFPdim = _
  rw [GraphLagrangian.center_totalFPdim (CocycleVec.centerSkeleton ψ)
    (CocycleVec.centerPivotal ψ), CocycleVec.center_totalFPdim]
  ring

/-- The actual graph algebra satisfies the actual Lagrangian dimension
relation in the actual target center. -/
theorem dimension_square : ((targetSkeleton ψ).fpdim (algebra ψ α)) ^ 2 =
    (targetSkeleton ψ).fusionBasis.totalFPdim := by
  rw [fpdim, target_totalFPdim]
  ring

/-- The actual algebra used to form graph modules in the actual source
category is the underlying algebra of the actual central graph algebra. -/
def underlyingAlgebra : D ψ := (Center.forget (D ψ)).obj (algebra ψ α)

instance underlyingAlgebraMonObj : MonObj (underlyingAlgebra ψ α) :=
  Functor.monObjObj (F := Center.forget (D ψ)) (algebra ψ α)

/-- Actual separability survives actual strong-monoidal forgetting, so
modules over this actual source algebra admit the established semisimple
module constructions. -/
def underlyingSeparable : SeparableAlgebra (underlyingAlgebra ψ α) :=
  (separable ψ α).map (Center.forget (D ψ))

end Paper18.Category.GraphLagrangian.CocycleCenter
