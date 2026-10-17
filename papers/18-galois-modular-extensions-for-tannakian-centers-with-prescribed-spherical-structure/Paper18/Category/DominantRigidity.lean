import Paper18.Category.RigidRetracts
import Paper18.Category.PivotalFunctor

/-!
# Rigidity transferred by an actual dominant tensor functor

A strong monoidal functor transports the original cups and caps. If every
target object is an actual retract of an image, splitting the dual
idempotent supplies its right dual. No target duals or rigidity conclusions
are part of the dominance assumption.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
universe v u v₁ u₁
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- A strong monoidal functor transports an actual chosen right dual. -/
def imageHasRightDual (X : C) [HasRightDual X] : HasRightDual (F.obj X) where
  rightDual := F.obj Xᘁ
  exact := mapExactPairing F X Xᘁ

/-- An actual retract of a dualizable image has a right dual. -/
def hasRightDualOfImageRetract [IsIdempotentComplete D]
    {X : C} [HasRightDual X] {Y : D} (R : Retract Y (F.obj X)) : HasRightDual Y := by
  letI := imageHasRightDual F X
  exact hasRightDualOfRetract R

variable [RightRigidCategory C]

/-- Actual retract dominance of a strong monoidal functor transfers right
rigidity to an idempotent-complete target. -/
def rightRigidOfDominant [IsIdempotentComplete D]
    (hF : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))) : RightRigidCategory D where
  rightDual Y :=
    hasRightDualOfImageRetract F (Classical.choice (Classical.choose_spec (hF Y)))

/-- A preadditive target with kernels is already idempotent complete, so actual
retract dominance suffices to construct all its right duals. -/
def rightRigidOfDominantOfKernels [Preadditive D] [CategoryTheory.Limits.HasKernels D]
    (hF : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))) : RightRigidCategory D := by
  letI := idempotentCompleteOfKernels (C := D)
  exact rightRigidOfDominant F hF

end Paper18.Category
