import Paper18.Category.DrinfeldPivotalFunctor
import Paper18.Category.PivotalFunctorNatIso

/-! # Actual pivotal preservation by lifts of monoidal functors to centers

The canonical forgetful functor is faithful and pivotal for the constructed
center pivotal structure. Thus a monoidal commuting square with the actual
underlying pivotal functor determines pivotal preservation of a center lift.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u v' u'
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [LeftRigidCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  [RightRigidCategory D] [LeftRigidCategory D]
  (F : C ⥤ D) [F.Monoidal]
  (L : Center C ⥤ Center D) [L.Monoidal]
  (e : L ⋙ Center.forget D ≅ Center.forget C ⋙ F) [NatTrans.IsMonoidal e.hom]
  (J : PivotalStructure C) (K : PivotalStructure D)

include e

/-- An actual monoidal lift to centers preserves the actual center pivotal
structures whenever its underlying strong monoidal functor preserves the
ambient ones. The commuting-square isomorphism is required to be monoidal;
no category braiding or scalar dimension assumption enters the proof. -/
theorem centerLift_preservesPivotal (hF : PreservesPivotal F J K) :
    PreservesPivotal L (centerPivotal J) (centerPivotal K) := by
  letI : NatTrans.IsMonoidal e.symm.hom := by
    change NatTrans.IsMonoidal e.inv
    infer_instance
  apply (forget_preservesPivotal K).of_comp
  have h := (forget_preservesPivotal J).comp hF
  exact h.of_monoidalIso e.symm

end Paper18.Category.Drinfeld
