import Paper18.Category.PivotalFunctorNatIso
import Paper18.Category.PivotalFunctorIdentity
import Paper18.Category.DrinfeldPivotalFunctor

/-! # Actual pivotal preservation by nonbraided monoidal inverses -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u v' u'
namespace Paper18.Category.PreservesPivotal
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]
  {F : C ⥤ D} [F.Monoidal] [F.Faithful] {G : D ⥤ C} [G.Monoidal]
  {J : PivotalStructure C} {K : PivotalStructure D}

/-- A strong monoidal inverse with an actual monoidal counit is pivotal
through its own canonical double-dual comparison. Neither category needs
a braiding and neither pivotal structure needs positivity. -/
theorem monoidal_inverse (e : G ⋙ F ≅ 𝟭 D) [NatTrans.IsMonoidal e.hom]
    (h : PreservesPivotal F J K) : PreservesPivotal G K J := by
  letI : NatTrans.IsMonoidal e.symm.hom := by
    change NatTrans.IsMonoidal e.inv
    infer_instance
  apply h.of_comp
  exact (preservesPivotal_identity K).of_monoidalIso e.symm

end Paper18.Category.PreservesPivotal
