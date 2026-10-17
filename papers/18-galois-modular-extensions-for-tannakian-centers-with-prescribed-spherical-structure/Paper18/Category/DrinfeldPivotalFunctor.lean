import Paper18.Category.DrinfeldPivotal
import Paper18.Category.PivotalFunctorComposition

/-! # Pivotal functors into the actual Drinfeld center -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u v₁ u₁ v₂ u₂
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual

namespace PreservesPivotal
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [RightRigidCategory D]
  {E : Type u₂} [Category.{v₂} E] [MonoidalCategory E] [RightRigidCategory E]
  {F : C ⥤ D} {G : D ⥤ E} [F.Monoidal] [G.Monoidal] [G.Faithful]
  {J : PivotalStructure C} {K : PivotalStructure D} {L : PivotalStructure E}

/-- Faithful pivotal tensor functors reflect pivotal preservation, using
actual composition coherence of the canonical double-dual comparisons. -/
theorem of_comp (hG : PreservesPivotal G K L)
    (h : PreservesPivotal (F ⋙ G) J L) : PreservesPivotal F J K := by
  intro X
  apply G.map_injective
  apply (cancel_mono (doubleDualComparison G (F.obj X)).hom).mp
  have hh := h X
  rw [Functor.comp_map, doubleDualComparison_comp_hom, ← assoc, ← G.map_comp] at hh
  exact hh.trans (hG (F.obj X)).symm

end PreservesPivotal

namespace Drinfeld
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [LeftRigidCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [RightRigidCategory D]

/-- Pivotal preservation into the center is detected by its canonical
faithful pivotal forgetful functor. -/
theorem preservesPivotal_iff_forget (F : D ⥤ Center C) [F.Monoidal]
    (K : PivotalStructure D) (J : PivotalStructure C) :
    PreservesPivotal F K (centerPivotal J) ↔
      PreservesPivotal (F ⋙ Center.forget C) K J :=
  ⟨fun h => h.comp (forget_preservesPivotal J),
    fun h => (forget_preservesPivotal J).of_comp h⟩

end Drinfeld
end Paper18.Category
