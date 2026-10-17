import Paper18.Category.PivotalFunctorTensor

/-! # Canonical dual comparison under actual monoidal natural isomorphisms -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
universe v u v' u'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]
  {F H : C ⥤ D} [F.Monoidal] [H.Monoidal]
  (e : F ≅ H) [NatTrans.IsMonoidal e.hom]

/-- The unit component of a monoidal natural isomorphism also preserves
the actual inverse unit maps of the strong functors. -/
lemma monoidalNatIso_eta : e.hom.app (𝟙_ C) ≫ η H = η F := by
  apply (cancel_epi (ε F)).mp
  rw [← assoc, NatTrans.IsMonoidal.unit (τ := e.hom)]
  simp only [ε_η]

/-- The actual canonical dual comparison is natural under a monoidal
natural isomorphism, as follows from uniqueness of evaluation pairings. -/
lemma dualComparison_monoidalIso (X : C) :
    e.hom.app (dual C X) ≫ (dualComparison H X).hom ≫ dualMap D (e.hom.app X) =
      (dualComparison F X).hom := by
  apply pairing_hom_ext
    (inferInstanceAs (ExactPairing (F.obj X) (dual D (F.obj X))))
  simp only [comp_whiskerRight, assoc]
  rw [rightAdjointMate_comp_evaluation (e.hom.app X)]
  rw [← whisker_exchange_assoc]
  rw [← tensorHom_def_assoc, dualComparison_evaluation, dualComparison_evaluation]
  rw [← NatTrans.IsMonoidal.tensor_assoc, ← e.hom.naturality_assoc,
    monoidalNatIso_eta e]

/-- Solved form of actual dual comparison naturality. -/
lemma dualComparison_monoidalIso_solved (X : C) :
    e.hom.app (dual C X) ≫ (dualComparison H X).hom =
      (dualComparison F X).hom ≫ dualMap D (e.inv.app X) := by
  apply (cancel_mono (dualMap D (e.hom.app X))).mp
  rw [assoc, dualComparison_monoidalIso e X]
  have hi : dualMap D (e.inv.app X) ≫ dualMap D (e.hom.app X) = 𝟙 _ :=
    (dualMapIso (e.app X)).inv_hom_id
  simp only [assoc, hi, comp_id]

/-- Isomorphism form of canonical dual comparison naturality. -/
lemma dualComparison_monoidalIso_eq (X : C) :
    e.app (dual C X) ≪≫ dualComparison H X =
      dualComparison F X ≪≫ (dualMapIso (e.app X)).symm :=
  Iso.ext (dualComparison_monoidalIso_solved e X)

/-- The inverse equation records the actual transported chosen dual. -/
lemma dualComparison_monoidalIso_inverse (X : C) :
    (dualComparison H X).inv ≫ e.inv.app (dual C X) =
      dualMap D (e.hom.app X) ≫ (dualComparison F X).inv :=
  congrArg Iso.inv (dualComparison_monoidalIso_eq e X)

/-- The actual canonical double-dual comparison is natural under an
actual monoidal natural isomorphism, without a braiding hypothesis. -/
lemma doubleDualComparison_monoidalIso (X : C) :
    e.hom.app ((doubleDualFunctor C).obj X) ≫ (doubleDualComparison H X).hom =
      (doubleDualComparison F X).hom ≫ (doubleDualFunctor D).map (e.hom.app X) := by
  simp only [doubleDualComparison, Iso.trans_hom, Iso.symm_hom, dualMapIso, assoc]
  dsimp only [doubleDualFunctor]
  rw [← assoc, dualComparison_monoidalIso_solved e (dual C X)]
  rw [assoc, ← comp_rightAdjointMate, dualComparison_monoidalIso_inverse e X]
  simp only [comp_rightAdjointMate, assoc]

namespace PreservesPivotal
include e
variable {J : PivotalStructure C} {K : PivotalStructure D}

/-- Monoidal natural isomorphisms transport actual pivotal preservation
through the canonical double-dual comparison, with no braiding assumption. -/
theorem of_monoidalIso (h : PreservesPivotal F J K) : PreservesPivotal H J K := by
  intro X
  apply (cancel_epi (e.hom.app X)).mp
  rw [← e.hom.naturality_assoc, doubleDualComparison_monoidalIso,
    ← assoc, h X]
  exact (K.j.hom.naturality (e.hom.app X)).symm

end PreservesPivotal
end Paper18.Category
