import Paper18.Category.SphericalizationMonoidal

/-! # Canonical dual comparisons needed for functorial sphericalization -/
noncomputable section
universe v u v₁ u₁
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [RightRigidCategory D]
  (F : C ⥤ D)

section Monoidal
variable [F.Monoidal]

/-- The canonical chosen-dual comparison is natural in actual morphisms,
with both contravariances displayed. -/
lemma dualComparison_naturality {X Y : C} (f : X ⟶ Y) :
    F.map (dualMap C f) ≫ (dualComparison F X).hom =
      (dualComparison F Y).hom ≫ dualMap D (F.map f) := by
  apply pairing_hom_ext (inferInstanceAs (ExactPairing (F.obj X) (dual D (F.obj X))))
  simp only [comp_whiskerRight, assoc]
  rw [dualComparison_evaluation]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← Functor.map_comp_assoc,
    rightAdjointMate_comp_evaluation, Functor.map_comp]
  simp only [assoc]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc, dualComparison_evaluation]

lemma dualComparison_inv_naturality {X Y : C} (f : X ⟶ Y) :
    (dualComparison F Y).inv ≫ F.map (dualMap C f) =
      dualMap D (F.map f) ≫ (dualComparison F X).inv := by
  apply (cancel_epi (dualComparison F Y).hom).mp
  simp only [← assoc, Iso.hom_inv_id, id_comp]
  rw [← dualComparison_naturality, assoc, Iso.hom_inv_id, comp_id]

/-- The canonical double-dual comparison is a genuine natural comparison. -/
lemma doubleDualComparison_naturality {X Y : C} (f : X ⟶ Y) :
    F.map ((doubleDualFunctor C).map f) ≫ (doubleDualComparison F Y).hom =
      (doubleDualComparison F X).hom ≫ (doubleDualFunctor D).map (F.map f) := by
  dsimp only [doubleDualComparison, Iso.trans_hom, Iso.symm_hom, dualMapIso]
  have hn := dualComparison_naturality F (dualMap C f)
  have hi := congrArg (dualMap D) (dualComparison_inv_naturality F f)
  dsimp only [doubleDualFunctor, dualMap] at hn hi ⊢
  simp only [comp_rightAdjointMate] at hi
  rw [← assoc, hn, assoc, hi]
  simp only [assoc]

/-- The canonical double-dual comparison as an actual natural isomorphism. -/
def doubleDualComparisonNatIso : doubleDualFunctor C ⋙ F ≅ F ⋙ doubleDualFunctor D :=
  NatIso.ofComponents (doubleDualComparison F) (fun f => doubleDualComparison_naturality F f)

/-- Transporting an arbitrary double-dual identification preserves its
actual cap. No pivotal coherence for that identification is assumed. -/
lemma doubleDualComparison_cap (X : C) (p : X ⟶ (doubleDualFunctor C).obj X) :
    F.obj X ◁ (dualComparison F X).hom ≫
      (F.map p ≫ (doubleDualComparison F X).hom) ▷ dual D (F.obj X) ≫
        ε_ (dual D (F.obj X)) (dual D (dual D (F.obj X))) =
      μ F X (dual C X) ≫ F.map (p ▷ dual C X ≫ ε_ (dual C X) (dual C (dual C X))) ≫ η F := by
  dsimp only [doubleDualComparison, Iso.trans_hom, Iso.symm_hom, dualMapIso]
  simp only [comp_whiskerRight, assoc]
  rw [rightAdjointMate_comp_evaluation (dualComparison F X).inv]
  rw [whisker_exchange_assoc, whisker_exchange_assoc]
  simp only [← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id, id_comp]
  rw [dualComparison_evaluation]
  have hn := Functor.LaxMonoidal.μ_natural_left F p (dual C X)
  dsimp only [doubleDualFunctor] at hn
  rw [reassoc_of% hn, F.map_comp]
  simp only [assoc]

end Monoidal

variable [BraidedCategory C] [BraidedCategory D] [F.Braided]

/-- Braided tensor functors preserve the canonical Drinfeld comparison,
using the canonical, rather than supplied, double-dual comparison. -/
lemma doubleDualComparison_drinfeld (X : C) :
    F.map (drinfeldIso X).hom ≫ (doubleDualComparison F X).hom =
      (drinfeldIso (F.obj X)).hom := by
  apply pairing_hom_ext
    (inferInstanceAs (ExactPairing (dual D (F.obj X)) (dual D (dual D (F.obj X)))))
  apply (cancel_epi (F.obj X ◁ (dualComparison F X).hom)).mp
  rw [doubleDualComparison_cap, drinfeldIso_evaluation]
  rw [Functor.map_comp]
  simp only [assoc]
  rw [Functor.LaxBraided.braided_assoc, ← dualComparison_evaluation]
  rw [drinfeldIso_evaluation, braiding_naturality_right_assoc]

end Paper18.Category
