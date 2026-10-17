import Paper18.Category.SphericalizationFunctor

/-! # Canonical pivotal comparison under composition of tensor functors -/
noncomputable section
universe v u v₁ u₁ v₂ u₂
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [RightRigidCategory D]
  {E : Type u₂} [Category.{v₂} E] [MonoidalCategory E] [RightRigidCategory E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal]

/-- Chosen-dual comparisons compose, as proved from their evaluation
characterization and the tensor functor coherence laws. -/
lemma dualComparison_comp_hom (X : C) :
    (dualComparison (F ⋙ G) X).hom =
      G.map (dualComparison F X).hom ≫ (dualComparison G (F.obj X)).hom := by
  apply pairing_hom_ext
    (inferInstanceAs (ExactPairing (G.obj (F.obj X)) (dual E (G.obj (F.obj X)))))
  have hc := dualComparison_evaluation (F ⋙ G) X
  dsimp only [Functor.comp_obj] at hc
  rw [hc]
  simp only [comp_whiskerRight, assoc]
  rw [dualComparison_evaluation, μ_natural_left_assoc,
    ← G.map_comp_assoc, dualComparison_evaluation]
  simp only [Functor.LaxMonoidal.comp_μ, Functor.OplaxMonoidal.comp_η,
    Functor.comp_map, Functor.map_comp, assoc]

lemma dualComparison_comp (X : C) : dualComparison (F ⋙ G) X =
    G.mapIso (dualComparison F X) ≪≫ dualComparison G (F.obj X) :=
  Iso.ext (dualComparison_comp_hom F G X)

lemma dualComparison_comp_inv (X : C) :
    (dualComparison (F ⋙ G) X).inv =
      (dualComparison G (F.obj X)).inv ≫ G.map (dualComparison F X).inv :=
  congrArg Iso.inv (dualComparison_comp F G X)

/-- Double-dual comparisons satisfy the actual composition coherence. -/
lemma doubleDualComparison_comp_hom (X : C) :
    (doubleDualComparison (F ⋙ G) X).hom =
      G.map (doubleDualComparison F X).hom ≫
        (doubleDualComparison G (F.obj X)).hom := by
  dsimp only [doubleDualComparison, Iso.trans_hom, Iso.symm_hom, dualMapIso]
  rw [dualComparison_comp_hom, dualComparison_comp_inv]
  simp only [comp_rightAdjointMate, Functor.map_comp, assoc]
  rw [← reassoc_of% (dualComparison_naturality G (dualComparison F X).inv)]

namespace PreservesPivotal
variable {F G} {JC : PivotalStructure C} {JD : PivotalStructure D}
  {JE : PivotalStructure E}

/-- Pivotal tensor functors compose, using canonical comparison coherence. -/
theorem comp (hF : PreservesPivotal F JC JD) (hG : PreservesPivotal G JD JE) :
    PreservesPivotal (F ⋙ G) JC JE := by
  intro X
  rw [Functor.comp_map, doubleDualComparison_comp_hom, ← assoc,
    ← G.map_comp, hF X, hG (F.obj X)]
  rfl

end PreservesPivotal
end Paper18.Category
