import Paper18.Category.DrinfeldPivotalFunctor
import Paper18.Category.ModuleBalancingFunctor

/-! # The canonical braided lifts preserve the prescribed pivotal structure -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u v' u'
namespace Paper18.Category.PreservesPivotal
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  [RightRigidCategory D] [BraidedCategory D]
  {F : C ⥤ D} [F.Braided] {J : PivotalStructure C} {K : PivotalStructure D}

/-- Actual braided pivotal tensor functors preserve the actual balancing. -/
lemma twist (h : PreservesPivotal F J K) (X : C) :
    F.map (J.twistIso X).hom = (K.twistIso (F.obj X)).hom := by
  apply (cancel_mono (drinfeldIso (F.obj X)).hom).mp
  rw [K.twist_comp_drinfeld]
  rw [← doubleDualComparison_drinfeld F X]
  rw [← assoc, ← F.map_comp, J.twist_comp_drinfeld]
  exact h X

end Paper18.Category.PreservesPivotal

namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [LeftRigidCategory C] [BraidedCategory C]

/-- The actual positive braided embedding preserves the lifted pivotal structure. -/
theorem positive_preservesPivotal (J : PivotalStructure C) :
    PreservesPivotal (positive C) J (centerPivotal J) := by
  apply (preservesPivotal_iff_forget (positive C) J J).mpr
  intro X
  have hd (Y : C) : (dualComparison (positive C ⋙ Center.forget C) Y).hom =
      𝟙 (dual C Y) := by
    apply pairing_hom_ext (inferInstanceAs (ExactPairing Y (dual C Y)))
    have hy := dualComparison_evaluation (positive C ⋙ Center.forget C) Y
    simpa using hy
  have hi (Y : C) : dualComparison (positive C ⋙ Center.forget C) Y =
      Iso.refl (dual C Y) := Iso.ext (hd Y)
  simp only [doubleDualComparison, Iso.trans_hom, Iso.symm_hom, hi,
    dualMapIso, Iso.refl_hom, Iso.refl_inv]
  change J.j.hom.app X ≫ 𝟙 (dual C (dual C X)) ≫
    dualMap C (𝟙 (dual C X)) = J.j.hom.app X
  dsimp only [dualMap, dual]
  rw [rightAdjointMate_id]
  erw [Category.comp_id, Category.comp_id]

/-- The actual negative tensor embedding also preserves the same pivotal
structure, independently of the direction of its half-braiding. -/
theorem negative_preservesPivotal (J : PivotalStructure C) :
    PreservesPivotal (negative C) J (centerPivotal J) := by
  apply (preservesPivotal_iff_forget (negative C) J J).mpr
  intro X
  have hd (Y : C) : (dualComparison (negative C ⋙ Center.forget C) Y).hom =
      𝟙 (dual C Y) := by
    apply pairing_hom_ext (inferInstanceAs (ExactPairing Y (dual C Y)))
    have hy := dualComparison_evaluation (negative C ⋙ Center.forget C) Y
    simpa [negative] using hy
  have hi (Y : C) : dualComparison (negative C ⋙ Center.forget C) Y =
      Iso.refl (dual C Y) := Iso.ext (hd Y)
  simp only [doubleDualComparison, Iso.trans_hom, Iso.symm_hom, hi,
    dualMapIso, Iso.refl_hom, Iso.refl_inv]
  change J.j.hom.app X ≫ 𝟙 (dual C (dual C X)) ≫
    dualMap C (𝟙 (dual C X)) = J.j.hom.app X
  dsimp only [dualMap, dual]
  rw [rightAdjointMate_id]
  erw [Category.comp_id, Category.comp_id]

/-- The actual negative embedding is braided when its source carries the
reverse of the ambient braiding. This is an explicit local structure. -/
def negativeBraided :
    let F := negative C
    letI : BraidedCategory C := reverseBraiding C
    F.Braided := by
  let F := negative C
  letI : BraidedCategory C := reverseBraiding C
  constructor
  intro X Y
  apply Center.ext
  change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
  simp only [id_comp, comp_id]
  rfl

/-- The negative central lift carries the twist computed with the reversed
source braiding to the actual center twist. -/
lemma negative_twist (J : PivotalStructure C) (X : C) :
    (negative C).map
      (letI : BraidedCategory C := reverseBraiding C; (J.twistIso X).hom) =
        ((centerPivotal J).twistIso ((negative C).obj X)).hom := by
  let F := negative C
  have hp : PreservesPivotal F J (centerPivotal J) := negative_preservesPivotal J
  let hb := negativeBraided (C := C)
  letI : BraidedCategory C := reverseBraiding C
  letI : F.Braided := hb
  exact hp.twist X

end Paper18.Category.Drinfeld
