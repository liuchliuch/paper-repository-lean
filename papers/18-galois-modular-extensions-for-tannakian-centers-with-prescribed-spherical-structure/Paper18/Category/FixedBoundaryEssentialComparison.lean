import Paper18.Category.FixedBoundaryRestrictBoundary
import Paper18.Category.RelativeTensorPivotalDominant

/-!
# Extending a specified comparison along an actual tensor equivalence

Fully faithful whiskering by an actual equivalence lifts the original
comparison. Its inverse is monoidal by detection on the actual essentially
surjective tensor image. The lifted comparison retains each specified
component exactly.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
universe v u v' u'
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (J : C ⥤ D) [J.IsEquivalence]
  (H : D ⥤ D) (a : J ⋙ H ≅ J)

/-- Actual fully faithful lifting of the specified comparison. -/
def comparisonOfEquivalence : H ≅ 𝟭 D :=
  ((whiskeringLeft C D D).obj J).preimageIso (a ≪≫ J.rightUnitor.symm)

/-- The original comparison is retained at every image object. -/
theorem comparisonOfEquivalence_component (X : C) :
    (comparisonOfEquivalence J H a).hom.app (J.obj X) = a.hom.app X := by
  have h := NatTrans.congr_app
    (((whiskeringLeft C D D).obj J).map_preimage (a ≪≫ J.rightUnitor.symm).hom) X
  change (comparisonOfEquivalence J H a).hom.app (J.obj X) =
    a.hom.app X ≫ 𝟙 (J.obj X) at h
  exact h.trans (Category.comp_id _)

theorem comparisonOfEquivalence_inv_component (X : C) :
    (comparisonOfEquivalence J H a).inv.app (J.obj X) = a.inv.app X := by
  exact (Iso.inv_eq_inv ((comparisonOfEquivalence J H a).app (J.obj X)) (a.app X)).mpr
    (comparisonOfEquivalence_component J H a X)

variable [J.Monoidal] [H.Monoidal] [ha : NatTrans.IsMonoidal a.hom]
include ha

/-- Actual monoidality follows from the original monoidal comparison,
with no choice of a replacement boundary map. -/
instance comparisonOfEquivalenceMonoidal :
    NatTrans.IsMonoidal (comparisonOfEquivalence J H a).hom := by
  let e := comparisonOfEquivalence J H a
  let a0 := a ≪≫ J.rightUnitor.symm
  have he : Functor.whiskerLeft J e.inv = a0.inv :=
    ((whiskeringLeft C D D).obj J).map_preimage a0.inv
  haveI : NatTrans.IsMonoidal a0.hom := by
    change NatTrans.IsMonoidal (a.hom ≫ J.rightUnitor.inv)
    infer_instance
  haveI : NatTrans.IsMonoidal (Functor.whiskerLeft J e.inv) := by
    rw [he]
    change NatTrans.IsMonoidal (a ≪≫ J.rightUnitor.symm).inv
    infer_instance
  haveI : NatTrans.IsMonoidal e.inv :=
    RelativeTensor.isMonoidal_of_retract_dominant J H e.inv (fun X =>
      ⟨J.objPreimage X, ⟨CategoryTheory.Retract.ofIso (J.objObjPreimageIso X).symm⟩⟩)
  refine { unit := ?_, tensor := ?_ }
  · rw [← NatTrans.IsMonoidal.unit (τ := e.inv), Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id]
  · intro X Y
    rw [← cancel_mono (e.inv.app (X ⊗ Y)), Category.assoc, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id, NatTrans.IsMonoidal.tensor (τ := e.inv),
      MonoidalCategory.tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app,
      Iso.hom_inv_id_app, tensorHom_id, id_whiskerRight, Category.id_comp]

end Paper18.Category.FixedBoundary
