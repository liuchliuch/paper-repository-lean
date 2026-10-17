import Paper18.Category.PointedPrescribed
import Paper18.Category.PointedSupport

noncomputable section

open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace Paper18.Category.AppendixBPointed

attribute [local instance 2000] RightRigidCategory.rightDual

/-- The modifying character is literally the identity on every actual
object of the centralizer's Müger center. -/
theorem bCharacter_trivial_on_center (X : BCenter) :
    (bCharacter Paper18.chi).hom.app X.obj = 𝟙 X.obj := by
  funext a
  change Paper18.chi a • 𝟙 (X.obj.obj a) = 𝟙 (X.obj.obj a)
  by_cases ha0 : a = 0
  · subst a
    simp
  · by_cases haf : a = Paper18.f
    · subst a
      rw [Paper18.appendixB_chi_on_f, one_smul]
    · exact (bCenter_fiber_isZero X a ha0 haf).eq_of_src _ _

def centerCanonicalPivotal : PivotalStructure BCenter :=
  bSkeleton.fullSubcategoryPivotal (centralizerProperty (Set.univ : Set B)) bCanonicalPivotal

def centerPrescribedPivotal : PivotalStructure BCenter :=
  bSkeleton.fullSubcategoryPivotal (centralizerProperty (Set.univ : Set B)) prescribedPivotal

private lemma pivotal_ext_center (J K : PivotalStructure BCenter) (h : J.j = K.j) : J = K := by
  cases J
  cases K
  cases h
  rfl

/-- The prescribed pivotal structure agrees with the canonical one on the
entire actual symmetric center, not just on its two simple labels. -/
theorem centerPrescribedPivotal_eq_canonical :
    centerPrescribedPivotal = centerCanonicalPivotal := by
  apply pivotal_ext_center
  ext X
  change (bCharacter Paper18.chi).hom.app X.obj ≫ bCanonicalPivotal.j.hom.app X.obj =
    bCanonicalPivotal.j.hom.app X.obj
  rw [bCharacter_trivial_on_center]
  exact Category.id_comp _

end Paper18.Category.AppendixBPointed
