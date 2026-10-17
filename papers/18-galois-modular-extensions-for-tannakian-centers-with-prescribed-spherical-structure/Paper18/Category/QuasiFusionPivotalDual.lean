import Paper18.Category.QuasiFusionRigid
import Paper18.Category.RepresentationPivotalBasic

/-! # Actual dual morphisms in the cocycle-twisted graded category -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
namespace Paper18.Category.QuasiFusion
attribute [local instance 2000] RightRigidCategory.rightDual
variable {G : Type} [Group G] [Fintype G] (ψ : ThreeCocycle G)

private lemma fiberMate_transport {A : Type} {X Y : A → FGModuleCat ℂ}
    (f : ∀ a, X a ⟶ Y a) {a b : A} (h : a = b) :
    dualMap (FGModuleCat ℂ) (f a) ≫ eqToHom (congrArg (fun c => (X c)ᘁ) h) =
      eqToHom (congrArg (fun c => (Y c)ᘁ) h) ≫ dualMap (FGModuleCat ℂ) (f b) := by
  subst b
  simp

/-- The chosen rigid mate is the actual pointwise vector-space mate. The
weighted cups and twisted associator cancel because evaluation is unchanged. -/
lemma dualMap_fiber {X Y : PointedVec (Additive G)} (f : X ⟶ Y) :
    letI := twistedMonoidalCategory ψ
    letI := twistedRightRigid ψ
    dualMap (PointedVec (Additive G)) f =
      (fun a => dualMap (FGModuleCat ℂ) (f (-a))) := by
  letI := twistedMonoidalCategory ψ
  letI := twistedRightRigid ψ
  let g : PointedVec.gradedDual Y ⟶ PointedVec.gradedDual X :=
    fun a => dualMap (FGModuleCat ℂ) (f (-a))
  change dualMap (PointedVec (Additive G)) f = g
  symm
  apply pairing_hom_ext
    (inferInstanceAs (ExactPairing X (dual (PointedVec (Additive G)) X)))
  rw [rightAdjointMate_comp_evaluation]
  funext k
  by_cases hk : k = 0
  · subst k
    apply GradedObject.Monoidal.tensorObj_ext
    intro a b h
    change GradedObject.Monoidal.ιTensorObj (PointedVec.gradedDual Y) X a b 0 h ≫
        (GradedObject.Monoidal.tensorHom g (𝟙 X) 0 ≫ PointedVec.gradedEvaluation X 0) =
      GradedObject.Monoidal.ιTensorObj (PointedVec.gradedDual Y) X a b 0 h ≫
        (GradedObject.Monoidal.tensorHom (𝟙 (PointedVec.gradedDual Y)) f 0 ≫
          PointedVec.gradedEvaluation Y 0)
    rw [GradedObject.Monoidal.ι_tensorHom_assoc,
      GradedObject.Monoidal.ι_tensorHom_assoc,
      PointedVec.inclusion_evaluation_zero, PointedVec.inclusion_evaluation_zero]
    have ha : a = -b := eq_neg_of_add_eq_zero_left h
    subst a
    simp only [PointedVec.dualPairIso_canonical]
    simp only [PointedVec.id_apply, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom, assoc]
    have ht : g (-b) ≫ (PointedVec.dualFiberIso X b).hom =
        (PointedVec.dualFiberIso Y b).hom ≫ dualMap (FGModuleCat ℂ) (f b) :=
      fiberMate_transport f (neg_neg b)
    rw [← comp_whiskerRight_assoc, ht, comp_whiskerRight, assoc,
      reassoc_of% (rightAdjointMate_comp_evaluation (f b)), ← whisker_exchange_assoc]
  · have hz : IsZero ((𝟙_ (PointedVec (Additive G))) k) :=
      (GradedObject.Monoidal.isInitialTensorUnitApply k hk).isZero
    exact hz.eq_of_tgt _ _

end Paper18.Category.QuasiFusion
