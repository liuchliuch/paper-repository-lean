import Paper18.Category.PointedRepEquivalence
import Paper18.Category.PointedRealization
import Paper18.Category.TannakianBasic

/-! # The actual Tannakian center and full Appendix B counterexample

The representation inclusion is the inverse of the constructed braided
equivalence, followed by the actual inclusion of transparent objects into B.
Its essential image is proved to be exactly the Müger center.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.AppendixBPointed
open RepresentationZ2

/-- The actual representation inclusion into the centralizer category. -/
def repZ2Inclusion : FDRep ℂ H ⥤ B :=
  repZ2Equivalence.inverse ⋙ centralizerInclusion (Set.univ : Set B)

instance repZ2Inclusion_braided : repZ2Inclusion.Braided := by
  dsimp [repZ2Inclusion]
  infer_instance

instance repZ2Inclusion_additive : repZ2Inclusion.Additive := by
  dsimp [repZ2Inclusion]
  infer_instance

instance repZ2Inclusion_linear : repZ2Inclusion.Linear ℂ := by
  dsimp [repZ2Inclusion]
  infer_instance

instance repZ2Inclusion_full : repZ2Inclusion.Full := by
  dsimp [repZ2Inclusion]
  infer_instance

instance repZ2Inclusion_faithful : repZ2Inclusion.Faithful := by
  dsimp [repZ2Inclusion]
  infer_instance

/-- The image characterization concerns every actual object of B. -/
theorem repZ2Inclusion_image_iff (X : B) :
    repZ2Inclusion.essImage X ↔ X ∈ mugerCenter := by
  constructor
  · rintro ⟨V, ⟨i⟩⟩ Y hY
    exact (centralizes_iso_left i).mp ((repZ2Equivalence.inverse.obj V).property Y hY)
  · intro hX
    let Z : BCenter := ⟨X, hX⟩
    refine ⟨repZ2Equivalence.functor.obj Z, ⟨?_⟩⟩
    exact (centralizerInclusion (Set.univ : Set B)).mapIso
      (repZ2Equivalence.unitIso.app Z).symm

/-- An actual Tannakian identification of the full transparent center of B. -/
def tannakianCenter : TannakianCenter B H where
  finite_group := inferInstance
  inclusion := repZ2Inclusion
  braided := repZ2Inclusion_braided
  additive := repZ2Inclusion_additive
  linear := repZ2Inclusion_linear
  full := repZ2Inclusion_full
  faithful := repZ2Inclusion_faithful
  image_iff := repZ2Inclusion_image_iff

/-- The full actual Appendix B counterexample, including its Tannakian
center. The prescribed spherical structure fixes that entire center and
extends pivotally to the fixed minimal modular extension, but no spherical
pivotal extension through that inclusion exists. -/
theorem appendixB_actual_counterexample :
    ∃ T : TannakianCenter B H,
      T.inclusion = repZ2Inclusion ∧
      IsModular canonicalPivotal ∧
      canonicalPivotal.twistNatIso = twist ∧
      prescribedPivotal.Spherical ∧
      centerPrescribedPivotal = centerCanonicalPivotal ∧
      PreservesPivotal BInclusion prescribedPivotal nonsphericalPivotalExtension ∧
      ¬ nonsphericalPivotalExtension.Spherical ∧
      (∀ J : PivotalStructure Vec, J.Spherical →
        ¬ PreservesPivotal BInclusion prescribedPivotal J) ∧
      (PointedVec.skeleton Paper18.PointedA).fusionBasis.totalFPdim =
        bSkeleton.fusionBasis.totalFPdim * bCenterSkeleton.fusionBasis.totalFPdim :=
  ⟨tannakianCenter, rfl, appendixB_actual_obstruction⟩

end Paper18.Category.AppendixBPointed
