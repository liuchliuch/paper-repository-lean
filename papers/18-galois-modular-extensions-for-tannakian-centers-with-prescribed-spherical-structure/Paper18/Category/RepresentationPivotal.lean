import Paper18.Category.RepresentationPivotalVector

/-! # The actual canonical positive pivotal structure on finite representations -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe u
namespace Paper18.Category.Representation
attribute [local instance 2000] RightRigidCategory.rightDual
variable {G : Type} [Group G]

/-- The actual categorical dimension is ordinary vector-space dimension.
The forgetful functor's trace preservation was derived from the genuine
rigid double-dual comparison. -/
lemma pivotalStructure_rightDimension (V : FDRep ℂ G) :
    (pivotalStructure (G := G)).rightDimension V =
      (dimension V : ℂ) • 𝟙 (𝟙_ (FDRep ℂ G)) := by
  let F := Action.forget (FGModuleCat ℂ) G
  apply F.map_injective
  have h := (forget_preservesPivotal (G := G)).rightDimension V
  rw [vectorPivotal_rightDimension] at h
  change 𝟙 (𝟙_ (FGModuleCat ℂ)) ≫
      F.map ((pivotalStructure (G := G)).rightDimension V) ≫ 𝟙 (𝟙_ (FGModuleCat ℂ)) =
        (dimension V : ℂ) • 𝟙 (𝟙_ (FGModuleCat ℂ)) at h
  simpa only [Functor.map_smul, Functor.map_id, id_comp, comp_id] using h

@[simp] lemma pivotalStructure_rightDim (V : FDRep ℂ G) :
    (pivotalStructure (G := G)).rightDim V = (dimension V : ℂ) := by
  unfold PivotalStructure.rightDim
  rw [pivotalStructure_rightDimension, unitScalarEquiv_smul_id]

/-- Positivity is proved for every actual simple representation from its
computed actual trace and its nonzero finite vector dimension. -/
lemma pivotalStructure_positive : (pivotalStructure (G := G)).Positive := by
  intro V hV
  letI := hV
  rw [pivotalStructure_rightDim]
  constructor
  · exact_mod_cast dimension_pos V
  · simp

end Paper18.Category.Representation
