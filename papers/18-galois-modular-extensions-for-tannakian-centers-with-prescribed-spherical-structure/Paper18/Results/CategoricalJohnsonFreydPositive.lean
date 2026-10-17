import Paper18.External.JohnsonFreyd23
import Paper18.Category.PositiveGaloisExtensionRefinement

/-! # Positive refinement relative to the nonspherical external JF input

Only the published nonspherical extension existence theorem is a premise.
Actual positivity of its integral centralizer, literal Proposition 2.4,
and uniqueness of positive pivotal structures are proved in this project.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {G : Type} [Group G]

include S in
/-- The positive refinement keeps the prescribed positive structure on
the actual source embedding; no ambient pivotal structure is an input. -/
theorem positive_extension_of_johnsonFreyd23
    (hJF : Paper18.External.JohnsonFreyd23.{v,u,w})
    (J : PivotalStructure C) (hJ : J.Positive) (T : TannakianCenter C G) :
    Nonempty (PositiveGaloisExtension.{v,u,max u v,max u (v+1),max (max u v) w} J) := by
  obtain ⟨E⟩ := hJF S T
  exact E.exists_positiveRefinement S J hJ

end Paper18.Category
