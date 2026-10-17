import Paper18.Category.FixedBoundaryMinimalExistenceEquivariantGrading
import Paper18.Category.TannakianDescentMonoidal
import Paper18.Category.RelativeTensorCentralDimensionBasic
import Paper18.Category.SemisimpleCokernels

/-! # Exact FP dimensions for genuine C₂ crossed extension assembly -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Paper18.Category.CrossedBraidedGauging
universe v u w v' u' w'
namespace Paper18.Category.FixedBoundary.MinimalExistence
section Graded
variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {P : Grading C2 D} {H : WeakAction C2 D}
  [∀ g : C2, (H.ρ g).Monoidal] [H.IsMonoidal]
  [∀ g : C2, (H.ρ g).Additive] [∀ g : C2, (H.ρ g).Linear ℂ]
  {κ : Type w} [Fintype κ] (SD : FiniteSemisimpleSkeleton D κ)

/-- The actual C₂ gauging has four times the actual neutral FP support.
Both factors of two come from proved categorical constructions. -/
theorem gauging_total_eq_four_neutral (hf : P.Faithful) :
    (H.equivariantSkeleton SD).fusionBasis.totalFPdim =
      4 * SD.supportFPdim (neutralProperty P) := by
  rw [H.totalFPdim_equivariant SD, totalFPdim_eq_twice_neutral P SD hf]
  norm_num
  ring

/-- The actual neutral equivariant part has exactly the total dimension
of the entire un-gauged C₂ extension. -/
theorem gauging_neutral_support_eq_total (Q : GradedAction P H) (hf : P.Faithful) :
    (H.equivariantSkeleton SD).supportFPdim (neutralProperty (equivariantGrading Q)) =
      SD.fusionBasis.totalFPdim := by
  have hi := totalFPdim_eq_twice_neutral (equivariantGrading Q)
    (H.equivariantSkeleton SD) (equivariantGrading_faithful Q hf)
  have ht := H.totalFPdim_equivariant SD
  norm_num at ht
  linarith

end Graded

section Tannakian
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [HasCoequalizers C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (T : TannakianCenter C C2)

/-- The original category has twice the FP dimension of its actual
regular-algebra de-equivariantization, by genuine descent and induction. -/
theorem tannakian_total_fpdim :
    letI := T.deequivariantRightRigid
    letI := T.deequivariantSimpleUnit S
    S.fusionBasis.totalFPdim = 2 * (T.deequivariantSkeleton S).fusionBasis.totalFPdim := by
  letI := T.deequivariantRightRigid
  letI := T.deequivariantSimpleUnit S
  have he := RelativeTensor.totalFPdim_eq_of_equivalence S
    (T.deequivariantAction.equivariantSkeleton (T.deequivariantSkeleton S)) T.descentComparison
  rw [T.deequivariantAction.totalFPdim_equivariant (T.deequivariantSkeleton S)] at he
  norm_num at he
  exact he

end Tannakian
end Paper18.Category.FixedBoundary.MinimalExistence
