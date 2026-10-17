import Paper18.Category.GraphPicardMoritaImageCentral
import Paper18.Category.NondegenerateBraidedFunctor
import Paper18.Category.FiniteSemisimpleLeftRigid
import Paper18.Category.DrinfeldExact

/-! # Full faithfulness of the actual central lift on its actual image

All center-target hypotheses follow from the actual image skeleton and
actual derived dual closure. The underlying ambient need not be braided.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.GraphPicard.MoritaImage
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C] [HasKernels C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RightRigidCategory C]
  [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {E : Type u'} [Category.{v'} E] [Preadditive E] [Linear ℂ E]
  [HasFiniteBiproducts E] [HasKernels E] [MonoidalCategory E]
  [MonoidalPreadditive E] [MonoidalLinear ℂ E] [RightRigidCategory E]
  [Simple (𝟙_ E)] [∀ X Y : E, FiniteDimensional ℂ (X ⟶ Y)]
  (K : C ⥤ Center E) [K.Braided] [K.Additive] [K.Linear ℂ]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton E κ)

/-- Actual source nondegeneracy makes the actual central restriction full
and faithful, without an ambient braiding or a supplied image equivalence. -/
def centralCoreFullyFaithful (hC : IsNondegenerate (C := C)) :
    (centralCore K).FullyFaithful := by
  let U := K ⋙ Center.forget E
  letI := hasKernels U T
  letI := rightRigid U T
  letI := simpleUnit U T
  let TI := skeleton U T
  letI := FiniteSemisimpleLeftRigid.leftRigidCategory TI
  exact NondegenerateBraidedFunctor.fullyFaithful S (centralCore K) hC

end Paper18.Category.GraphPicard.MoritaImage
