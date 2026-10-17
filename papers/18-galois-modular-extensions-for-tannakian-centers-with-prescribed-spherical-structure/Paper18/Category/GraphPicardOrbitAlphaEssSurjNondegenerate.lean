import Paper18.Category.GraphPicardAlphaFull
import Paper18.Category.GraphPicardOrbitAlphaEssSurj

/-! # Actual graph alpha equivalences from nondegeneracy

The actual commutant proof supplies fullness. The independent actual orbit
FP-dimension calculation supplies essential surjectivity. Together these
construct actual alpha equivalences, without any fullness, dimension-equality
or Azumaya-equivalence premise.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]
  (hD : IsNondegenerate (C := D))
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- Positive native graph alpha induction is actually essentially
surjective, by the actual commutant fullness theorem and actual equal total
FP dimensions. -/
def graphPositiveEssSurjOfNondegenerate : (graphPositive S α).EssSurj := by
  letI := graphPositiveFull S α hD
  infer_instance

/-- Negative native graph alpha induction is actually essentially surjective. -/
def graphNegativeEssSurjOfNondegenerate : (graphNegative S α).EssSurj := by
  letI := graphNegativeFull S α hD
  infer_instance

/-- Actual nondegeneracy proves that the actual positive alpha functor
is an actual equivalence. -/
def graphPositiveIsEquivalenceOfNondegenerate : (graphPositive S α).IsEquivalence := by
  letI := graphPositiveFull S α hD
  infer_instance

/-- Actual nondegeneracy proves that the actual negative alpha functor
is an actual equivalence. -/
def graphNegativeIsEquivalenceOfNondegenerate : (graphNegative S α).IsEquivalence := by
  letI := graphNegativeFull S α hD
  infer_instance

/-- The actual positive strong monoidal graph equivalence. Its target
monoidal opposite is dictated by the native endofunctor tensor convention. -/
def graphPositiveMonoidalEquivalenceOfNondegenerate :
    Dᴹᵒᵖ ≌ (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α))ᴹᵒᵖ := by
  letI := graphPositiveFull S α hD
  exact graphPositiveMonoidalEquivalence S α

/-- The actual negative strong monoidal graph equivalence. -/
def graphNegativeMonoidalEquivalenceOfNondegenerate :
    Dᴹᵒᵖ ≌ (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α))ᴹᵒᵖ := by
  letI := graphNegativeFull S α hD
  exact graphNegativeMonoidalEquivalence S α

instance graphPositiveNondegenerateFunctorMonoidal :
    (graphPositiveMonoidalEquivalenceOfNondegenerate S α hD).functor.Monoidal :=
  inferInstanceAs (graphPositiveMop S α).Monoidal

instance graphNegativeNondegenerateFunctorMonoidal :
    (graphNegativeMonoidalEquivalenceOfNondegenerate S α hD).functor.Monoidal :=
  inferInstanceAs (graphNegativeMop S α).Monoidal

/-- The positive inverse has an actual strong tensor structure. -/
def graphPositiveNondegenerateInverseMonoidal :
    (graphPositiveMonoidalEquivalenceOfNondegenerate S α hD).inverse.Monoidal :=
  (graphPositiveMonoidalEquivalenceOfNondegenerate S α hD).inverseMonoidal

/-- The negative inverse has an actual strong tensor structure. -/
def graphNegativeNondegenerateInverseMonoidal :
    (graphNegativeMonoidalEquivalenceOfNondegenerate S α hD).inverse.Monoidal :=
  (graphNegativeMonoidalEquivalenceOfNondegenerate S α hD).inverseMonoidal

/-- The positive unit and counit have the actual monoidal compatibility. -/
def graphPositiveNondegenerateEquivalenceIsMonoidal :
    letI := graphPositiveNondegenerateInverseMonoidal S α hD
    (graphPositiveMonoidalEquivalenceOfNondegenerate S α hD).IsMonoidal := by
  letI := graphPositiveNondegenerateInverseMonoidal S α hD
  infer_instance

/-- The negative unit and counit have the actual monoidal compatibility. -/
def graphNegativeNondegenerateEquivalenceIsMonoidal :
    letI := graphNegativeNondegenerateInverseMonoidal S α hD
    (graphNegativeMonoidalEquivalenceOfNondegenerate S α hD).IsMonoidal := by
  letI := graphNegativeNondegenerateInverseMonoidal S α hD
  infer_instance

end Paper18.Category.GraphPicard
