import Paper18.Category.CentralizerDimensionFunctorRules
import Paper18.Category.FusionSubcategoryRigid
import Paper18.Category.PivotalFunctor

/-! # The dimension quotient of an actual dominant tensor functor -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Monoidal]

/-- Duality compatibility of the actual image multiplicities follows from
the canonical rigid comparison of the given tensor functor. -/
lemma imageCoeff_rightDual (i : ι) (j : κ) :
    S.imageCoeff T F (S.dualLabel i) j = S.imageCoeff T F i (T.dualLabel j) := by
  unfold imageCoeff
  rw [T.multiplicity_iso (F.mapIso (S.dualIso i) ≪≫ dualComparison F (S.simpleObject i))]
  exact T.multiplicity_rightDual _ _

/-- The total FP-dimension quotient is derived from the actual unit-image
multiplicities and dominance. No pivotal positivity is required. -/
lemma dominant_totalFPdim_eq
    (hF : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))) :
    S.fusionBasis.totalFPdim =
      (∑ i, (S.imageCoeff T F i T.unitLabel : ℝ) * S.fusionBasis.fpdim i) *
        T.fusionBasis.totalFPdim := by
  exact DominantDimension.totalFPdim_eq (S.fusionMap T F hF)
    (S.imageCoeff_rightDual T F)

end Paper18.Category.FiniteSemisimpleSkeleton
