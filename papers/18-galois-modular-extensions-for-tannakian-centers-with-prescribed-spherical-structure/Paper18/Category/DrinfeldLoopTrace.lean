import Paper18.Category.DrinfeldLoopTraceProjection
import Paper18.Category.DrinfeldLoopTraceDiagram
import Paper18.Category.ENOPseudounitaryInductionUnit

/-! # The actual induction-loop trace formula

The nonunit trace vanishes through actual coend matrix decomposition and
the actual rigid Choi partial contraction. The unit trace is the dimension
of the actual induction object. No sphericality or ambient braiding is
needed.
-/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
open Classical
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- Every object with zero actual unit-Hom space has zero induction-loop trace. -/
theorem inductionLoop_rightTrace_eq_zero (A : C) (hA : ∀ a : 𝟙_ C ⟶ A, a = 0) :
    J.rightTrace (inductionLoop S J A).f = 0 := by
  apply inductionLoop_rightTrace_zero_of_annular S J A
  intro i u p
  exact inductionLoopAnnularTerm_rightTrace_eq_zero J (S.simpleObject i) A hA u p

variable [Simple (𝟙_ C)]

/-- The actual adjunction loop has categorical trace equal to the global
dimension at the unit simple label, and zero at every other simple label. -/
theorem inductionLoop_rightTrace (i : ι) :
    unitScalarEquiv (C := C)
      (J.rightTrace (inductionLoop S J (S.simpleObject i)).f) =
        if i = S.unitLabel then (J.pivotalData S).globalDimension else 0 := by
  by_cases hi : i = S.unitLabel
  · subst i
    simpa only [if_pos rfl] using inductionLoop_rightTrace_unitLabel S J
  · rw [if_neg hi, inductionLoop_rightTrace_eq_zero S J (S.simpleObject i)
      (simple_nonunit_from_unit_eq_zero S i hi)]
    exact map_zero _

end Paper18.Category.Drinfeld
