import Paper18.Category.ENOPseudounitaryBounds
import Paper18.Category.RigidRetracts

/-!
# Integrality of actual pivotal idempotent traces

An actual idempotent in a finite semisimple rigid category splits, and its
pivotal trace is the categorical dimension of its image. The latter is an
algebraic integer by the actual simple decomposition and fusion equations.
This is the integrality step needed after constructing a suitable projection
on central induction; no projection or ratio-integrality conclusion is
postulated here.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w

namespace Paper18.Category.PivotalStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

include S in
/-- The actual categorical dimension of every object is an algebraic integer. -/
theorem rightDim_isIntegral (X : C) : IsIntegral ℤ (J.rightDim X) := by
  rw [J.rightDim_eq_sum_multiplicity S X]
  apply IsIntegral.sum
  intro i _
  have hn : IsIntegral ℤ (S.multiplicity X i : ℂ) := by
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ)
      (x := (S.multiplicity X i : ℤ)))
  exact hn.mul ((J.pivotalData S).jdim_isIntegral i)

omit [HasFiniteBiproducts C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- Cyclicity identifies the trace of a split projection with the dimension
of its actual image object. -/
theorem rightTrace_split_projection {X Y : C} (i : Y ⟶ X) (p : X ⟶ Y)
    (hip : i ≫ p = 𝟙 Y) :
    unitScalarEquiv (C := C) (J.rightTrace (p ≫ i)) = J.rightDim Y := by
  rw [J.rightTrace_comp p i, hip]
  rfl

include S in
/-- The pivotal trace of every actual idempotent is an algebraic integer.
Only kernels in the original category are needed to split it; no finite
semisimple skeleton of the Drinfeld center is needed. -/
theorem rightTrace_idempotent_isIntegral {X : C} (e : X ⟶ X)
    (he : e ≫ e = e) :
    IsIntegral ℤ (unitScalarEquiv (C := C) (J.rightTrace e)) := by
  letI := idempotentCompleteOfKernels (C := C)
  obtain ⟨Y, i, p, hip, hpi⟩ := IsIdempotentComplete.idempotents_split X e he
  rw [← hpi, J.rightTrace_split_projection i p hip]
  exact J.rightDim_isIntegral S Y

end Paper18.Category.PivotalStructure
