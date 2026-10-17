import Paper18.Category.FusionCategory
import Paper18.Category.SemisimpleComplement
import Paper18.Category.SemisimpleSplitting

/-! # Actual FP dimension detects equality of actual semisimple subobjects -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Binary additivity is the actual binary Hom universal property. -/
lemma fpdim_biprod (X Y : C) : S.fpdim (X ⊞ Y) = S.fpdim X + S.fpdim Y := by
  simp only [fpdim, multiplicity, finrank_hom_biprod, Nat.cast_add,
    add_mul, Finset.sum_add_distrib]

/-- An actual monic subobject of equal actual FP dimension is the whole
object: the actual split complement has zero dimension and hence is zero. -/
theorem isIso_of_mono_fpdim_eq {X Y : C} (f : X ⟶ Y) [Mono f]
    (h : S.fpdim X = S.fpdim Y) : IsIso f := by
  let s := S.splitMono f
  have hd : S.fpdim Y = S.fpdim X + S.fpdim (kernel s.retraction) :=
    (S.fpdim_iso (splitMonoComplementIso f s)).trans (S.fpdim_biprod _ _)
  have hz : S.fpdim (kernel s.retraction) = 0 := by linarith
  exact splitMono_isIso_of_isZero_complement f s
    ((S.fpdim_eq_zero_iff _).mp hz)

end Paper18.Category.FiniteSemisimpleSkeleton
