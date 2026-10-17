import Paper18.Category.TannakianDescentTorsor
import Paper18.Category.FunctorRetract

/-! # The actual Tannakian descent equivalence of categories -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

/-- The actual comparison image is closed under the genuine equivariant
retracts constructed by regular-algebra averaging. -/
instance TannakianCenter.descentComparisonEssSurj : T.descentComparison.EssSurj := by
  letI : IsIdempotentComplete C :=
    (Idempotents.isIdempotentComplete_iff_idempotents_have_kernels (C := C)).mpr
      (fun X p _ => inferInstance)
  exact essSurj_of_retract_dominant T.descentComparison
    (fun M => ⟨M.obj.X, T.descentComparison_retract_dominant M⟩)

/-- Full faithfulness and actual equivariant retract descent make the
comparison functor an actual equivalence. -/
instance TannakianCenter.descentComparisonIsEquivalence : T.descentComparison.IsEquivalence where

/-- The original category is actually equivalent to the equivariantization
of its regular-algebra de-equivariantization by the actual translation
action of its finite Tannakian group. -/
def TannakianCenter.descentEquivalence : C ≌ T.deequivariantAction.Equivariant :=
  T.descentComparison.asEquivalence

end Paper18.Category
