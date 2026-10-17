import Paper18.Category.TannakianC2GeneratorDecomposition
import Paper18.Category.TwoObjectSupport

/-! # Intrinsic support and dimension of an actual C₂ Tannakian center -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.TannakianCenter
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [HasFiniteBiproducts C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RightRigidCategory C] [Simple (𝟙_ C)]
  (T : TannakianCenter C RepresentationZ2.H)
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include T S

theorem c2Generator_simple : Simple T.c2Generator :=
  T.c2GeneratorTensorInverse.simple S

/-- The intrinsic FP dimension of the actual Müger center is two, derived
from its actual unit/sign support and actual tensor inverse. -/
theorem c2Generator_centerFPdim : S.centralizerFPdim (Set.univ : Set C) = 2 := by
  have hs : S.centralizerFPdim (Set.univ : Set C) =
      S.supportFPdim (fun X => Nonempty (X ≅ 𝟙_ C) ∨ Nonempty (X ≅ T.c2Generator)) := by
    apply Finset.sum_congr rfl
    intro i _
    change (if S.simpleObject i ∈ mugerCenter (C := C) then _ else _) = _
    rw [T.c2Generator_simple_transparent_iff]
  rw [hs]
  exact S.twoObject_supportFPdim T.c2GeneratorTensorInverse T.c2Generator_nonunit

end Paper18.Category.TannakianCenter
