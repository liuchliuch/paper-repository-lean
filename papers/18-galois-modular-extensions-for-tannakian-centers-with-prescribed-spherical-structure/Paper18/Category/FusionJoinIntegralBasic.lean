import Paper18.Category.FactorizationEssentialSurjectiveProduct
import Paper18.Category.Integrality

/-! # Actual integrality of Deligne products -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.DeligneProduct
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

/-- The actual Deligne product of integral fusion categories is integral,
by the actual simple-pair skeleton and its derived product FP dimensions. -/
theorem integral_of_integral (hS : S.Integral) (hT : T.Integral) :
    letI := hasKernels S T
    letI := simpleUnit S T
    (skeleton S T).Integral := by
  letI := hasKernels S T
  letI := simpleUnit S T
  apply (skeleton S T).integral_iff_basis.mpr
  intro p
  obtain ⟨n, hn⟩ := S.integral_iff_basis.mp hS p.1
  obtain ⟨m, hm⟩ := T.integral_iff_basis.mp hT p.2
  refine ⟨n * m, ?_⟩
  rw [fpdim_pair, hn, hm, Int.cast_mul]

end Paper18.Category.DeligneProduct
