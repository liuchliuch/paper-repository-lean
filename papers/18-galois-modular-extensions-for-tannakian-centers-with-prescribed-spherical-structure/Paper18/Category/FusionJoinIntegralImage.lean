import Paper18.Category.RelativeTensorCentralImage
import Paper18.Category.FusionSubcategoryIntegral

/-! # Actual integral tensor images for fusion joins -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.FiniteSemisimpleSkeleton
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
  (F : C ⥤ D) [F.Additive] [F.Monoidal] [F.Full] [F.Faithful]

/-- The actual full tensor image of an integral fusion category is integral.
Its summand and tensor closure are constructed from actual full faithfulness,
and its intrinsic FP dimensions are identified by the actual inclusion. -/
theorem essImageIntegral (hS : S.Integral) : T.FullSubcategoryIntegral F.essImage := by
  apply (T.fullSubcategoryIntegral_iff F.essImage).mpr
  intro i hi
  obtain ⟨X, ⟨e⟩⟩ := hi
  obtain ⟨n, hn⟩ := S.fpdim_integer hS X
  refine ⟨n, ?_⟩
  rw [← T.fpdim_iso e, S.fpdim_map T F X, hn]

end Paper18.Category.FiniteSemisimpleSkeleton
