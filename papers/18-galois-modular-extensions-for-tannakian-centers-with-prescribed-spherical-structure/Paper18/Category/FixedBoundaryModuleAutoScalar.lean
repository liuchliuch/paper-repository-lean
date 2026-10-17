import Paper18.Category.FixedBoundaryModuleScalar
import Paper18.Category.FunctorImage

/-! # Scalar coordinates derived for actual regular-module autoequivalences -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (F : C ⥤ C) [F.LeftLinear C] [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]

include S in
/-- The actual regular-module automorphism scalar is derived from full
faithfulness, the simple tensor unit, the actual module lineator, and
Schur's lemma. No scalar-coordinate or automorphism-classification field
is supplied. -/
theorem regularModuleAut_unique_scalar (τ : F ≅ F) [IsModuleNatural C τ.hom] :
    ∃! z : ℂˣ, ∀ X : C, τ.hom.app X = (z : ℂ) • 𝟙 (F.obj X) := by
  letI := S.simple_map F (𝟙_ C)
  exact exists_unique_moduleScalarUnit F τ

end Paper18.Category.ModuleFunctor
