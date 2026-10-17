import Paper18.Category.SphericalizationFusion
import Paper18.Category.EquivariantFPdim

/-! # Actual Frobenius--Perron dimension doubling under sphericalization -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

theorem simple_fpdim_equivariant (i : SimpleIndex S) :
    (skeleton S).fusionBasis.fpdim i =
      ((sphericalizationAction C).equivariantSkeleton S).fusionBasis.fpdim i := by
  have hs := (skeleton S).fpdim_map_simple S forget i
  have he := ((sphericalizationAction C).equivariantSkeleton S).fpdim_map_simple S
    (sphericalizationAction C).forget i
  rw [(skeleton S).fpdim_simple] at hs
  rw [((sphericalizationAction C).equivariantSkeleton S).fpdim_simple] at he
  exact hs.symm.trans he

theorem totalFPdim_eq_twice :
    (skeleton S).fusionBasis.totalFPdim = 2 * S.fusionBasis.totalFPdim := by
  calc
    _ = ((sphericalizationAction C).equivariantSkeleton S).fusionBasis.totalFPdim := by
      simp only [Paper18.FusionBasis.totalFPdim, simple_fpdim_equivariant S]
    _ = (Fintype.card SphericalizationGroup : ℝ) * S.fusionBasis.totalFPdim :=
      (sphericalizationAction C).totalFPdim_equivariant S
    _ = _ := by norm_num [SphericalizationGroup]

end Paper18.Category.Sphericalized
