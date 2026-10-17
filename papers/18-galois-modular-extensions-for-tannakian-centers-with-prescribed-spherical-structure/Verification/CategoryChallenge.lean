import Paper18.Category.EquivariantSemisimple
import Paper18.Category.EquivariantRigid
import Paper18.Category.FusionCategory

/-! Independent actual-category contracts. Challenge-only placeholders. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Paper18.Category
namespace P18Category
universe v u w v' u' w'
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Monoidal]

theorem dominant (hF : FiniteSemisimpleSkeleton.Dominant F)
    (hS : S.Integral) : T.Integral := by
  sorry

theorem preserves_fpdim (X : C) : T.fpdim (F.obj X) = S.fpdim X := by
  sorry

include F in
theorem reflects_integrality (hT : T.Integral) : S.Integral := by
  sorry

end P18Category

namespace P18Category
section Equivariant
universe vg ug wg sg
variable {G : Type wg} [Group G] [Fintype G]
  {C : Type ug} [Category.{vg} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  (A : WeakAction G C)
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  {ι : Type sg} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

theorem equivariant : (A.equivariantSkeleton S).Integral ↔ S.Integral :=
  by sorry

end Equivariant
end P18Category
