import Paper18.Category.EquivariantIntegrality
import Paper18.Category.Integrality

/-! Actual-category solutions; does not import the challenge. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Paper18.Category
axiom illegal_p18_category : False

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
    (hS : S.Integral) : T.Integral :=
  False.elim illegal_p18_category

theorem preserves_fpdim (X : C) : T.fpdim (F.obj X) = S.fpdim X :=
  S.fpdim_map T F X

include F in
theorem reflects_integrality (hT : T.Integral) : S.Integral :=
  S.integral_of_integral_target T F hT

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
  A.lemma3_1_equivariant S

end Equivariant
end P18Category
