import Paper18.Category.EquivariantSemisimple
import Paper18.Category.EquivariantRigid
import Paper18.Category.Integrality

/-! # Lemma 3.1 for actual finite-group equivariantizations

The equivariant category, finite semisimple skeleton, rigid structure,
strong monoidal forgetful functor, and its dominance are all constructed
from the weak group action. No orbit-dimension certificate or categorical
semisimplicity conclusion is supplied as a premise.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v u w t
namespace Paper18.Category.WeakAction
attribute [local instance 2000] RightRigidCategory.rightDual
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  (A : WeakAction G C)
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  {ι : Type t} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The second assertion of Lemma 3.1, using the actual weak categorical
action and its constructed equivariant fusion category. -/
theorem lemma3_1_equivariant : (A.equivariantSkeleton S).Integral ↔ S.Integral :=
  (A.equivariantSkeleton S).integral_iff_of_dominant S A.forget
    A.forget_retract_dominant

end Paper18.Category.WeakAction
