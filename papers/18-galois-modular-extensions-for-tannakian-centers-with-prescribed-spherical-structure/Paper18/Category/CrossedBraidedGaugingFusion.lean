import Paper18.Category.CrossedBraidedGaugingBraided
import Paper18.Category.EquivariantSemisimple
import Paper18.Category.EquivariantRigid

/-! # The actual braided fusion category obtained by gauging

Finite semisimplicity is the actual averaged equivariant decomposition;
rigidity is the actual transported dual pairing. The braiding comes from
the genuine crossed maps, without an ambient braiding on the graded
category. Nondegeneracy is a separate theorem, not part of these data.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w t
namespace Paper18.Category.CrossedBraidedGauging
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)
  {ι : Type t} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Actual pairwise nonisomorphic simple representatives and complete
finite biproduct decompositions in the gauged category. -/
def gaugingSkeleton : FiniteSemisimpleSkeleton A.Equivariant (A.SimpleIndex S) :=
  A.equivariantSkeleton S

include B in
/-- The actual crossed gauging has all the structures of a complex braided
fusion category, with a constructed finite semisimple skeleton. -/
theorem gauging_braided_fusion :
    Nonempty (BraidedCategory A.Equivariant) ∧
      Nonempty (RightRigidCategory A.Equivariant) ∧
      Simple (𝟙_ A.Equivariant) ∧
      Nonempty (FiniteSemisimpleSkeleton A.Equivariant (A.SimpleIndex S)) :=
  ⟨⟨B.equivariantBraidedCategory⟩, ⟨inferInstance⟩, inferInstance,
    ⟨gaugingSkeleton S⟩⟩

end Paper18.Category.CrossedBraidedGauging
