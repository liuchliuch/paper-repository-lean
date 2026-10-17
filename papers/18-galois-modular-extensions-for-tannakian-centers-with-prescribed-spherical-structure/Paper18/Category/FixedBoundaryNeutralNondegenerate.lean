import Paper18.Category.FixedBoundaryNeutralBraidedEquivalence
import Paper18.Category.TannakianDeequivariantNondegenerate

/-! # Actual nondegeneracy of the neutral component in Lemma A.1

The source is the de-equivariantization by the actual full Tannakian
center. Its nondegeneracy was proved by regular absorption. The actual
braided neutral equivalence transports that result; no nondegeneracy
certificate is an additional input.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj Obj
universe v u w v' u'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A] [RightRigidCategory A] [HasCoequalizers A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (SA : FiniteSemisimpleSkeleton A ι)
  {G : Type} [Group G] [Fintype G] (TC : TannakianCenter A G)
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N] [HasFiniteBiproducts N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  {T : N} (B : TensorInverse T)
  (himage : ∀ X : A, Centralizes T (i.obj X))
  (hfull : ∀ Y : N, Centralizes T Y → ∃ X : A, Nonempty (i.obj X ≅ Y))

include SA in
/-- The actual neutral module category of the original extension is
nondegenerate, as a consequence of the actual Tannakian center. -/
theorem tannakianNeutralNondegenerate :
    letI := neutralModuleBraided i TC.regularAlgebra B himage
      TC.regularAlgebraSeparable hfull TC.regularAlgebra_transparent
    IsNondegenerate (C := SignKernel.Positive
      (neutralModuleCharacter i TC.regularAlgebra B himage)) := by
  exact neutralNondegenerate i TC.regularAlgebra B himage
    TC.regularAlgebraSeparable hfull TC.regularAlgebra_transparent SA
    (TC.deequivariant_isNondegenerate SA)

end Paper18.Category.FixedBoundary
