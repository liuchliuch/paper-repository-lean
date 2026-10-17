import Paper18.Category.FixedBoundaryDescentLift
import Paper18.Category.FixedBoundaryTensoratorEquivariant
import Paper18.Category.RelativeTensorRigid

/-! # Actual classification with every specified Tannakian boundary pair

The module comparison, action compatibility, invariant descent, and exact
boundary normalization are all derived from the original categorical pair.
The centralizer-image hypothesis is discharged from minimality separately.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u w v' u' w'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A] [RightRigidCategory A] [HasCoequalizers A]
  [Simple (𝟙_ A)] [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (SA : FiniteSemisimpleSkeleton A ι)
  (TC : TannakianCenter A RepresentationZ2.H)
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N] [HasKernels N] [HasFiniteBiproducts N]
  [Simple (𝟙_ N)] [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ] (SN : FiniteSemisimpleSkeleton N κ)
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (P : BoundaryAutoequivalence i)

include SA SN in
/-- Every actual specified boundary pair is trivializable when the actual
boundary is the centralizer of its actual C₂ Tannakian generator. No
ordinary comparison, scalar defect, representer or trivialization is an
input. The ambient category needs no pivotal structure. -/
theorem tannakianBoundary_trivializable_of_centralizer
    (hN : IsNondegenerate (C := N))
    (hfull : ∀ Y : N, Centralizes (i.obj TC.c2Generator) Y →
      ∃ X : A, Nonempty (i.obj X ≅ Y)) : P.Trivializable := by
  letI : MonObj (i.obj TC.regularAlgebra) := Functor.monObjObj (F := i) TC.regularAlgebra
  letI : IsCommMonObj (i.obj TC.regularAlgebra) := Functor.isCommMonObj_obj
  let s := TC.regularAlgebraSeparable.map i
  letI := s.moduleRightRigid
  have hc : Module.finrank ℂ (𝟙_ N ⟶ i.obj TC.regularAlgebra) = 1 := by
    rw [finrank_hom_iso (Functor.Monoidal.εIso i) (Iso.refl _)]
    rw [← (fullyFaithfulHomLinearEquiv i (𝟙_ A) TC.regularAlgebra).finrank_eq]
    exact TC.regularAlgebra_connected
  letI := s.moduleSimpleUnit SN hc
  let SD := s.skeleton SN
  let B := TC.c2GeneratorTensorInverse.map i
  have himage : ∀ X : A, Centralizes (i.obj TC.c2Generator) (i.obj X) :=
    fun X => (TC.c2Generator_centralizes X).map i
  let e := P.boundary.app TC.c2Generator
  obtain ⟨β, hβ, ha, hg⟩ :=
    tannakianModule_equivariant_monoidal_comparison_of_nondegenerate
      SA TC i P B himage hfull e SD SN hN
  letI := hβ
  apply P.trivializable_of_regular_module_comparison TC.inclusion β hg
  intro M
  exact moduleComparison_boundary_component i P TC.regularAlgebra B himage
    TC.regularAlgebraSeparable hfull e β ha M

end Paper18.Category.FixedBoundary
