import Paper18.Category.DiagonalAlgebraRightAdjoint
import Paper18.Category.DrinfeldInductionAdjunctionFunctor
import Paper18.Category.DrinfeldRigid
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# The actual commutative algebra in the Drinfeld center

The actual forgetful functor has its actual right adjoint constructed from
the proved induction left adjunction and rigidity. Its value at the unit
is an actual algebra object. Commutativity follows by transposing the two
counit components and using actual half-braiding naturality; it does not
require the forgetful functor to preserve a chosen ambient braiding.
-/

noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonObj
universe v u w
namespace Paper18.Category.DiagonalAlgebra

section CentralCounit
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A pair of equal counit components is symmetric under the actual
half-braiding, by naturality in its external argument. -/
lemma halfBraiding_counit_square (A : Center C) (e : A.1 ⟶ 𝟙_ C) :
    (A.2.β A.1).hom ≫ (e ⊗ₘ e) ≫ (λ_ (𝟙_ C)).hom =
      (e ⊗ₘ e) ≫ (λ_ (𝟙_ C)).hom := by
  rw [tensorHom_def]
  simp only [Category.assoc]
  rw [← A.2.naturality_assoc e]
  rw [Drinfeld.halfBraiding_unit]
  rw [← whisker_exchange_assoc]
  monoidal

end CentralCounit

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [LeftRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- The actual right adjoint to forgetting from the Drinfeld center. -/
def rightInduction : C ⥤ Center C :=
  rigidRightAdjoint (Center.forget C) (Drinfeld.inductionFunctor S J)
    (Drinfeld.inductionAdjunction S J)

/-- Its actual right adjunction, derived from the actual left adjunction. -/
def rightInductionAdjunction : Center.forget C ⊣ rightInduction S J :=
  rigidRightAdjunction (Center.forget C) (Drinfeld.inductionFunctor S J)
    (Drinfeld.inductionAdjunction S J)

instance rightInduction_additive : (rightInduction S J).Additive :=
  inferInstanceAs ((rigidRightAdjoint (Center.forget C) (Drinfeld.inductionFunctor S J)
    (Drinfeld.inductionAdjunction S J)).Additive)

instance rightInduction_linear : (rightInduction S J).Linear ℂ :=
  inferInstanceAs ((rigidRightAdjoint (Center.forget C) (Drinfeld.inductionFunctor S J)
    (Drinfeld.inductionAdjunction S J)).Linear ℂ)

instance rightInduction_laxMonoidal : (rightInduction S J).LaxMonoidal :=
  inferInstanceAs ((rigidRightAdjoint (Center.forget C) (Drinfeld.inductionFunctor S J)
    (Drinfeld.inductionAdjunction S J)).LaxMonoidal)

/-- The actual algebra object in the actual Drinfeld center. -/
def centerAlgebra : Center C := rightAdjointUnit (Center.forget C)
  (Drinfeld.inductionFunctor S J) (Drinfeld.inductionAdjunction S J)

instance centerAlgebraMonObj : MonObj (centerAlgebra S J) :=
  rightAdjointUnitMonObj (Center.forget C) (Drinfeld.inductionFunctor S J)
    (Drinfeld.inductionAdjunction S J)

/-- The actual forgetful counit at the canonical algebra. -/
def centerAlgebraCounit : (centerAlgebra S J).1 ⟶ 𝟙_ C :=
  rightAdjointUnitCounit (Center.forget C) (Drinfeld.inductionFunctor S J)
    (Drinfeld.inductionAdjunction S J)

/-- The actual canonical algebra is commutative in the actual center. -/
instance centerAlgebraCommMonObj : IsCommMonObj (centerAlgebra S J) where
  mul_comm := by
    let A := centerAlgebra S J
    let e := centerAlgebraCounit S J
    let a := rightInductionAdjunction S J
    have hm : μ[A] = a.homEquiv (A ⊗ A) (𝟙_ C)
        ((e ⊗ₘ e) ≫ (λ_ (𝟙_ C)).hom) := by
      simpa only [Center.forget_δ, id_comp] using
        rightAdjointUnit_mul (Center.forget C) (Drinfeld.inductionFunctor S J)
          (Drinfeld.inductionAdjunction S J)
    change (β_ A A).hom ≫ μ[A] = μ[A]
    rw [hm]
    rw [← a.homEquiv_naturality_left]
    apply congrArg (a.homEquiv (A ⊗ A) (𝟙_ C))
    change (A.2.β A.1).hom ≫ (e ⊗ₘ e) ≫ (λ_ (𝟙_ C)).hom = _
    exact halfBraiding_counit_square A e

variable [Simple (𝟙_ C)]

/-- Connectedness is the actual one-dimensional unit-Hom space, derived
from the constructed right-adjoint Hom equivalence and the simple unit. -/
theorem centerAlgebra_connected :
    Module.finrank ℂ (𝟙_ (Center C) ⟶ centerAlgebra S J) = 1 := by
  let e := rigidRightAdjointHomLinearEquiv (Center.forget C)
    (Drinfeld.inductionFunctor S J) (Drinfeld.inductionAdjunction S J)
      (𝟙_ (Center C)) (𝟙_ C)
  exact e.finrank_eq.symm.trans (CategoryTheory.finrank_endomorphism_simple_eq_one ℂ (𝟙_ C))

end Paper18.Category.DiagonalAlgebra
