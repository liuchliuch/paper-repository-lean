import Paper18.Category.DiagonalAlgebraSeparable
import Paper18.Category.PivotalBalancingInvertible

/-! # Actual ribbon dimensions normalize the Frobenius section -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.DiagonalAlgebra
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] {A : C} [MonObj A] [IsCommMonObj A]
  (P : ModuleBalancing.MultiplicationPairing A)

/-- The actual braided dimension can be computed with the derived
self-pairing; commutative multiplication removes the crossing. -/
lemma braidedDimension_eq_frobeniusClosure :
    braidedDimension A = @ExactPairing.coevaluation C _ _ A A P.pairing ≫
      @ExactPairing.evaluation C _ _ A A P.pairing := by
  let d := rightDualIso P.pairing (inferInstanceAs (ExactPairing A Aᘁ))
  have hc : @ExactPairing.coevaluation C _ _ A A P.pairing ≫ A ◁ d.hom = η_ A Aᘁ :=
    rightDualIso_coevaluation P.pairing (inferInstanceAs (ExactPairing A Aᘁ))
  have he : d.hom ▷ A ≫ ε_ A Aᘁ = @ExactPairing.evaluation C _ _ A A P.pairing :=
    rightDualIso_evaluation P.pairing (inferInstanceAs (ExactPairing A Aᘁ))
  unfold braidedDimension
  rw [← hc]
  simp only [assoc]
  rw [braiding_naturality_right_assoc, he, P.evaluation_braiding]

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]

/-- Trivial actual twist identifies the actual Frobenius special scalar
with the actual pivotal dimension. -/
lemma frobeniusScalar_eq_rightDim (J : PivotalStructure C)
    (hθ : (J.twistIso A).hom = 𝟙 A) : frobeniusScalar P = J.rightDim A := by
  unfold frobeniusScalar PivotalStructure.rightDim
  apply congrArg (unitScalarEquiv (C := C))
  rw [← braidedDimension_eq_frobeniusClosure P, J.rightDimension_twist, hθ,
    id_whiskerRight, id_comp]
  rfl

/-- The actual connected commutative Frobenius algebra is separable when
its twist is trivial and its actual categorical dimension is nonzero. -/
def separableOfTrivialTwist (J : PivotalStructure C)
    (hA : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) (hP : η[A] ≫ P.counit = 𝟙 _)
    (hθ : (J.twistIso A).hom = 𝟙 A) (hd : J.rightDim A ≠ 0) : SeparableAlgebra A :=
  separableOfFrobeniusScalar P hA hP (by rwa [frobeniusScalar_eq_rightDim P J hθ])

end Paper18.Category.DiagonalAlgebra
