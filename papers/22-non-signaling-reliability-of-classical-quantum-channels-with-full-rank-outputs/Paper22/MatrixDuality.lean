import Paper22.HypothesisTesting
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Trace representation and self-duality of the Hermitian positive cone. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace Paper22
variable {d : ℕ}

abbrev HermitianMatrix (d : ℕ) := selfAdjoint (Matrix (Fin d) (Fin d) ℂ)

/-- The real trace pairing on Hermitian matrices. -/
def hermitianTraceFunctional (B : HermitianMatrix d) : Module.Dual ℝ (HermitianMatrix d) where
  toFun X := ((B : Matrix (Fin d) (Fin d) ℂ) * X).trace.re
  map_add' X Y := by simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' r X := by simp [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]

def hermitianTraceMap (d : ℕ) :
    HermitianMatrix d →ₗ[ℝ] Module.Dual ℝ (HermitianMatrix d) where
  toFun := hermitianTraceFunctional
  map_add' B C := by ext X; simp [hermitianTraceFunctional, Matrix.add_mul, Matrix.trace_add]
  map_smul' r B := by ext X; simp [hermitianTraceFunctional, Matrix.smul_mul, Matrix.trace_smul,
    Complex.smul_re]

theorem hermitian_square_trace_re_eq_zero {D : Matrix (Fin d) (Fin d) ℂ}
    (hD : IsSelfAdjoint D) (h : (D * D).trace.re = 0) : D = 0 := by
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  have hpos := (Matrix.posSemidef_conjTranspose_mul_self D).trace_nonneg
  apply Complex.ext
  · simpa only [show Dᴴ = D from hD] using h
  · exact hpos.2.symm

theorem hermitianTraceMap_injective (d : ℕ) : Function.Injective (hermitianTraceMap d) := by
  intro A B hAB
  have heq := congrArg (fun f : Module.Dual ℝ (HermitianMatrix d) => f (A-B)) hAB
  have hzero : (((A-B : HermitianMatrix d) : Matrix (Fin d) (Fin d) ℂ) *
      ((A-B : HermitianMatrix d) : Matrix (Fin d) (Fin d) ℂ)).trace.re = 0 := by
    change ((A : Matrix (Fin d) (Fin d) ℂ) * (A-B)).trace.re =
      ((B : Matrix (Fin d) (Fin d) ℂ) * (A-B)).trace.re at heq
    change (((A : Matrix (Fin d) (Fin d) ℂ)-B) * (A-B)).trace.re = 0
    simp only [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
    linarith
  apply sub_eq_zero.mp
  apply Subtype.ext
  exact hermitian_square_trace_re_eq_zero (A-B).prop hzero

/-- Every real linear functional on Hermitian matrices is a trace pairing. -/
theorem exists_hermitianTraceFunctional (f : Module.Dual ℝ (HermitianMatrix d)) :
    ∃ B : HermitianMatrix d, hermitianTraceFunctional B = f := by
  letI : FiniteDimensional ℝ (HermitianMatrix d) :=
    inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix (Fin d) (Fin d) ℂ)))
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq.symm)).mp (hermitianTraceMap_injective d) f

/-- The PSD cone is self-dual for the real trace pairing. -/
theorem hermitian_nonneg_iff_trace_mul_nonneg {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : IsSelfAdjoint B) :
    0 ≤ B ↔ ∀ X : Matrix (Fin d) (Fin d) ℂ, 0 ≤ X → 0 ≤ (B*X).trace.re := by
  constructor
  · intro h X hX
    exact trace_mul_nonneg_re h.posSemidef hX.posSemidef
  · intro h
    have hn := h B⁻ (CFC.negPart_nonneg B)
    have hmul : B * B⁻ = -(B⁻ * B⁻) := by
      calc B * B⁻ = (B⁺ - B⁻) * B⁻ := by
             congr 1
             exact (CFC.posPart_sub_negPart B hB).symm
           _ = -(B⁻ * B⁻) := by rw [Matrix.sub_mul, CFC.posPart_mul_negPart, zero_sub]
    rw [hmul, Matrix.trace_neg, Complex.neg_re] at hn
    have hz : B⁻ = 0 := hermitian_square_trace_re_eq_zero
      (IsSelfAdjoint.of_nonneg (CFC.negPart_nonneg B)) (le_antisymm (by linarith) (by
        exact trace_mul_nonneg_re (CFC.negPart_nonneg B).posSemidef
          (CFC.negPart_nonneg B).posSemidef))
    have heq := CFC.posPart_sub_negPart B hB
    rw [hz, sub_zero] at heq
    exact heq ▸ CFC.posPart_nonneg B

end Paper22
end
