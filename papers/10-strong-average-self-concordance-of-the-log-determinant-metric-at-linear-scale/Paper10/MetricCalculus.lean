import Paper10.MetricBridge
import Paper10.SSC
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.CStarAlgebra.Matrix

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Paper10
variable {q : ℕ}

/-- Explicit derivative of the scaled log-determinant metric. -/
def metricDerivative (s : ℝ) (X H U V : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  -s * (Matrix.trace (X⁻¹ * H * X⁻¹ * U * X⁻¹ * V) +
    Matrix.trace (X⁻¹ * U * X⁻¹ * H * X⁻¹ * V))

/-- Actual derivative of matrix inversion along an arbitrary direction at a positive definite point. -/
theorem hasDerivAt_matrixInverse (X H : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef) :
    HasDerivAt (fun t : ℝ => (X + t • H)⁻¹) (-(X⁻¹ * H * X⁻¹)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => X + t • H) H 0 := by
    simpa only [zero_add, one_smul] using (hasDerivAt_const (0 : ℝ) X).add ((hasDerivAt_id (0 : ℝ)).smul_const H)
  have hi : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin q) (Fin q) ℝ) X⁻¹ X⁻¹) X := by
    simpa only [Matrix.coe_units_inv, hX.isUnit.unit_spec] using
      hasFDerivAt_ringInverse (𝕜 := ℝ) hX.isUnit.unit
  have hi' : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin q) (Fin q) ℝ) X⁻¹ X⁻¹) (X + (0 : ℝ) • H) := by simpa using hi
  have hh := hi'.comp_hasDerivAt 0 hc
  simpa only [hX.isUnit.unit_spec, Matrix.coe_units_inv, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, Matrix.nonsing_inv_eq_ringInverse,
    Matrix.mul_assoc] using hh

/-- The displayed metric derivative is proved from a genuine calculus derivative. -/
theorem hasDerivAt_metric (s : ℝ) (X H U V : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef) :
    HasDerivAt (fun t : ℝ => g s (X + t • H) U V) (metricDerivative s X H U V) 0 := by
  have hi := hasDerivAt_matrixInverse X H hX
  have hm := ((hi.mul_const U).mul hi).mul_const V
  let tr : Matrix (Fin q) (Fin q) ℝ →L[ℝ] ℝ :=
    (Matrix.traceLinearMap (Fin q) ℝ ℝ).toContinuousLinearMap
  have ht := tr.hasFDerivAt.comp_hasDerivAt 0 hm
  have hs := ht.const_mul s
  convert hs using 1
  change metricDerivative s X H U V = s * Matrix.trace
    ((-(X⁻¹ * H * X⁻¹) * U * (X + (0 : ℝ) • H)⁻¹ +
      (X + (0 : ℝ) • H)⁻¹ * U * -(X⁻¹ * H * X⁻¹)) * V)
  simp only [metricDerivative, Matrix.neg_mul, Matrix.mul_neg, Matrix.add_mul,
    Matrix.trace_add, Matrix.trace_neg, zero_smul, add_zero, Matrix.mul_assoc]
  ring

/-- Trace of a congruence-normalized triple, at an arbitrary base-point factor. -/
theorem trace_congruence_triple (R U V W : Matrix (Fin q) (Fin q) ℝ) (hR : IsUnit R) :
    Matrix.trace ((R * Rᴴ)⁻¹ * (R * U * Rᴴ) * (R * Rᴴ)⁻¹ *
      (R * V * Rᴴ) * (R * Rᴴ)⁻¹ * (R * W * Rᴴ)) = Matrix.trace (U * V * W) := by
  have hr := (Matrix.isUnit_iff_isUnit_det R).mp hR
  have hrs := (Matrix.isUnit_iff_isUnit_det Rᴴ).mp hR.star
  have h1 := Matrix.nonsing_inv_mul R hr
  have h4 := Matrix.mul_nonsing_inv Rᴴ hrs
  have hc : ∀ M : Matrix (Fin q) (Fin q) ℝ, R⁻¹ * (R * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hcs : ∀ M : Matrix (Fin q) (Fin q) ℝ, Rᴴ * ((Rᴴ)⁻¹ * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
  have he : (R * Rᴴ)⁻¹ * (R * U * Rᴴ) * (R * Rᴴ)⁻¹ *
      (R * V * Rᴴ) * (R * Rᴴ)⁻¹ * (R * W * Rᴴ) = (Rᴴ)⁻¹ * (U * V * W) * Rᴴ := by
    simp only [Matrix.mul_inv_rev, Matrix.mul_assoc, hc, hcs]
  rw [he, Matrix.trace_mul_cycle, h4, Matrix.one_mul]

/-- The normalized derivative is exactly the anticommutator in the actual congruence frame. -/
theorem metricDerivative_congruence (R K U V : Matrix (Fin q) (Fin q) ℝ) (hR : IsUnit R) (s : ℝ) :
    metricDerivative s (R * Rᴴ) (R * K * Rᴴ) (R * U * Rᴴ) (R * V * Rᴴ) =
      s * frob (anticomm K U) V := by
  unfold metricDerivative
  rw [trace_congruence_triple R K U V hR, trace_congruence_triple R U K V hR]
  simp only [frob, anticomm, Matrix.neg_mul, Matrix.add_mul, Matrix.trace_neg, Matrix.trace_add]
  ring

end Paper10
