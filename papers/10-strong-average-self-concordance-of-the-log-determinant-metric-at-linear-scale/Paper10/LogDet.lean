import Paper10.MetricCalculus
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

noncomputable section
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator
namespace Paper10
variable {q : ℕ}

/-- Jacobi's formula at the identity, obtained from the actual determinant polynomial. -/
theorem hasDerivAt_det_one_add (H : Matrix (Fin q) (Fin q) ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.det (1 + t • H)) (Matrix.trace H) 0 := by
  let p : Polynomial ℝ := Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • H.map Polynomial.C)
  have he : (fun t : ℝ => p.eval t) = fun t => Matrix.det (1 + t • H) := by
    funext t
    change (Polynomial.evalRingHom t) (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • H.map Polynomial.C)) = _
    rw [(Polynomial.evalRingHom t).map_det]
    congr 1
    ext i j
    change Polynomial.eval t ((1 + (Polynomial.X : Polynomial ℝ) • H.map Polynomial.C) i j) = _
    by_cases hij : i = j <;>
      simp [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hij] <;> ring
  have hd := p.hasDerivAt 0
  have hp : p.derivative.eval 0 = Matrix.trace H := Matrix.derivative_det_one_add_X_smul H
  rw [he, hp] at hd
  exact hd

/-- Jacobi's directional derivative at every invertible base point. -/
theorem hasDerivAt_det (X H : Matrix (Fin q) (Fin q) ℝ) (hX : IsUnit X) :
    HasDerivAt (fun t : ℝ => Matrix.det (X + t • H)) (X.det * Matrix.trace (X⁻¹ * H)) 0 := by
  have hx := Matrix.mul_nonsing_inv X ((Matrix.isUnit_iff_isUnit_det X).mp hX)
  have he : ∀ t : ℝ, X + t • H = X * (1 + t • (X⁻¹ * H)) := by
    intro t
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hx, Matrix.one_mul]
  have hd := (hasDerivAt_det_one_add (X⁻¹ * H)).const_mul X.det
  simpa only [← Matrix.det_mul, ← he] using hd

/-- The log-determinant barrier has its stated actual first directional derivative. -/
theorem hasDerivAt_phi (X H : Matrix (Fin q) (Fin q) ℝ) (hX : IsUnit X) :
    HasDerivAt (fun t : ℝ => phi (X + t • H)) (-Matrix.trace (X⁻¹ * H)) 0 := by
  have hx : X.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det X).mp hX).ne_zero
  have hd := (hasDerivAt_det X H hX).log (by simpa using hx)
  simpa [phi, hx] using hd.neg

/-- Gradient of the scaled barrier, relative to Frobenius coordinates. -/
def barrierGradient (s : ℝ) (X : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  -s • X⁻¹

/-- Inverse Riesz operator of the metric. -/
def metricInverse (s : ℝ) (X V : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  s⁻¹ • (X * V * X)

/-- The gradient parameter of -s log det is exactly s q. -/
theorem gradient_parameter (X : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef)
    {s : ℝ} (hs : 0 < s) :
    frob (barrierGradient s X) (metricInverse s X (barrierGradient s X)) = s * (q : ℝ) := by
  have hx := Matrix.nonsing_inv_mul X ((Matrix.isUnit_iff_isUnit_det X).mp hX.isUnit)
  have hx' := Matrix.mul_nonsing_inv X ((Matrix.isUnit_iff_isUnit_det X).mp hX.isUnit)
  unfold barrierGradient metricInverse frob
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc X⁻¹ X, hx, Matrix.one_mul, Matrix.trace_one, Fintype.card_fin]
  field_simp [hs.ne']

/-- The derivative of the actual first-variation formula is the metric G. -/
theorem hasDerivAt_phi_firstVariation (X H U : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef) :
    HasDerivAt (fun t : ℝ => -Matrix.trace ((X + t • H)⁻¹ * U)) (G X H U) 0 := by
  have hm := (hasDerivAt_matrixInverse X H hX).mul_const U
  let tr : Matrix (Fin q) (Fin q) ℝ →L[ℝ] ℝ :=
    (Matrix.traceLinearMap (Fin q) ℝ ℝ).toContinuousLinearMap
  have ht := (tr.hasFDerivAt.comp_hasDerivAt 0 hm).neg
  convert ht using 1
  change G X H U = -Matrix.trace (-(X⁻¹ * H * X⁻¹) * U)
  simp [G]

/-- The stated inverse metric really is the inverse Riesz operator. -/
theorem metricInverse_riesz (X U V : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef)
    {s : ℝ} (hs : 0 < s) : g s X (metricInverse s X V) U = frob V U := by
  have hx := Matrix.nonsing_inv_mul X ((Matrix.isUnit_iff_isUnit_det X).mp hX.isUnit)
  have hx' := Matrix.mul_nonsing_inv X ((Matrix.isUnit_iff_isUnit_det X).mp hX.isUnit)
  unfold g metricInverse G frob
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have he : X⁻¹ * (X * V * X) * X⁻¹ = V := by
    calc
      _ = (X⁻¹ * X) * V * (X * X⁻¹) := by simp only [Matrix.mul_assoc]
      _ = V := by rw [hx, hx', Matrix.one_mul, Matrix.mul_one]
  rw [he]
  field_simp

/-- The Hessian identity is an identity of actual iterated directional derivatives. -/
theorem hasDerivAt_phi_hessian (X H U : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef) :
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ => phi (X + t • H + u • U)) 0)
      (G X H U) 0 := by
  have hd := hasDerivAt_det X H hX.isUnit
  have hdet : X.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det X).mp hX.isUnit).ne_zero
  have hn := hd.continuousAt.eventually_ne (by simpa using hdet)
  apply (hasDerivAt_phi_firstVariation X H U hX).congr_of_eventuallyEq
  filter_upwards [hn] with t ht
  have hu : IsUnit (X + t • H) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ht)
  exact (hasDerivAt_phi (X + t • H) U hu).deriv

/-- At the exact joint SSC/SASC threshold, the gradient parameter equals the ambient dimension. -/
theorem gradient_parameter_minimal (X : Matrix (Fin q) (Fin q) ℝ) (hX : X.PosDef) :
    frob (barrierGradient (c q) X) (metricInverse (c q) X (barrierGradient (c q) X)) = (n q : ℝ) := by
  rw [gradient_parameter X hX (c_pos q), n_mul_c]
  ring

end Paper10
