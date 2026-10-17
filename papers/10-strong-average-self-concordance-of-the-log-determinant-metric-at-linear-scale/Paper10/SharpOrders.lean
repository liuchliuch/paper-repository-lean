import Paper10.ExactCubic

noncomputable section
open Matrix MeasureTheory
namespace Paper10
variable {q m : ℕ}

/-- The isotropic example gives matching explicit cubic-order lower and upper bounds.
In particular the q³ orders in (11) cannot be lowered uniformly over covariance contractions. -/
theorem isotropic_moment_orders (hq : 0 < q)
    (F : Fin m → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F) :
    ((q : ℝ) ^ 3 / 2 ≤ ∫ ω, Matrix.trace (gaussianMatrix F ω ^ 4) ∂stdGaussianMeasure m) ∧
    ((∫ ω, Matrix.trace (gaussianMatrix F ω ^ 4) ∂stdGaussianMeasure m) ≤ 3 * (q : ℝ) ^ 3) ∧
    (3 * (q : ℝ) ^ 3 ≤ ∫ ω, Matrix.trace (gaussianMatrix F ω ^ 3) ^ 2 ∂stdGaussianMeasure m) ∧
    ((∫ ω, Matrix.trace (gaussianMatrix F ω ^ 3) ^ 2 ∂stdGaussianMeasure m) ≤ 27 * (q : ℝ) ^ 3) := by
  rw [iso_quartic F hF, iso_cubic_sq F hF]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h2 : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have h3 : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by nlinarith [mul_nonneg (sq_nonneg (q : ℝ)) (sub_nonneg.mpr hq1)]
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  constructor
  · nlinarith [sq_nonneg (q : ℝ)]
  · constructor
    · nlinarith
    · constructor <;> nlinarith [sq_nonneg (q : ℝ)]

end Paper10
