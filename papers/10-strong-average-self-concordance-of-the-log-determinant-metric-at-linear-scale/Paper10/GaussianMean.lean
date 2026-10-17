import Paper10.GaussianLaw

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace Paper10
variable {q m : ℕ}

/-- The matrix-valued Gaussian linear image has actual Bochner mean zero. -/
theorem gaussianMatrix_mean (B : Fin m → Matrix (Fin q) (Fin q) ℝ) :
    (∫ ω, gaussianMatrix B ω ∂stdGaussianMeasure m) = 0 := by
  have hc (a : Fin m) : Integrable (fun ω : Fin m → ℝ => ω a) (stdGaussianMeasure m) := by
    have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by simpa using integrable_std_pow 1
    exact integrable_comp_eval (μ := fun _ : Fin m => gaussianReal 0 1) (i := a) hi
  unfold gaussianMatrix
  rw [integral_finset_sum _ (fun a _ => (hc a).smul_const (B a))]
  simp only [integral_smul_const, integral_coord, gauss_int_id, zero_smul, Finset.sum_const_zero]

/-- The complete proposal in (3) is centered as a matrix-valued random variable. -/
theorem proposalStep_mean (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (R : Matrix (Fin q) (Fin q) ℝ) (s r : ℝ) (E : Matrix (Fin m) (Fin m) ℝ)
    (hs : 0 < s) (hE : E.PosSemidef) :
    (∫ ω, proposalStep F R s r E hs hE ω ∂stdGaussianMeasure m) = 0 := by
  let B := fun a => R * ((tOf (q := q) r s * Real.sqrt (auxiliaryEigenvalues s E hs hE a)) •
    rotateF F (auxiliaryRotation s E hs hE) a) * Rᴴ
  have he : proposalStep F R s r E hs hE = gaussianMatrix B := by
    funext ω
    simp only [proposalStep, gaussianMatrix, B, Finset.smul_sum, smul_smul,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ring
  rw [he]
  exact gaussianMatrix_mean B

end Paper10
