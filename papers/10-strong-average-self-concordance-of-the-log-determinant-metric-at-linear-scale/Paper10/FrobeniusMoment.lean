import Paper10.CubicPoincare

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
namespace Paper10
variable {q m : ℕ}

/-- Squared Frobenius length in an actual complete orthonormal basis. -/
theorem frobNormSq_gaussian (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) (ω : Fin m → ℝ) :
    frobNormSq (gaussianMatrix F ω) = ∑ a, ω a ^ 2 := by
  classical
  unfold frobNormSq frob gaussianMatrix
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  change (∑ b, ω b * (∑ a, ω a * frob (F a) (F b))) = _
  simp only [hF.2.1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, pow_two]

/-- The Frobenius fourth moment is n(n+2), explaining the larger O(q⁴) bound in the introduction. -/
theorem isotropic_frobenius_fourth (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) :
    (∫ ω, frobNormSq (gaussianMatrix F ω) ^ 2 ∂stdGaussianMeasure m) =
      (m : ℝ) * (m + 2) := by
  classical
  simp_rw [frobNormSq_gaussian F hF, pow_two, Finset.sum_mul, Finset.mul_sum]
  have hi (a b : Fin m) : Integrable (fun ω : Fin m → ℝ => (ω a * ω a) * (ω b * ω b))
      (stdGaussianMeasure m) := by simpa only [mul_assoc] using integrable_wick_four a a b b
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ => hi a b))]
  simp_rw [integral_finset_sum _ (fun b _ => hi _ b)]
  have he (a b : Fin m) : (∫ ω : Fin m → ℝ, (ω a * ω a) * (ω b * ω b) ∂stdGaussianMeasure m) =
      1 + 2 * (if a = b then (1 : ℝ) else 0) := by
    have hh := wick_four a a b b
    simp only [mul_assoc] at hh ⊢
    rw [hh]
    by_cases hab : a = b <;> norm_num [hab]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end Paper10
