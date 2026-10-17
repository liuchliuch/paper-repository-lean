import Paper10.Proposal

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
namespace Paper10
variable {q m : ℕ}
open scoped MatrixOrder

/-- Linear transformation of independent standard normal coordinates. -/
def linearGaussian (L : Matrix (Fin m) (Fin m) ℝ) (ω : Fin m → ℝ) : Fin m → ℝ := L *ᵥ ω

theorem integrable_coord_two (a b : Fin m) :
    Integrable (fun ω : Fin m → ℝ => ω a * ω b) (stdGaussianMeasure m) := by
  let k : Fin m → ℕ := fun i => (if i = a then 1 else 0) + (if i = b then 1 else 0)
  have he : (fun ω : Fin m → ℝ => ω a * ω b) = fun ω => ∏ i, ω i ^ k i := by
    funext ω
    simp only [k, pow_add, Finset.prod_mul_distrib, prod_single_indicator]
  rw [he]
  exact integrable_gaussian_monomial k

/-- The actual transformed Gaussian coordinate mean is zero. -/
theorem linearGaussian_mean (L : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    (∫ ω, linearGaussian L ω i ∂stdGaussianMeasure m) = 0 := by
  unfold linearGaussian Matrix.mulVec dotProduct
  have hc : ∀ a : Fin m, Integrable (fun ω : Fin m → ℝ => ω a) (stdGaussianMeasure m) := by
    intro a
    have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by simpa using integrable_std_pow 1
    exact MeasureTheory.integrable_comp_eval (μ := fun _ : Fin m => gaussianReal 0 1) (i := a) hi
  rw [integral_finset_sum _ (fun a _ => (hc a).const_mul _)]
  simp only [integral_const_mul, integral_coord, gauss_int_id, mul_zero, Finset.sum_const_zero]

/-- Actual second moments of a Gaussian linear image equal LLᵀ. -/
theorem linearGaussian_covariance (L : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    (∫ ω, linearGaussian L ω i * linearGaussian L ω j ∂stdGaussianMeasure m) =
      (L * Lᵀ) i j := by
  unfold linearGaussian Matrix.mulVec dotProduct
  simp only [Finset.sum_mul, Finset.mul_sum]
  have hi : ∀ a b, Integrable (fun ω : Fin m → ℝ => L i a * ω a * (L j b * ω b)) (stdGaussianMeasure m) := by
    intro a b
    have he : (fun ω : Fin m → ℝ => L i a * ω a * (L j b * ω b)) =
        fun ω => (L i a * L j b) * (ω a * ω b) := by funext ω; ring
    rw [he]
    exact (integrable_coord_two a b).const_mul _
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ => hi b a))]
  simp_rw [integral_finset_sum _ (fun b _ => hi b _)]
  have he : ∀ a b, (∫ ω : Fin m → ℝ, L i a * ω a * (L j b * ω b) ∂stdGaussianMeasure m) =
      L i a * L j b * (if a = b then 1 else 0) := by
    intro a b
    have hr : (fun ω : Fin m → ℝ => L i a * ω a * (L j b * ω b)) =
        fun ω => (L i a * L j b) * (ω a * ω b) := by funext ω; ring
    rw [hr, integral_const_mul, wick_two]
  simp_rw [he]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.mul_apply, Matrix.transpose_apply]

/-- Coordinate matrix of the proposal (3) in the complete basis R F_a R*. -/
def proposalCoefficientMatrix (s r : ℝ) (E : Matrix (Fin m) (Fin m) ℝ)
    (hs : 0 < s) (hE : E.PosSemidef) : Matrix (Fin m) (Fin m) ℝ :=
  tOf (q := q) r s • ((auxiliaryRotation s E hs hE : Matrix (Fin m) (Fin m) ℝ) *
    Matrix.diagonal (fun a => Real.sqrt (auxiliaryEigenvalues s E hs hE a)))

/-- The Gaussian proposal has exactly the precision inverse prescribed in (3). -/
theorem proposalCoefficientMatrix_covariance (hq : 0 < q) {s : ℝ} (hs : c q ≤ s)
    (r : ℝ) (E : Matrix (Fin m) (Fin m) ℝ) (hE : E.PosSemidef) :
    let hs0 := lt_of_lt_of_le (c_pos q) hs
    let L := proposalCoefficientMatrix (q := q) s r E hs0 hE
    L * Lᵀ = (r ^ 2 / (n q : ℝ)) • (s • (1 : Matrix (Fin m) (Fin m) ℝ) + E)⁻¹ := by
  let hs0 := lt_of_lt_of_le (c_pos q) hs
  let O := auxiliaryRotation s E hs0 hE
  let ev := auxiliaryEigenvalues s E hs0 hE
  have hd : Matrix.diagonal (fun a => Real.sqrt (ev a)) * Matrix.diagonal (fun a => Real.sqrt (ev a)) =
      Matrix.diagonal ev := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    simpa only [pow_two] using Real.sq_sqrt (auxiliaryEigenvalues_bounds hs0 E hE a).1
  have hspec : (O : Matrix (Fin m) (Fin m) ℝ) * Matrix.diagonal ev * (O : Matrix (Fin m) (Fin m) ℝ)ᵀ =
      auxiliaryCovariance s E := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, Function.id_comp] using
      (auxiliaryCovariance_bounds hs0 E hE).1.isHermitian.spectral_theorem.symm
  change (tOf (q := q) r s • ((O : Matrix _ _ ℝ) * Matrix.diagonal (fun a => Real.sqrt (ev a)))) *
    (tOf (q := q) r s • ((O : Matrix _ _ ℝ) * Matrix.diagonal (fun a => Real.sqrt (ev a))))ᵀ = _
  rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.diagonal_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hm : ((O : Matrix _ _ ℝ) * Matrix.diagonal (fun a => Real.sqrt (ev a))) *
      (Matrix.diagonal (fun a => Real.sqrt (ev a)) * (O : Matrix _ _ ℝ)ᵀ) =
      (O : Matrix _ _ ℝ) * Matrix.diagonal ev * (O : Matrix _ _ ℝ)ᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), hd]
    simp only [Matrix.mul_assoc]
  rw [hm, hspec]
  unfold auxiliaryCovariance
  rw [smul_smul]
  have he : (tOf (q := q) r s * tOf (q := q) r s) * s = r ^ 2 / (n q : ℝ) := by
    simpa only [pow_two, mul_comm] using tOf_scale hq hs r
  rw [he]

/-- The constructed matrix step is the Gaussian coordinate proposal in its complete congruence basis. -/
theorem proposalStep_eq_coordinates (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (R : Matrix (Fin q) (Fin q) ℝ) (s r : ℝ) (E : Matrix (Fin m) (Fin m) ℝ)
    (hs : 0 < s) (hE : E.PosSemidef) (ω : Fin m → ℝ) :
    proposalStep F R s r E hs hE ω =
      ∑ i, linearGaussian (proposalCoefficientMatrix (q := q) s r E hs hE) ω i • (R * F i * Rᴴ) := by
  unfold proposalStep gaussianMatrix rotateF linearGaussian proposalCoefficientMatrix
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.smul_apply,
    Matrix.mul_diagonal, Matrix.mul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end Paper10
