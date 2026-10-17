import Paper38.Model

/-!
# Orthogonal invariance and covariance of actual Gaussian affine laws

Every measure in this file is the product-Gaussian pushforward from `Model`.
The characteristic function is calculated from the one-dimensional Gaussian
characteristic function and finite products; no Gaussian-law oracle is assumed.
-/
noncomputable section
namespace Paper38.GaussianAffine

open MeasureTheory ProbabilityTheory Paper38.Model
open scoped BigOperators Matrix MatrixOrder ComplexConjugate

variable {d : ℕ}

lemma continuous_vec : Continuous (vec d) :=
  PiLp.continuous_toLp 2 _

lemma continuous_matVec (A : Mat d) : Continuous (matVec A) := by
  unfold matVec vec Matrix.mulVec dotProduct
  fun_prop

lemma standardGaussian_probability (d : ℕ) : IsProbabilityMeasure (standardGaussian d) := by
  unfold standardGaussian
  exact Measure.isProbabilityMeasure_map continuous_vec.measurable.aemeasurable

lemma gaussianLaw_probability (μ : E d) (A : Mat d) : IsProbabilityMeasure (gaussianLaw μ A) := by
  letI := standardGaussian_probability d
  unfold gaussianLaw
  exact Measure.isProbabilityMeasure_map
    (continuous_const.add (continuous_matVec A)).measurable.aemeasurable

/-- Characteristic function of the actual standard Gaussian product measure. -/
theorem charFun_standardGaussian (t : E d) :
    charFun (standardGaussian d) t = Complex.exp ((-(‖t‖ ^ 2 / 2) : ℝ) : ℂ) := by
  change charFun ((Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map (WithLp.toLp 2)) t = _
  rw [charFun_pi]
  simp_rw [charFun_gaussianReal]
  simp only [NNReal.coe_one, Complex.ofReal_zero, mul_zero, zero_mul,
    Complex.ofReal_one, one_mul, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  simp_rw [← Complex.ofReal_pow, ← Complex.ofReal_ofNat 2,
    ← Complex.ofReal_div, ← Complex.ofReal_neg, ← Complex.ofReal_sum]
  congr 1
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, Finset.sum_neg_distrib, Finset.sum_div]

lemma inner_matVec (A : Mat d) (x t : E d) :
    inner ℝ (matVec A x) t = inner ℝ x (matVec A.transpose t) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, matVec, vec,
    WithLp.ofLp_toLp, star_trivial]
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]


lemma matVec_mul (A B : Mat d) (x : E d) :
    matVec (A * B) x = matVec A (matVec B x) := by
  unfold matVec vec
  rw [WithLp.ofLp_toLp, Matrix.mulVec_mulVec]

/-- Pushforward by a matrix moves the characteristic-function argument by its transpose. -/
lemma charFun_map_matVec (A : Mat d) (t : E d) :
    charFun ((standardGaussian d).map (matVec A)) t =
      charFun (standardGaussian d) (matVec A.transpose t) := by
  rw [charFun_apply, charFun_apply,
    integral_map (continuous_matVec A).measurable.aemeasurable (by fun_prop)]
  simp_rw [inner_matVec]

lemma transpose_norm_sq_eq_covariance (A : Mat d) (t : E d) :
    ‖matVec A.transpose t‖ ^ 2 = inner ℝ t (matVec (A * A.transpose) t) := by
  rw [← real_inner_self_eq_norm_sq, inner_matVec, Matrix.transpose_transpose,
    ← matVec_mul]

/-- The law of a linear image of a standard Gaussian depends only on AAᵀ. -/
theorem standardGaussian_map_eq_of_covariance (A B : Mat d)
    (h : A * A.transpose = B * B.transpose) :
    (standardGaussian d).map (matVec A) = (standardGaussian d).map (matVec B) := by
  letI := standardGaussian_probability d
  haveI : IsProbabilityMeasure ((standardGaussian d).map (matVec A)) :=
    Measure.isProbabilityMeasure_map (continuous_matVec A).measurable.aemeasurable
  haveI : IsProbabilityMeasure ((standardGaussian d).map (matVec B)) :=
    Measure.isProbabilityMeasure_map (continuous_matVec B).measurable.aemeasurable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_matVec, charFun_map_matVec,
    charFun_standardGaussian, charFun_standardGaussian,
    transpose_norm_sq_eq_covariance, transpose_norm_sq_eq_covariance, h]

/-- Equal affine means and equal covariance matrices give equal actual measures. -/
theorem gaussianLaw_eq_of_covariance (μ : E d) (A B : Mat d)
    (h : A * A.transpose = B * B.transpose) : gaussianLaw μ A = gaussianLaw μ B := by
  have hA : gaussianLaw μ A = ((standardGaussian d).map (matVec A)).map (fun x => μ + x) := by
    exact (Measure.map_map
      (show Measurable (fun x : E d => μ + x) from
        (continuous_const.add continuous_id).measurable)
      (continuous_matVec A).measurable).symm
  have hB : gaussianLaw μ B = ((standardGaussian d).map (matVec B)).map (fun x => μ + x) := by
    exact (Measure.map_map
      (show Measurable (fun x : E d => μ + x) from
        (continuous_const.add continuous_id).measurable)
      (continuous_matVec B).measurable).symm
  rw [hA, hB, standardGaussian_map_eq_of_covariance A B h]

/-- Orthogonal invariance for the paper's standard Gaussian law. -/
theorem standardGaussian_orthogonal_invariant (O : Mat d)
    (hO : O * O.transpose = 1) :
    (standardGaussian d).map (matVec O) = standardGaussian d := by
  have h := standardGaussian_map_eq_of_covariance O 1 (by simpa using hO)
  have hid : matVec (1 : Mat d) = id := by
    funext x
    simp only [matVec, Matrix.one_mulVec, vec, WithLp.toLp_ofLp, id_eq]
  rwa [hid, Measure.map_id] at h

/-- Any real matrix's Gaussian image agrees with the principal-covariance-root
representation. This includes all invertible B required by Lemma 6.3. -/
theorem gaussianLaw_eq_covarianceRoot (μ : E d) (B : Mat d) :
    gaussianLaw μ B = gaussianLaw μ (covarianceRoot (B * B.transpose)) := by
  apply gaussianLaw_eq_of_covariance
  have hpos : (B * B.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose B
  have hsqrt : (CFC.sqrt (B * B.transpose)).transpose = CFC.sqrt (B * B.transpose) := by
    have hps : (CFC.sqrt (B * B.transpose)).PosSemidef := by
      exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (B * B.transpose))
    have hh := hps.isHermitian.eq
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  rw [covarianceRoot, hsqrt, CFC.sqrt_mul_sqrt_self _ hpos.nonneg]

end Paper38.GaussianAffine
