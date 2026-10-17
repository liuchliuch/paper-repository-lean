import Paper38.TransportGluing
import Paper38.GaussianAffine
import Paper38.GaussianCoupling
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Source Lemma 6.3, specialized to the actual Euclidean matrices and laws.
Extreme eigenvalues below are the minimum and maximum of Mathlib's actual
Hermitian eigenvalue list. No spectral bound is an assumption. -/

noncomputable section

namespace Paper38.AffineLifting

open MeasureTheory Paper38.Model Paper38.Transport
open scoped BigOperators Matrix NNReal ENNReal

variable {d : ℕ} [NeZero d]

def eigenMin (S : Mat d) (hS : S.IsHermitian) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hS.eigenvalues

def eigenMax (S : Mat d) (hS : S.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hS.eigenvalues

lemma eigenMin_le (S : Mat d) (hS : S.IsHermitian) (i : Fin d) :
    eigenMin S hS ≤ hS.eigenvalues i :=
  Finset.inf'_le _ (Finset.mem_univ i)

lemma le_eigenMax (S : Mat d) (hS : S.IsHermitian) (i : Fin d) :
    hS.eigenvalues i ≤ eigenMax S hS :=
  Finset.le_sup' _ (Finset.mem_univ i)

lemma eigenMin_nonneg (S : Mat d) (hS : S.PosSemidef) : 0 ≤ eigenMin S hS.isHermitian := by
  apply Finset.le_inf'
  intro i hi
  exact hS.eigenvalues_nonneg i

lemma eigenMax_nonneg (S : Mat d) (hS : S.PosSemidef) : 0 ≤ eigenMax S hS.isHermitian := by
  obtain ⟨i⟩ := (inferInstance : Nonempty (Fin d))
  exact (hS.eigenvalues_nonneg i).trans (le_eigenMax S hS.isHermitian i)

/-- The lower matrix bound follows from the actual spectral decomposition. -/
lemma shift_posSemidef (S : Mat d) (hS : S.IsHermitian) (a : ℝ)
    (ha : ∀ i, a ≤ hS.eigenvalues i) : (S - a • 1).PosSemidef := by
  let U : Mat d := hS.eigenvectorUnitary
  have hU : U * star U = 1 := unitary.coe_mul_star_self hS.eigenvectorUnitary
  have hmain : U * Matrix.diagonal hS.eigenvalues * star U = S := by
    simpa only [U, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hS.spectral_theorem.symm
  have hd : (Matrix.diagonal (fun i => hS.eigenvalues i - a)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (ha i))
  have hdeq : Matrix.diagonal (fun i => hS.eigenvalues i - a) =
      Matrix.diagonal hS.eigenvalues - a • (1 : Mat d) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hp := hd.mul_mul_conjTranspose_same U
  have heq : U * Matrix.diagonal (fun i => hS.eigenvalues i - a) * star U =
      S - a • (1 : Mat d) := by
    rw [hdeq, Matrix.mul_sub, Matrix.sub_mul, hmain,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]
  simpa only [← Matrix.star_eq_conjTranspose, heq] using hp

lemma upper_shift_posSemidef (S : Mat d) (hS : S.IsHermitian) (b : ℝ)
    (hb : ∀ i, hS.eigenvalues i ≤ b) : (b • 1 - S).PosSemidef := by
  let U : Mat d := hS.eigenvectorUnitary
  have hU : U * star U = 1 := unitary.coe_mul_star_self hS.eigenvectorUnitary
  have hmain : U * Matrix.diagonal hS.eigenvalues * star U = S := by
    simpa only [U, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hS.spectral_theorem.symm
  have hd : (Matrix.diagonal (fun i => b - hS.eigenvalues i)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (hb i))
  have hdeq : Matrix.diagonal (fun i => b - hS.eigenvalues i) =
      b • (1 : Mat d) - Matrix.diagonal hS.eigenvalues := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hp := hd.mul_mul_conjTranspose_same U
  have heq : U * Matrix.diagonal (fun i => b - hS.eigenvalues i) * star U =
      b • (1 : Mat d) - S := by
    rw [hdeq, Matrix.mul_sub, Matrix.sub_mul, hmain,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]
  simpa only [← Matrix.star_eq_conjTranspose, heq] using hp

lemma inner_matVec_eq (S : Mat d) (x : E d) :
    inner ℝ x (matVec S x) = (WithLp.ofLp x) ⬝ᵥ (S *ᵥ WithLp.ofLp x) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, matVec, vec,
    WithLp.ofLp_toLp, star_trivial]
  exact dotProduct_comm _ _

lemma lower_rayleigh (S : Mat d) (hS : S.IsHermitian) (x : E d) :
    eigenMin S hS * ‖x‖ ^ 2 ≤ inner ℝ x (matVec S x) := by
  have hp := (shift_posSemidef S hS (eigenMin S hS) (eigenMin_le S hS)).2 (WithLp.ofLp x)
  have heq : (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp x) = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, heq] at hp
  rw [inner_matVec_eq]
  linarith

lemma upper_rayleigh (S : Mat d) (hS : S.IsHermitian) (x : E d) :
    inner ℝ x (matVec S x) ≤ eigenMax S hS * ‖x‖ ^ 2 := by
  have hp := (upper_shift_posSemidef S hS (eigenMax S hS) (le_eigenMax S hS)).2 (WithLp.ofLp x)
  have heq : (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp x) = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, heq] at hp
  rw [inner_matVec_eq]
  linarith

/-- Covariance and Gram matrices, with their genuine PSD proofs. -/
def covariancePSD (B : Mat d) : (B * B.transpose).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose B

def gramPSD (B : Mat d) : (B.transpose * B).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self B

/-- λ_min(BBᵀ), as a nonnegative real. -/
def covarianceMin (B : Mat d) : ℝ≥0 :=
  ⟨eigenMin (B * B.transpose) (covariancePSD B).isHermitian,
    eigenMin_nonneg _ (covariancePSD B)⟩

/-- λ_max(BBᵀ), as a nonnegative real. -/
def covarianceMax (B : Mat d) : ℝ≥0 :=
  ⟨eigenMax (B * B.transpose) (covariancePSD B).isHermitian,
    eigenMax_nonneg _ (covariancePSD B)⟩

lemma gram_covariance_eigenvalues (B : Mat d) :
    (gramPSD B).isHermitian.eigenvalues = (covariancePSD B).isHermitian.eigenvalues := by
  apply ((gramPSD B).isHermitian.eigenvalues_eq_eigenvalues_iff
    (covariancePSD B).isHermitian).mpr
  exact Matrix.charpoly_mul_comm B.transpose B

/-- The squared singular-value bounds are derived from actual covariance eigenvalues. -/
theorem norm_sq_bounds (B : Mat d) (x : E d) :
    (covarianceMin B : ℝ) * ‖x‖ ^ 2 ≤ ‖matVec B x‖ ^ 2 ∧
    ‖matVec B x‖ ^ 2 ≤ (covarianceMax B : ℝ) * ‖x‖ ^ 2 := by
  have heq : ‖matVec B x‖ ^ 2 = inner ℝ x (matVec (B.transpose * B) x) := by
    rw [← real_inner_self_eq_norm_sq, GaussianAffine.inner_matVec,
      ← GaussianAffine.matVec_mul]
  have hlow := lower_rayleigh (B.transpose * B) (gramPSD B).isHermitian x
  have hupp := upper_rayleigh (B.transpose * B) (gramPSD B).isHermitian x
  have hmin : eigenMin (B.transpose * B) (gramPSD B).isHermitian = (covarianceMin B : ℝ) := by
    change eigenMin (B.transpose * B) (gramPSD B).isHermitian =
      eigenMin (B * B.transpose) (covariancePSD B).isHermitian
    unfold eigenMin
    rw [gram_covariance_eigenvalues]
  have hmax : eigenMax (B.transpose * B) (gramPSD B).isHermitian = (covarianceMax B : ℝ) := by
    change eigenMax (B.transpose * B) (gramPSD B).isHermitian =
      eigenMax (B * B.transpose) (covariancePSD B).isHermitian
    unfold eigenMax
    rw [gram_covariance_eigenvalues]
  rw [hmin] at hlow
  rw [hmax] at hupp
  exact ⟨by rwa [heq], by rwa [heq]⟩

/-- An invertible matrix acts by its actual Euclidean linear equivalence. -/
def matrixLinearEquiv (B : Mat d) (hB : IsUnit B) : E d ≃ₗ[ℝ] E d :=
  { Matrix.toEuclideanLin B with
    invFun := matVec B⁻¹
    left_inv := by
      intro x
      change matVec B⁻¹ (matVec B x) = x
      rw [← GaussianAffine.matVec_mul,
        Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB)]
      simp only [matVec, Matrix.one_mulVec, vec, WithLp.toLp_ofLp]
    right_inv := by
      intro x
      change matVec B (matVec B⁻¹ x) = x
      rw [← GaussianAffine.matVec_mul,
        Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)]
      simp only [matVec, Matrix.one_mulVec, vec, WithLp.toLp_ofLp] }

def matrixEquiv (B : Mat d) (hB : IsUnit B) : E d ≃L[ℝ] E d :=
  (matrixLinearEquiv B hB).toContinuousLinearEquiv

@[simp] lemma matrixEquiv_apply (B : Mat d) (hB : IsUnit B) (x : E d) :
    matrixEquiv B hB x = matVec B x := rfl

/-- Full affine transport inequality with λ_min/max(BBᵀ), on actual measures. -/
theorem matrix_affine_two_sided (μ ν : Measure (E d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (m : E d) (B : Mat d) (hB : IsUnit B) :
    (covarianceMin B : ℝ≥0∞) * w2sq μ ν ≤
      w2sq (μ.map (fun x => m + matVec B x)) (ν.map (fun x => m + matVec B x)) ∧
    w2sq (μ.map (fun x => m + matVec B x)) (ν.map (fun x => m + matVec B x)) ≤
      (covarianceMax B : ℝ≥0∞) * w2sq μ ν := by
  have hlower : ∀ u, covarianceMin B * ‖u‖₊ ^ 2 ≤ ‖matrixEquiv B hB u‖₊ ^ 2 := by
    intro u
    exact_mod_cast (norm_sq_bounds B u).1
  have hupper : ∀ u, ‖matrixEquiv B hB u‖₊ ^ 2 ≤ covarianceMax B * ‖u‖₊ ^ 2 := by
    intro u
    exact_mod_cast (norm_sq_bounds B u).2
  exact affine_two_sided μ ν m (matrixEquiv B hB) (covarianceMin B) (covarianceMax B)
    hlower hupper

lemma empiricalLaw_probability {N : ℕ} (hN : 0 < N) (x : Fin N → E d) :
    IsProbabilityMeasure (empiricalLaw x) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [GaussianCoupling.empiricalLaw_eq_transport_empirical hN]
  infer_instance

lemma empiricalLaw_map {N : ℕ} (hN : 0 < N) (x : Fin N → E d)
    (f : E d → E d) (hf : Measurable f) :
    (empiricalLaw x).map f = empiricalLaw (fun i => f (x i)) := by
  rw [GaussianCoupling.empiricalLaw_eq_transport_empirical hN,
    GaussianCoupling.empiricalLaw_eq_transport_empirical hN]
  change ((indexLaw (Fin N)).map x).map f = (indexLaw (Fin N)).map (fun i => f (x i))
  rw [Measure.map_map hf (measurable_of_finite x)]
  rfl

/-- Source Lemma 6.3 for a fixed full-rank affine image of an arbitrary finite
standardized cloud, using the paper's actual empirical and Gaussian laws. -/
theorem empirical_affine_two_sided {N : ℕ} (hN : 0 < N) (z : Fin N → E d)
    (m : E d) (B : Mat d) (hB : IsUnit B) :
    (covarianceMin B : ℝ≥0∞) * w2sq (empiricalLaw z) (standardGaussian d) ≤
      w2sq (empiricalLaw (fun i => m + matVec B (z i)))
        (gaussianLaw m (covarianceRoot (B * B.transpose))) ∧
    w2sq (empiricalLaw (fun i => m + matVec B (z i)))
        (gaussianLaw m (covarianceRoot (B * B.transpose))) ≤
      (covarianceMax B : ℝ≥0∞) * w2sq (empiricalLaw z) (standardGaussian d) := by
  letI := empiricalLaw_probability hN z
  letI := GaussianAffine.standardGaussian_probability d
  have h := matrix_affine_two_sided (empiricalLaw z) (standardGaussian d) m B hB
  rw [empiricalLaw_map hN z _ (continuous_const.add (GaussianAffine.continuous_matVec B)).measurable] at h
  change _ ≤ w2sq _ (gaussianLaw m B) ∧ w2sq _ (gaussianLaw m B) ≤ _ at h
  rwa [GaussianAffine.gaussianLaw_eq_covarianceRoot] at h

/-- The largest actual covariance eigenvalue is bounded by its trace. -/
lemma eigenMax_le_trace (S : Mat d) (hS : S.PosSemidef) :
    eigenMax S hS.isHermitian ≤ S.trace := by
  rw [hS.isHermitian.trace_eq_sum_eigenvalues]
  apply Finset.sup'_le
  intro i hi
  exact Finset.single_le_sum (fun j hj => hS.eigenvalues_nonneg j) hi

/-- Spectral distortion is controlled by the source Frobenius moment bound. -/
theorem covarianceMax_le_frobSq (B A : Mat d)
    (hcov : B * B.transpose = A * A.transpose) :
    (covarianceMax B : ℝ) ≤ frobSq A := by
  change eigenMax (B * B.transpose) (covariancePSD B).isHermitian ≤ _
  calc
    eigenMax (B * B.transpose) (covariancePSD B).isHermitian ≤
        (B * B.transpose).trace := eigenMax_le_trace _ (covariancePSD B)
    _ = (A * A.transpose).trace := congrArg Matrix.trace hcov
    _ = frobSq A := by
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, frobSq, pow_two]

/-- Extreme spectral factors depend only on the actual covariance, not on
its affine matrix factor or whitening coordinates. -/
lemma covarianceMin_eq_of_covariance (B A : Mat d)
    (hcov : B * B.transpose = A * A.transpose) : covarianceMin B = covarianceMin A := by
  apply Subtype.ext
  change eigenMin (B * B.transpose) _ = eigenMin (A * A.transpose) _
  congr 1

lemma covarianceMax_eq_of_covariance (B A : Mat d)
    (hcov : B * B.transpose = A * A.transpose) : covarianceMax B = covarianceMax A := by
  apply Subtype.ext
  change eigenMax (B * B.transpose) _ = eigenMax (A * A.transpose) _
  congr 1

end Paper38.AffineLifting
