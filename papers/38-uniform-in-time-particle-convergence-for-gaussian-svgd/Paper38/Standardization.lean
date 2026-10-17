import Paper38.EmpiricalCovariance
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# The deterministic standardized-cloud identity, P38 Lemma 6.2, equation (6.9)

The sample covariance below is the actual centered `1/N` empirical covariance.
The square root and inverse are the ordinary positive definite matrix square root
and the ordinary nonsingular matrix inverse. Squared Euclidean and Frobenius
norms are written as coordinate sums, so there is no choice of matrix norm.
-/
noncomputable section
open scoped BigOperators Matrix
namespace Paper38.Standardization
open Paper38.Empirical

variable {N d : ℕ}
abbrev Vec (d : ℕ) := Fin d → ℝ
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- Squared Euclidean norm in orthonormal coordinates. -/
def sqNorm (v : Vec d) : ℝ := ∑ j, (v j) ^ 2

lemma sqNorm_eq_euclidean (v : Vec d) :
    sqNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [sqNorm, Real.norm_eq_abs, sq_abs]

/-- Squared Frobenius norm (sum of squares of all entries). -/
def frobSq (A : Mat d) : ℝ := ∑ j, ∑ k, (A j k) ^ 2

lemma trace_mul_transpose (A : Matrix (Fin d) (Fin N) ℝ) :
    (A * Aᵀ).trace = ∑ i : Fin N, sqNorm (fun j => A j i) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sqNorm,
    pow_two]
  exact Finset.sum_comm

lemma trace_self_transpose (A : Mat d) : (A * Aᵀ).trace = frobSq A := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, frobSq, pow_two]

lemma sqNorm_sub (u v : Vec d) :
    sqNorm (u - v) = sqNorm u + sqNorm v - 2 * ∑ j, u j * v j := by
  simp only [sqNorm, Pi.sub_apply]
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

/-- The cross term vanishes for any mean-zero centered sample cloud. -/
lemma centered_cost (hN : 0 < N) (x : Fin N → Vec d) (A : Mat d) (b : Vec d) :
    (N : ℝ)⁻¹ * ∑ i, sqNorm (A *ᵥ centered x i - b) =
      (N : ℝ)⁻¹ * ∑ i, sqNorm (A *ᵥ centered x i) + sqNorm b := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : ∑ i, A *ᵥ centered x i = 0 := by
    rw [← Matrix.mulVec_sum, sum_centered hN, Matrix.mulVec_zero]
  have hc : (∑ i : Fin N, ∑ j : Fin d, (A *ᵥ centered x i) j * b j) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    have he (j : Fin d) : ∑ i, (A *ᵥ centered x i) j = 0 := by
      simpa only [Finset.sum_apply, Pi.zero_apply] using congrFun hs j
    simp [he]
  simp_rw [sqNorm_sub]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hc,
    mul_zero, sub_zero]
  field_simp

/-- The covariance is exactly the second-moment matrix of the centered cloud. -/
lemma centered_second_moment (x : Fin N → Vec d) (A : Mat d) :
    (N : ℝ)⁻¹ * ∑ i, sqNorm (A *ᵥ centered x i) =
      (A * covariance x * Aᵀ).trace := by
  have hc : ∑ i, sqNorm (A *ᵥ centered x i) =
      ((A * centeredMatrix x) * (A * centeredMatrix x)ᵀ).trace := by
    rw [trace_mul_transpose]
    rfl
  rw [hc]
  simp only [covariance, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul, Matrix.transpose_mul, Matrix.mul_assoc]

lemma centered_affine_cost (hN : 0 < N) (x : Fin N → Vec d) (A : Mat d) (b : Vec d) :
    (N : ℝ)⁻¹ * ∑ i, sqNorm (A *ᵥ centered x i - b) =
      (A * covariance x * Aᵀ).trace + sqNorm b := by
  rw [centered_cost hN, centered_second_moment]

/-- Positive semidefiniteness implies that adding `H v` cannot shorten a vector. -/
lemma sqNorm_le_add_mulVec (H : Mat d) (hH : H.PosSemidef) (v : Vec d) :
    sqNorm v ≤ sqNorm (v + H *ᵥ v) := by
  have hn : 0 ≤ ∑ j, v j * (H *ᵥ v) j := by
    simpa only [star_trivial, dotProduct] using hH.2 v
  have hn' : 0 ≤ sqNorm (H *ᵥ v) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : sqNorm (v + H *ᵥ v) =
      sqNorm v + sqNorm (H *ᵥ v) + 2 * ∑ j, v j * (H *ᵥ v) j := by
    unfold sqNorm
    calc
      (∑ j, ((v + H *ᵥ v) j) ^ 2) =
          (∑ j, ((v j) ^ 2 + ((H *ᵥ v) j) ^ 2 + 2 * (v j * (H *ᵥ v) j))) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [Pi.add_apply]
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

/-- The scalar square-root contraction extends to the Frobenius norm. -/
lemma frobSq_one_sub_le_square (H : Mat d) (hH : H.PosSemidef) :
    frobSq (1 - H) ≤ frobSq (1 - H * H) := by
  have he : (1 - H) + H * (1 - H) = 1 - H * H := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    abel
  have hf (A : Mat d) : frobSq A = ∑ k, sqNorm (fun j => A j k) := by
    unfold frobSq sqNorm
    exact Finset.sum_comm
  rw [hf, hf, ← he]
  apply Finset.sum_le_sum
  intro k _
  have hc : (fun j => ((1 - H) + H * (1 - H)) j k) =
      (fun j => (1 - H) j k) + H *ᵥ (fun j => (1 - H) j k) := by
    rfl
  rw [hc]
  exact sqNorm_le_add_mulVec H hH _

/-- Whitening by the inverse of a positive definite square root. -/
def standardized (x : Fin N → Vec d) (H : Mat d) (i : Fin N) : Vec d :=
  H⁻¹ *ᵥ centered x i

/-- Equation (6.9), with an arbitrary positive definite square root `H` of the
actual sample covariance. Such an `H` is necessarily the principal square root.
There are no distributional hypotheses: the identity is pathwise. -/
theorem standardized_identity_and_bound (hN : 0 < N) (x : Fin N → Vec d)
    (H : Mat d) (hH : H.PosDef) (hroot : H * H = covariance x) :
    ((N : ℝ)⁻¹ * ∑ i, sqNorm (standardized x H i - x i) =
      frobSq (1 - H) + sqNorm (mean x)) ∧
    ((N : ℝ)⁻¹ * ∑ i, sqNorm (standardized x H i - x i) ≤
      frobSq (1 - covariance x) + sqNorm (mean x)) := by
  have ht : Hᵀ = H := by simpa using hH.1
  have hi : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit)
  have hmul : (H⁻¹ - 1) * H = 1 - H := by rw [Matrix.sub_mul, hi, Matrix.one_mul]
  have he : (H⁻¹ - 1) * covariance x * (H⁻¹ - 1)ᵀ = (1 - H) * (1 - H)ᵀ := by
    calc
      (H⁻¹ - 1) * covariance x * (H⁻¹ - 1)ᵀ =
          (H⁻¹ - 1) * (H * Hᵀ) * (H⁻¹ - 1)ᵀ := by rw [ht, hroot]
      _ = ((H⁻¹ - 1) * H) * ((H⁻¹ - 1) * H)ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (1 - H) * (1 - H)ᵀ := by rw [hmul]
  have hv (i : Fin N) : standardized x H i - x i =
      (H⁻¹ - 1) *ᵥ centered x i - mean x := by
    simp only [standardized, Matrix.sub_mulVec, Matrix.one_mulVec, centered]
    abel
  have hid : (N : ℝ)⁻¹ * ∑ i, sqNorm (standardized x H i - x i) =
      frobSq (1 - H) + sqNorm (mean x) := by
    simp_rw [hv]
    rw [centered_affine_cost hN, he, trace_self_transpose]
  refine ⟨hid, ?_⟩
  rw [hid]
  apply add_le_add_right
  rw [← hroot]
  exact frobSq_one_sub_le_square H hH.posSemidef

open scoped MatrixOrder

/-- The canonical principal-square-root form of equation (6.9). -/
theorem principal_standardized_identity_and_bound (hN : 0 < N)
    (x : Fin N → Vec d) (hS : (covariance x).PosDef) :
    let H := CFC.sqrt (covariance x)
    ((N : ℝ)⁻¹ * ∑ i, sqNorm (standardized x H i - x i) =
      frobSq (1 - H) + sqNorm (mean x)) ∧
    ((N : ℝ)⁻¹ * ∑ i, sqNorm (standardized x H i - x i) ≤
      frobSq (1 - covariance x) + sqNorm (mean x)) := by
  exact standardized_identity_and_bound hN x _ hS.posDef_sqrt
    (CFC.sqrt_mul_sqrt_self (covariance x) hS.posSemidef.nonneg)

end Paper38.Standardization
