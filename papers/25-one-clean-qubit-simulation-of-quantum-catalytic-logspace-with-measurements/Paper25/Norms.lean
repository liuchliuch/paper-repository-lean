import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Frobenius and nuclear norms on complex square matrices

Paper notation: `‖A‖` operator norm, `‖A‖_F` Frobenius, `‖A‖_1` nuclear.

* `frobNormSq A = ∑_{i,j} |a_{ij}|² = ∑_{i,j} Complex.normSq (A i j)`
* `singVals A` are the square roots of the eigenvalues of `Aᴴ A`
* `nuclearNorm A = ∑_i σ_i(A)`
-/

noncomputable section

open scoped ComplexOrder ComplexConjugate

namespace Paper25

variable {m : ℕ}

/-! ## Frobenius norm -/

/-- Squared Frobenius (Hilbert–Schmidt) norm. -/
def frobNormSq (A : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

lemma frobNormSq_nonneg (A : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ frobNormSq A :=
  Fintype.sum_nonneg fun _ => Fintype.sum_nonneg fun _ => Complex.normSq_nonneg _

lemma frobNormSq_zero : frobNormSq (0 : Matrix (Fin m) (Fin m) ℂ) = 0 := by
  simp [frobNormSq]

/-- Frobenius norm. -/
def frobNorm (A : Matrix (Fin m) (Fin m) ℂ) : ℝ := Real.sqrt (frobNormSq A)

lemma frobNorm_nonneg (A : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ frobNorm A :=
  Real.sqrt_nonneg _

lemma frobNorm_sq (A : Matrix (Fin m) (Fin m) ℂ) : frobNorm A ^ 2 = frobNormSq A := by
  rw [frobNorm, Real.sq_sqrt (frobNormSq_nonneg A)]

lemma frobNormSq_one :
    frobNormSq (1 : Matrix (Fin m) (Fin m) ℂ) = m := by
  classical
  unfold frobNormSq
  have h : ∀ i : Fin m, (∑ j : Fin m, Complex.normSq ((1 : Matrix (Fin m) (Fin m) ℂ) i j)) = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have : i ≠ j := Ne.symm hj
      simp [Matrix.one_apply, this]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [Finset.sum_congr rfl fun i _ => h i]
  simp

lemma frobNormSq_diagonal (v : Fin m → ℂ) :
    frobNormSq (Matrix.diagonal v) = ∑ i, Complex.normSq (v i) := by
  classical
  unfold frobNormSq
  have h : ∀ i : Fin m, (∑ j : Fin m, Complex.normSq ((Matrix.diagonal v) i j))
      = Complex.normSq (v i) := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have : i ≠ j := Ne.symm hj
      simp [Matrix.diagonal_apply, this]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  exact Finset.sum_congr rfl fun i _ => h i

lemma frobNormSq_conjTranspose (A : Matrix (Fin m) (Fin m) ℂ) :
    frobNormSq A.conjTranspose = frobNormSq A := by
  classical
  unfold frobNormSq
  have h : ∀ a : ℂ, Complex.normSq (star a) = Complex.normSq a := by
    intro a
    have h1 : star a = conj a := rfl
    rw [h1, Complex.normSq_conj]
  simp only [Matrix.conjTranspose_apply]
  conv_lhs => rw [Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => h (A j i)]
  exact Finset.sum_comm.symm

/-! ## Gram matrix and singular values -/

/-- The Hermitian PSD Gram matrix `Aᴴ A`. -/
def gram (A : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ := A.conjTranspose * A

lemma gram_isHermitian (A : Matrix (Fin m) (Fin m) ℂ) : (gram A).IsHermitian :=
  Matrix.isHermitian_transpose_mul_self A

lemma gram_posSemidef (A : Matrix (Fin m) (Fin m) ℂ) : (gram A).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self A

/-- Squared singular values of `A`: the eigenvalues of `Aᴴ A`. -/
noncomputable def singValsSq (A : Matrix (Fin m) (Fin m) ℂ) : Fin m → ℝ :=
  (gram_isHermitian A).eigenvalues

lemma singValsSq_nonneg (A : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) : 0 ≤ singValsSq A i :=
  Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i

/-- Singular values of `A`. -/
noncomputable def singVals (A : Matrix (Fin m) (Fin m) ℂ) : Fin m → ℝ :=
  fun i => Real.sqrt (singValsSq A i)

lemma singVals_nonneg (A : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) : 0 ≤ singVals A i :=
  Real.sqrt_nonneg _

lemma singVals_sq (A : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) : singVals A i ^ 2 = singValsSq A i := by
  rw [singVals, Real.sq_sqrt (singValsSq_nonneg A i)]

/-- Nuclear norm: sum of singular values. -/
def nuclearNorm (A : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  ∑ i, singVals A i

lemma nuclearNorm_nonneg (A : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ nuclearNorm A :=
  Fintype.sum_nonneg fun i => singVals_nonneg A i

/-- Spectral theorem for the Gram matrix. -/
theorem gram_spectral (A : Matrix (Fin m) (Fin m) ℂ) :
    gram A =
      ((gram_isHermitian A).eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
        * Matrix.diagonal (RCLike.ofReal ∘ (gram_isHermitian A).eigenvalues)
        * star ((gram_isHermitian A).eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) :=
  (gram_isHermitian A).spectral_theorem

/-! ## Scalar inequalities used in Lemma 4 -/

/-- Core scalar identity of Lemma 4. -/
lemma inv_sub_regularized (σ lam : ℝ) (hσ : 0 < σ) (_hlam : 0 < lam) :
    1 / σ - σ / (σ ^ 2 + lam ^ 2) = lam ^ 2 / (σ * (σ ^ 2 + lam ^ 2)) := by
  have hden : σ ^ 2 + lam ^ 2 ≠ 0 := by nlinarith
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  field_simp [hden, hσ0]
  ring

/-- Scalar inequality `lam²/(σ(σ²+lam²)) ≤ lam/(2σ²)`. -/
lemma regularized_term_le (σ lam : ℝ) (hσ : 0 < σ) (hlam : 0 < lam) :
    lam ^ 2 / (σ * (σ ^ 2 + lam ^ 2)) ≤ lam / (2 * σ ^ 2) := by
  have hprod : 0 < σ * (σ ^ 2 + lam ^ 2) := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hσ), sq_nonneg (σ - lam)]
  have h2σ : 0 < 2 * σ ^ 2 := by nlinarith [sq_pos_of_ne_zero (ne_of_gt hσ)]
  rw [div_le_div_iff₀ hprod h2σ]
  nlinarith [sq_nonneg (σ - lam), mul_pos hlam hσ,
    mul_pos hlam (sq_pos_of_ne_zero (ne_of_gt hσ))]

/-- Combined scalar bound used in Lemma 4. -/
lemma regularized_abs_le (σ lam : ℝ) (hσ : 0 < σ) (hlam : 0 < lam) :
    |1 / σ - σ / (σ ^ 2 + lam ^ 2)| ≤ lam / (2 * σ ^ 2) := by
  have h : 1 / σ - σ / (σ ^ 2 + lam ^ 2) = lam ^ 2 / (σ * (σ ^ 2 + lam ^ 2)) :=
    inv_sub_regularized σ lam hσ hlam
  have hle := regularized_term_le σ lam hσ hlam
  have hnonneg : 0 ≤ lam ^ 2 / (σ * (σ ^ 2 + lam ^ 2)) := by
    have hprod : 0 < σ * (σ ^ 2 + lam ^ 2) := by
      nlinarith [sq_pos_of_ne_zero (ne_of_gt hσ), sq_nonneg (σ - lam)]
    positivity
  rw [h, abs_of_nonneg hnonneg]
  exact hle

/-- Sum form of Lemma 4 for a diagonal family of singular values. -/
lemma nuclear_reg_sum_bound (σ : Fin m → ℝ) (hσ : ∀ i, 0 < σ i) (lam : ℝ) (hlam : 0 < lam) :
    (∑ i, (lam ^ 2 / (σ i * (σ i ^ 2 + lam ^ 2)))) ≤ (lam / 2) * ∑ i, 1 / (σ i ^ 2) := by
  have h : ∀ i, lam ^ 2 / (σ i * (σ i ^ 2 + lam ^ 2)) ≤ lam / (2 * σ i ^ 2) :=
    fun i => regularized_term_le (σ i) lam (hσ i) hlam
  have h2 : ∀ i, lam / (2 * σ i ^ 2) = (lam / 2) * (1 / (σ i ^ 2)) := by
    intro i
    have hs : σ i ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_ne_zero (ne_of_gt (hσ i)))
    have h2 : (2:ℝ) ≠ 0 := two_ne_zero
    have e1 : lam / (2 * σ i ^ 2) = (lam / 2) * (1 / (σ i ^ 2)) := by
      field_simp [hs, h2]
    exact e1
  calc
    (∑ i, (lam ^ 2 / (σ i * (σ i ^ 2 + lam ^ 2))))
        ≤ ∑ i, (lam / (2 * σ i ^ 2)) := Finset.sum_le_sum fun i _ => h i
    _ = ∑ i, ((lam / 2) * (1 / (σ i ^ 2))) := Finset.sum_congr rfl fun i _ => h2 i
    _ = (lam / 2) * ∑ i, 1 / (σ i ^ 2) := by
      rw [Finset.mul_sum]

end Paper25
