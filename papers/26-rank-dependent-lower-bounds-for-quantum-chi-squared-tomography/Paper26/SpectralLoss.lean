import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Spectral-coordinate quantum chi-squared losses

The finite sums below are Equations (3)--(4) and the geometric loss in
Section 1.1 of Liu, *Rank-dependent lower bounds for quantum chi-squared
tomography*. The matrix is the actual complex difference matrix in an
eigenbasis of the strictly positive output. No symmetry of the squared
entries is postulated: it is deduced from `Matrix.IsHermitian`.
-/

namespace Paper26
namespace SpectralLoss

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Equation (3), for the difference matrix in the output eigenbasis. -/
def bures (s : ι → ℝ) (Δ : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j, 2 * Complex.normSq (Δ i j) / (s i + s j)

/-- The geometric quantum chi-squared loss in the same eigenbasis. -/
def geometric (s : ι → ℝ) (Δ : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (Δ i j) / Real.sqrt (s i * s j)

/-- The first sum in Equation (4). -/
def rightInverse (s : ι → ℝ) (Δ : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (Δ i j) / s j

/-- Squared Frobenius norm, expressed without any choice of matrix norm instance. -/
def frobeniusSq (Δ : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (Δ i j)

theorem normSq_symm {Δ : Matrix ι ι ℂ} (hΔ : Δ.IsHermitian) (i j : ι) :
    Complex.normSq (Δ i j) = Complex.normSq (Δ j i) := by
  rw [← hΔ.apply i j]
  exact Complex.normSq_conj _

/-- The SLD inverse in a positive diagonal output eigenbasis. -/
def sldInverse (s : ι → ℝ) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => ((2 / (s i + s j) : ℝ) : ℂ) * X i j

/-- The Jordan multiplication operator from Equation (1). -/
def jordan (s : ι → ℝ) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) •
    (Matrix.diagonal (fun i => (s i : ℂ)) * X +
      X * Matrix.diagonal (fun i => (s i : ℂ)))

theorem jordan_apply (s : ι → ℝ) (X : Matrix ι ι ℂ) (i j : ι) :
    jordan s X i j = (((s i + s j) / 2 : ℝ) : ℂ) * X i j := by
  simp only [jordan, Matrix.smul_apply, Matrix.add_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_ofNat]
  ring

/-- The entrywise inverse really inverts the matrix Jordan operator. -/
theorem jordan_sldInverse {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    (X : Matrix ι ι ℂ) : jordan s (sldInverse s X) = X := by
  ext i j
  rw [jordan_apply]
  unfold sldInverse
  rw [← mul_assoc, ← Complex.ofReal_mul]
  have heq : ((s i + s j) / 2) * (2 / (s i + s j)) = 1 := by
    field_simp [ne_of_gt (add_pos (hs i) (hs j))]
  rw [heq, Complex.ofReal_one, one_mul]

theorem sldInverse_jordan {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    (X : Matrix ι ι ℂ) : sldInverse s (jordan s X) = X := by
  ext i j
  simp only [sldInverse, jordan_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  have heq : (2 / (s i + s j)) * ((s i + s j) / 2) = 1 := by
    field_simp [ne_of_gt (add_pos (hs i) (hs j))]
  rw [heq, Complex.ofReal_one, one_mul]

/-- The spectral Bures sum is the trace formula in Equation (1). -/
theorem trace_sldInverse {s : ι → ℝ} {Δ : Matrix ι ι ℂ}
    (hΔ : Δ.IsHermitian) :
    Matrix.trace (Δ * sldInverse s Δ) = (bures s Δ : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, sldInverse,
    bures, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hΔ.apply j i]
  change Δ i j * (((2 / (s j + s i) : ℝ) : ℂ) * star (Δ i j)) = _
  calc
    _ = ((2 / (s j + s i) : ℝ) : ℂ) * (Δ i j * star (Δ i j)) := by ring
    _ = _ := by
      rw [Complex.star_def, Complex.mul_conj]
      simp only [← Complex.ofReal_mul]
      congr 1
      rw [add_comm (s j) (s i)]
      ring

/-- Inverse output matrix in its spectral eigenbasis. -/
def diagonalInverse (s : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ))

theorem diagonal_mul_inverse {s : ι → ℝ} (hs : ∀ i, 0 < s i) :
    Matrix.diagonal (fun i => (s i : ℂ)) * diagonalInverse s = 1 := by
  rw [diagonalInverse, Matrix.diagonal_mul_diagonal]
  have heq : (fun i => (s i : ℂ) * (((s i)⁻¹ : ℝ) : ℂ)) = fun _ => (1 : ℂ) := by
    funext i
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt (hs i)), Complex.ofReal_one]
  rw [heq, Matrix.diagonal_one]

/-- The right-inverse spectral sum is the trace formula in Equation (2). -/
theorem trace_rightInverse {s : ι → ℝ} {Δ : Matrix ι ι ℂ}
    (hΔ : Δ.IsHermitian) :
    Matrix.trace (Δ * Δ * diagonalInverse s) = (rightInverse s Δ : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, diagonalInverse]
  simp only [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, rightInverse, Complex.ofReal_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hΔ.apply j i, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.ofReal_div, Complex.ofReal_inv]
  ring

theorem bures_nonneg {s : ι → ℝ} (hs : ∀ i, 0 < s i) (Δ : Matrix ι ι ℂ) :
    0 ≤ bures s Δ := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact div_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
    (add_pos (hs i) (hs j)).le

theorem geometric_nonneg (s : ι → ℝ) (Δ : Matrix ι ι ℂ) :
    0 ≤ geometric s Δ := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact div_nonneg (Complex.normSq_nonneg _) (Real.sqrt_nonneg _)

theorem rightInverse_nonneg {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    (Δ : Matrix ι ι ℂ) : 0 ≤ rightInverse s Δ := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact div_nonneg (Complex.normSq_nonneg _) (hs j).le

theorem frobeniusSq_nonneg (Δ : Matrix ι ι ℂ) : 0 ≤ frobeniusSq Δ := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Complex.normSq_nonneg _

theorem twice_sqrt_mul_le_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  have hs := Real.sqrt_nonneg (a * b)
  have hsq := Real.sq_sqrt (mul_pos ha hb).le
  nlinarith [sq_nonneg (a - b)]

theorem harmonic_le_geometric_term {a b w : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hw : 0 ≤ w) :
    2 * w / (a + b) ≤ w / Real.sqrt (a * b) := by
  apply (div_le_div_iff₀ (add_pos ha hb) (Real.sqrt_pos.2 (mul_pos ha hb))).2
  have h := mul_le_mul_of_nonneg_right (twice_sqrt_mul_le_add ha hb) hw
  nlinarith

theorem geometric_le_arithmetic_term {a b w : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hw : 0 ≤ w) :
    w / Real.sqrt (a * b) ≤ (a + b) / (2 * a * b) * w := by
  have hs : 0 < Real.sqrt (a * b) := Real.sqrt_pos.2 (mul_pos ha hb)
  have hsq := Real.sq_sqrt (mul_pos ha hb).le
  have hav := mul_le_mul_of_nonneg_right (twice_sqrt_mul_le_add ha hb) hs.le
  have hwav := mul_le_mul_of_nonneg_right hav hw
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ hs (by positivity : 0 < 2 * a * b)).2
  nlinarith

/-- Symmetrizing the column-weighted formula gives the second sum in (4). -/
theorem rightInverse_eq_symmetric {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    {Δ : Matrix ι ι ℂ} (hΔ : Δ.IsHermitian) :
    rightInverse s Δ =
      ∑ i, ∑ j, (s i + s j) / (2 * s i * s j) * Complex.normSq (Δ i j) := by
  have hswap : (∑ i, ∑ j, Complex.normSq (Δ i j) / s i) = rightInverse s Δ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [normSq_symm hΔ j i]
  have hterm (i j : ι) :
      (s i + s j) / (2 * s i * s j) * Complex.normSq (Δ i j) =
        (Complex.normSq (Δ i j) / s i + Complex.normSq (Δ i j) / s j) / 2 := by
    field_simp [ne_of_gt (hs i), ne_of_gt (hs j)]
    <;> ring
  simp_rw [hterm, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [hswap]
  unfold rightInverse
  ring

/-- The first inequality in Equation (5). It does not require Hermitian symmetry. -/
theorem bures_le_geometric {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    (Δ : Matrix ι ι ℂ) : bures s Δ ≤ geometric s Δ := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact harmonic_le_geometric_term (hs i) (hs j) (Complex.normSq_nonneg _)

/-- The second inequality in (5), using Hermitian symmetry of the actual matrix. -/
theorem geometric_le_rightInverse {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    {Δ : Matrix ι ι ℂ} (hΔ : Δ.IsHermitian) :
    geometric s Δ ≤ rightInverse s Δ := by
  rw [rightInverse_eq_symmetric hs hΔ]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact geometric_le_arithmetic_term (hs i) (hs j) (Complex.normSq_nonneg _)

/-- Equation (5), jointly, for any finite Hermitian difference matrix. -/
theorem loss_comparison {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    {Δ : Matrix ι ι ℂ} (hΔ : Δ.IsHermitian) :
    bures s Δ ≤ geometric s Δ ∧ geometric s Δ ≤ rightInverse s Δ :=
  ⟨bures_le_geometric hs Δ, geometric_le_rightInverse hs hΔ⟩

/-- The classical chi-squared divergence, with the estimate in the denominator. -/
def classical (p q : ι → ℝ) : ℝ := ∑ i, (p i - q i) ^ 2 / q i

/-- Difference matrix of diagonal input and output states in their common eigenbasis. -/
def diagonalDifference (p q : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => ((p i - q i : ℝ) : ℂ))

theorem bures_diagonal {p q : ι → ℝ} (hq : ∀ i, 0 < q i) :
    bures q (diagonalDifference p q) = classical p q := by
  unfold bures diagonalDifference classical
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.diagonal_apply_eq, Complex.normSq_ofReal]
    field_simp [ne_of_gt (hq i)]
    <;> ring
  · intro j _ hji
    simp [Matrix.diagonal, Ne.symm hji]
  · simp

theorem geometric_diagonal {p q : ι → ℝ} (hq : ∀ i, 0 < q i) :
    geometric q (diagonalDifference p q) = classical p q := by
  unfold geometric diagonalDifference classical
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.diagonal_apply_eq, Complex.normSq_ofReal,
      Real.sqrt_mul_self (hq i).le, pow_two]
  · intro j _ hji
    simp [Matrix.diagonal, Ne.symm hji]
  · simp

theorem rightInverse_diagonal (p q : ι → ℝ) :
    rightInverse q (diagonalDifference p q) = classical p q := by
  unfold rightInverse diagonalDifference classical
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.diagonal_apply_eq, Complex.normSq_ofReal, pow_two]
  · intro j _ hji
    simp [Matrix.diagonal, Ne.symm hji]
  · simp

/-- A normalized classical output which dominates `t * p` controls the
chi-squared divergence. This is the commuting step in Lemma 5.4. -/
theorem classical_le_of_dominates {p q : ι → ℝ} {t : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hpSum : ∑ i, p i = 1) (hqSum : ∑ i, q i = 1)
    (ht : 0 < t) (hdom : ∀ i, t * p i ≤ q i) :
    classical p q ≤ 1 / t - 1 := by
  have hterm (i : ι) : p i ^ 2 / q i ≤ p i / t := by
    apply (div_le_div_iff₀ (hq i) ht).2
    have h := mul_le_mul_of_nonneg_left (hdom i) (hp i)
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hid (i : ι) : (p i - q i) ^ 2 / q i = p i ^ 2 / q i - 2 * p i + q i := by
    field_simp [ne_of_gt (hq i)]
    <;> ring
  unfold classical
  simp_rw [hid]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hpSum, hqSum]
  rw [← Finset.sum_div, hpSum] at hsum
  linarith

theorem normSq_add_le (z w : ℂ) :
    Complex.normSq (z + w) ≤ 2 * Complex.normSq z + 2 * Complex.normSq w := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - w.im)]

theorem rightInverse_add_le {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    (A B : Matrix ι ι ℂ) :
    rightInverse s (A + B) ≤ 2 * rightInverse s A + 2 * rightInverse s B := by
  have hterm (i j : ι) :
      Complex.normSq ((A + B) i j) / s j ≤
        2 * (Complex.normSq (A i j) / s j) +
          2 * (Complex.normSq (B i j) / s j) := by
    calc
      _ ≤ (2 * Complex.normSq (A i j) + 2 * Complex.normSq (B i j)) / s j :=
        div_le_div_of_nonneg_right (normSq_add_le _ _) (hs j).le
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm i j))
  simpa only [rightInverse, Finset.sum_add_distrib, Finset.mul_sum] using hsum

theorem rightInverse_le_frobeniusSq {s : ι → ℝ} {c : ℝ}
    (hs : ∀ i, 0 < s i) (hc : ∀ i, 1 ≤ c * s i)
    (Δ : Matrix ι ι ℂ) : rightInverse s Δ ≤ c * frobeniusSq Δ := by
  unfold rightInverse frobeniusSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply (div_le_iff₀ (hs j)).2
  have h := mul_le_mul_of_nonneg_left (hc j) (Complex.normSq_nonneg (Δ i j))
  nlinarith

/-- Spectrum of isotropic regularization of an estimate. -/
def regularizedSpectrum (α : ℝ) (p : ι → ℝ) (i : ι) : ℝ :=
  (1 - α) * p i + α / (Fintype.card ι : ℝ)

theorem regularizedSpectrum_pos [Nonempty ι] {α : ℝ} {p : ι → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hp : ∀ i, 0 ≤ p i) (i : ι) :
    0 < regularizedSpectrum α p i := by
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  unfold regularizedSpectrum
  exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (hp i)) (div_pos hα hd)

theorem regularizedSpectrum_sum [Nonempty ι] {α : ℝ} {p : ι → ℝ}
    (hpSum : ∑ i, p i = 1) : ∑ i, regularizedSpectrum α p i = 1 := by
  have hd : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.2 Fintype.card_pos)
  simp only [regularizedSpectrum, Finset.sum_add_distrib, ← Finset.mul_sum,
    hpSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hd]
  <;> ring

theorem classical_regularization_le [Nonempty ι] {α : ℝ} {p : ι → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i, p i = 1) :
    classical p (regularizedSpectrum α p) ≤ α / (1 - α) := by
  have h := classical_le_of_dominates hp
    (regularizedSpectrum_pos hα hα1 hp) hpSum (regularizedSpectrum_sum hpSum)
    (by linarith : 0 < 1 - α) (fun i => by
      unfold regularizedSpectrum
      have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
      exact le_add_of_nonneg_right (div_pos hα hd).le)
  have heq : 1 / (1 - α) - 1 = α / (1 - α) := by
    field_simp [ne_of_gt (by linarith : 0 < 1 - α)]
    <;> ring
  rwa [heq] at h

/-- Lemma 5.4 in an eigenbasis of the density estimate. The arbitrary complex
matrix `ρ` is the true state in that basis; `p` is the estimate's nonnegative,
normalized spectrum. The conclusion actually holds for every complex `ρ`.
-/
theorem regularization_bound [Nonempty ι] {α : ℝ} {p : ι → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i, p i = 1) (ρ : Matrix ι ι ℂ) :
    rightInverse (regularizedSpectrum α p)
        (ρ - Matrix.diagonal (fun i => (regularizedSpectrum α p i : ℂ))) ≤
      (2 * (Fintype.card ι : ℝ) / α) *
        frobeniusSq (ρ - Matrix.diagonal (fun i => (p i : ℂ))) + 2 * α / (1 - α) := by
  let q := regularizedSpectrum α p
  let P : Matrix ι ι ℂ := Matrix.diagonal (fun i => (p i : ℂ))
  let Q : Matrix ι ι ℂ := Matrix.diagonal (fun i => (q i : ℂ))
  have hq : ∀ i, 0 < q i := regularizedSpectrum_pos hα hα1 hp
  have hsplit : ρ - Q = (ρ - P) + (P - Q) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply]
    ring
  have hmin (i : ι) : 1 ≤ ((Fintype.card ι : ℝ) / α) * q i := by
    have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
    have hge : α / (Fintype.card ι : ℝ) ≤ q i := by
      exact le_add_of_nonneg_left (mul_nonneg (by linarith) (hp i))
    have h := mul_le_mul_of_nonneg_left hge (div_pos hd hα).le
    have heq : ((Fintype.card ι : ℝ) / α) * (α / (Fintype.card ι : ℝ)) = 1 := by
      field_simp [ne_of_gt hα, ne_of_gt hd]
    rwa [heq] at h
  have hfirst := rightInverse_le_frobeniusSq hq hmin (ρ - P)
  have hdiff : P - Q = diagonalDifference p q := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [P, Q, diagonalDifference]
    · simp [P, Q, diagonalDifference, Matrix.diagonal, hij]
  have hsecond : rightInverse q (P - Q) ≤ α / (1 - α) := by
    rw [hdiff, rightInverse_diagonal]
    exact classical_regularization_le hα hα1 hp hpSum
  change rightInverse q (ρ - Q) ≤ _
  rw [hsplit]
  calc
    _ ≤ 2 * rightInverse q (ρ - P) + 2 * rightInverse q (P - Q) :=
      rightInverse_add_le hq _ _
    _ ≤ 2 * (((Fintype.card ι : ℝ) / α) * frobeniusSq (ρ - P)) +
        2 * (α / (1 - α)) := by linarith
    _ = _ := by dsimp [P]; ring

/-- The explicit epsilon specialization stated after Equation (47). -/
theorem regularization_epsilon [Nonempty ι] {ε : ℝ} {p : ι → ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i, p i = 1) (ρ : Matrix ι ι ℂ)
    (herr : frobeniusSq (ρ - Matrix.diagonal (fun i => (p i : ℂ))) ≤
      ε ^ 2 / (64 * (Fintype.card ι : ℝ))) :
    rightInverse (regularizedSpectrum (ε / 8) p)
      (ρ - Matrix.diagonal (fun i => (regularizedSpectrum (ε / 8) p i : ℂ))) ≤ ε := by
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hα : 0 < ε / 8 := by positivity
  have hα1 : ε / 8 < 1 := by linarith
  have hbound := regularization_bound hα hα1 hp hpSum ρ
  have hmult := mul_le_mul_of_nonneg_left herr
    (by positivity : 0 ≤ 2 * (Fintype.card ι : ℝ) / (ε / 8))
  have heq : (2 * (Fintype.card ι : ℝ) / (ε / 8)) *
      (ε ^ 2 / (64 * (Fintype.card ι : ℝ))) = ε / 4 := by
    field_simp [ne_of_gt hε, ne_of_gt hd]
    <;> ring
  rw [heq] at hmult
  have hrest : 2 * (ε / 8) / (1 - ε / 8) ≤ ε / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - ε / 8)).2
    nlinarith
  linarith

end
end SpectralLoss
end Paper26
