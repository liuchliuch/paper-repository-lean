import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exact normalization of the two quantum chi-squared energies

The matrix `A` is represented in its own orthonormal eigenbasis by a strictly
positive finite spectrum `a`.  The matrix `ρ` retains arbitrary complex entries
in that basis.  Thus the two double sums below include all noncommuting,
off-diagonal contributions.  Their weights are respectively the inverse
Jordan superoperator and the right inverse in this basis.
-/

noncomputable section
open scoped BigOperators ComplexOrder
open Complex

namespace Paper26.Normalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The positive matrix in its spectral coordinates. -/
def diagonalMatrix (a : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => (a i : ℂ))

/-- A weighted quadratic matrix error, including every ordered matrix entry. -/
def spectralEnergy (ρ : Matrix ι ι ℂ) (a : ι → ℝ) (w : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * Complex.normSq (ρ i j - diagonalMatrix a i j)

/-- `Tr[(ρ-A) J_A⁻¹(ρ-A)]` in an eigenbasis of `A`, for Hermitian `ρ`. -/
def buresEnergy (ρ : Matrix ι ι ℂ) (a : ι → ℝ) : ℝ :=
  spectralEnergy ρ a (fun i j => 2 / (a i + a j))

/-- `Tr[(ρ-A)² A⁻¹]` in an eigenbasis of `A`, for Hermitian `ρ`. -/
def rightEnergy (ρ : Matrix ι ι ℂ) (a : ι → ℝ) : ℝ :=
  spectralEnergy ρ a (fun _ j => 1 / a j)

/-- Normalizing the positive matrix divides every eigenvalue by its trace. -/
def normalizedSpectrum (a : ι → ℝ) : ι → ℝ :=
  fun i => a i / (∑ j, a j)

lemma normSq_sub_real (z : ℂ) (x : ℝ) :
    Complex.normSq (z - (x : ℂ)) = Complex.normSq z + x ^ 2 - 2 * x * z.re := by
  simp only [Complex.normSq_sub, Complex.normSq_ofReal, Complex.conj_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

lemma spectralEnergy_expansion (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (w : ι → ι → ℝ) (ha : ∀ i, a i ≠ 0) (hw : ∀ i, w i i = 1 / a i) :
    spectralEnergy ρ a w =
      (∑ i, ∑ j, w i j * Complex.normSq (ρ i j)) -
        2 * (∑ i, (ρ i i).re) + ∑ i, a i := by
  have he : ∀ i j, w i j * Complex.normSq (ρ i j - diagonalMatrix a i j) =
      w i j * Complex.normSq (ρ i j) +
        if i = j then a i - 2 * (ρ i i).re else 0 := by
    intro i j
    by_cases h : i = j
    · subst j
      rw [if_pos rfl, diagonalMatrix, Matrix.diagonal_apply_eq, normSq_sub_real, hw]
      field_simp [ha i]
      <;> ring
    · simp [diagonalMatrix, Matrix.diagonal_apply_ne _ h, h]
  simp only [spectralEnergy, he, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma spectralEnergy_nonneg (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    0 ≤ spectralEnergy ρ a w := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hw i j) (Complex.normSq_nonneg _)

lemma buresEnergy_nonneg (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) : 0 ≤ buresEnergy ρ a := by
  apply spectralEnergy_nonneg
  intro i j
  exact div_nonneg (by norm_num) (le_of_lt (add_pos (ha i) (ha j)))

lemma rightEnergy_nonneg (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) : 0 ≤ rightEnergy ρ a := by
  apply spectralEnergy_nonneg
  intro i j
  exact div_nonneg (by norm_num) (ha j).le

end Paper26.Normalization

namespace Paper26.Normalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma spectralEnergy_normalization_formula (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (w : ι → ι → ℝ) (ha : ∀ i, a i ≠ 0) (ht : (∑ i, a i) ≠ 0)
    (hw : ∀ i, w i i = 1 / a i)
    (htrace : ∑ i, (ρ i i).re = 1) :
    spectralEnergy ρ (normalizedSpectrum a) (fun i j => (∑ k, a k) * w i j) =
      (∑ i, a i) * spectralEnergy ρ a w - ((∑ i, a i) - 1) ^ 2 := by
  have han : ∀ i, normalizedSpectrum a i ≠ 0 := fun i => div_ne_zero (ha i) ht
  have hwn : ∀ i, (∑ k, a k) * w i i = 1 / normalizedSpectrum a i := by
    intro i
    rw [hw]
    unfold normalizedSpectrum
    field_simp [ha i, ht]
  rw [spectralEnergy_expansion ρ (normalizedSpectrum a) _ han hwn,
    spectralEnergy_expansion ρ a w ha hw, htrace]
  have hs : (∑ i, normalizedSpectrum a i) = 1 := by
    simp only [normalizedSpectrum, ← Finset.sum_div, div_self ht]
  rw [hs]
  have hm : (∑ i, ∑ j, ((∑ k, a k) * w i j) * Complex.normSq (ρ i j)) =
      (∑ k, a k) * (∑ i, ∑ j, w i j * Complex.normSq (ρ i j)) := by
    simp only [mul_assoc, Finset.mul_sum]
  rw [hm]
  ring

/-- Equation (40), Bures case, with every complex matrix entry retained. -/
theorem bures_normalization_formula (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (ht : (∑ i, a i) ≠ 0)
    (htrace : ∑ i, (ρ i i).re = 1) :
    buresEnergy ρ (normalizedSpectrum a) =
      (∑ i, a i) * buresEnergy ρ a - ((∑ i, a i) - 1) ^ 2 := by
  have hw : ∀ i, 2 / (a i + a i) = 1 / a i := by
    intro i
    field_simp [ne_of_gt (ha i)]
    <;> ring
  have he : (fun i j => 2 / (normalizedSpectrum a i + normalizedSpectrum a j)) =
      (fun i j => (∑ k, a k) * (2 / (a i + a j))) := by
    funext i j
    unfold normalizedSpectrum
    have hp : a i + a j ≠ 0 := ne_of_gt (add_pos (ha i) (ha j))
    field_simp [hp, ht]
    <;> ring
  unfold buresEnergy
  rw [he]
  exact spectralEnergy_normalization_formula ρ a _ (fun i => ne_of_gt (ha i)) ht hw htrace

/-- Equation (40), right-inverse case, with every complex matrix entry retained. -/
theorem right_normalization_formula (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (ht : (∑ i, a i) ≠ 0)
    (htrace : ∑ i, (ρ i i).re = 1) :
    rightEnergy ρ (normalizedSpectrum a) =
      (∑ i, a i) * rightEnergy ρ a - ((∑ i, a i) - 1) ^ 2 := by
  have he : (fun (_ : ι) j => 1 / normalizedSpectrum a j) =
      (fun _ j => (∑ k, a k) * (1 / a j)) := by
    funext i j
    unfold normalizedSpectrum
    field_simp [ne_of_gt (ha j), ht]
  unfold rightEnergy
  rw [he]
  exact spectralEnergy_normalization_formula ρ a _ (fun i => ne_of_gt (ha i)) ht
    (fun _ => rfl) htrace

lemma spectrum_trace_pos [Nonempty ι] (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    0 < ∑ i, a i :=
  Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty

/-- The quadratic trace discrepancy is bounded by the unnormalized Bures error. -/
theorem bures_trace_discrepancy [Nonempty ι] (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (htrace : ∑ i, (ρ i i).re = 1) :
    ((∑ i, a i) - 1) ^ 2 ≤ (∑ i, a i) * buresEnergy ρ a := by
  have ht := spectrum_trace_pos a ha
  have hn : ∀ i, 0 < normalizedSpectrum a i := fun i => div_pos (ha i) ht
  have hp := buresEnergy_nonneg ρ (normalizedSpectrum a) hn
  rw [bures_normalization_formula ρ a ha (ne_of_gt ht) htrace] at hp
  linarith

/-- The quadratic trace discrepancy is bounded by the unnormalized right-inverse error. -/
theorem right_trace_discrepancy [Nonempty ι] (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (htrace : ∑ i, (ρ i i).re = 1) :
    ((∑ i, a i) - 1) ^ 2 ≤ (∑ i, a i) * rightEnergy ρ a := by
  have ht := spectrum_trace_pos a ha
  have hn : ∀ i, 0 < normalizedSpectrum a i := fun i => div_pos (ha i) ht
  have hp := rightEnergy_nonneg ρ (normalizedSpectrum a) hn
  rw [right_normalization_formula ρ a ha (ne_of_gt ht) htrace] at hp
  linarith

lemma trace_le_two_of_small_energy (t E : ℝ) (ht : 0 < t)
    (hquad : (t - 1) ^ 2 ≤ t * E) (hE : E ≤ 1 / 2) : t ≤ 2 := by
  have hmul : t * E ≤ t * (1 / 2) := mul_le_mul_of_nonneg_left hE ht.le
  by_contra h
  have ht2 : 2 < t := lt_of_not_ge h
  have hm : 0 < (t - 2) * (t - 1 / 2) := mul_pos (by linarith) (by linarith)
  nlinarith

lemma normalized_loss_le_twice_energy (t E χ : ℝ) (ht : 0 < t)
    (hquad : (t - 1) ^ 2 ≤ t * E) (hE : E ≤ 1 / 2)
    (hidentity : χ = t * E - (t - 1) ^ 2) : χ ≤ 2 * E := by
  have hE0 : 0 ≤ E := by nlinarith [sq_nonneg (t - 1)]
  have ht2 := trace_le_two_of_small_energy t E ht hquad hE
  have hmul : t * E ≤ 2 * E := mul_le_mul_of_nonneg_right ht2 hE0
  nlinarith [sq_nonneg (t - 1)]

/-- The two final conclusions of Lemma 5.2 for Bures loss. -/
theorem bures_small_energy [Nonempty ι] (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (htrace : ∑ i, (ρ i i).re = 1)
    (hE : buresEnergy ρ a ≤ 1 / 2) :
    (∑ i, a i) ≤ 2 ∧ buresEnergy ρ (normalizedSpectrum a) ≤ 2 * buresEnergy ρ a := by
  have ht := spectrum_trace_pos a ha
  have hq := bures_trace_discrepancy ρ a ha htrace
  exact ⟨trace_le_two_of_small_energy _ _ ht hq hE,
    normalized_loss_le_twice_energy _ _ _ ht hq hE
      (bures_normalization_formula ρ a ha (ne_of_gt ht) htrace)⟩

/-- The two final conclusions of Lemma 5.2 for right-inverse loss. -/
theorem right_small_energy [Nonempty ι] (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (htrace : ∑ i, (ρ i i).re = 1)
    (hE : rightEnergy ρ a ≤ 1 / 2) :
    (∑ i, a i) ≤ 2 ∧ rightEnergy ρ (normalizedSpectrum a) ≤ 2 * rightEnergy ρ a := by
  have ht := spectrum_trace_pos a ha
  have hq := right_trace_discrepancy ρ a ha htrace
  exact ⟨trace_le_two_of_small_energy _ _ ht hq hE,
    normalized_loss_le_twice_energy _ _ _ ht hq hE
      (right_normalization_formula ρ a ha (ne_of_gt ht) htrace)⟩

end Paper26.Normalization

namespace Paper26.Normalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Inverse of the Jordan multiplication operator, in the eigenbasis of `A`. -/
def inverseJordan (a : ι → ℝ) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => ((2 / (a i + a j) : ℝ) : ℂ) * X i j

lemma diagonalMatrix_conjTranspose (a : ι → ℝ) :
    (diagonalMatrix a).conjTranspose = diagonalMatrix a := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [diagonalMatrix, Matrix.conjTranspose_apply, Complex.star_def]
  · simp [diagonalMatrix, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Complex.star_def, hij, Ne.symm hij]

lemma hermitian_mul_reverse (X : Matrix ι ι ℂ) (hX : X.conjTranspose = X) (i j : ι) :
    X i j * X j i = (Complex.normSq (X i j) : ℂ) := by
  have hj : X j i = star (X i j) := by
    have hj := congrArg (fun M : Matrix ι ι ℂ => M j i) hX
    simpa only [Matrix.conjTranspose_apply, Complex.star_def] using hj.symm
  rw [hj]
  simpa only [Complex.star_def] using Complex.mul_conj (X i j)

/-- The displayed spectral formula really is an inverse to `X ↦ (AX+XA)/2`. -/
theorem inverseJordan_equation (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (X : Matrix ι ι ℂ) :
    diagonalMatrix a * inverseJordan a X + inverseJordan a X * diagonalMatrix a =
      (2 : ℂ) • X := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, diagonalMatrix,
    Matrix.diagonal_mul, Matrix.mul_diagonal, inverseJordan]
  have hc : ((a i : ℂ) + (a j : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (add_pos (ha i) (ha j)))
  push_cast
  field_simp [hc]
  <;> ring

/-- The Bures double sum equals the real part of the original matrix trace. -/
theorem buresEnergy_eq_trace (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (hρ : ρ.conjTranspose = ρ) :
    buresEnergy ρ a =
      (Matrix.trace ((ρ - diagonalMatrix a) *
        inverseJordan a (ρ - diagonalMatrix a))).re := by
  let X := ρ - diagonalMatrix a
  have hX : X.conjTranspose = X := by
    dsimp [X]
    rw [Matrix.conjTranspose_sub, hρ, diagonalMatrix_conjTranspose]
  change (∑ i, ∑ j, 2 / (a i + a j) * Complex.normSq (X i j)) = _
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum, inverseJordan]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_left_comm (X i j), hermitian_mul_reverse X hX i j,
    ← Complex.ofReal_mul, Complex.ofReal_re, add_comm (a j) (a i)]

/-- The right-inverse double sum equals `Re Tr[(ρ-A)² A⁻¹]`. -/
theorem rightEnergy_eq_trace (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (hρ : ρ.conjTranspose = ρ) :
    rightEnergy ρ a =
      (Matrix.trace ((ρ - diagonalMatrix a) * (ρ - diagonalMatrix a) *
        diagonalMatrix (fun i => 1 / a i))).re := by
  let X := ρ - diagonalMatrix a
  have hX : X.conjTranspose = X := by
    dsimp [X]
    rw [Matrix.conjTranspose_sub, hρ, diagonalMatrix_conjTranspose]
  have hcyc : Matrix.trace (X * diagonalMatrix (fun i => 1 / a i) * X) =
      Matrix.trace (X * X * diagonalMatrix (fun i => 1 / a i)) :=
    Matrix.trace_mul_cycle _ _ _
  rw [← hcyc]
  change (∑ i, ∑ j, 1 / a j * Complex.normSq (X i j)) = _
  have hm : X * diagonalMatrix (fun i => 1 / a i) =
      (fun i j => X i j * ((1 / a j : ℝ) : ℂ)) := by
    ext i j
    simp [diagonalMatrix, Matrix.mul_diagonal]
  rw [hm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_right_comm (X i j), hermitian_mul_reverse X hX i j]
  simp [mul_comm]

end Paper26.Normalization

namespace Paper26.Normalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_one_coordinates (ρ : Matrix ι ι ℂ) (htrace : Matrix.trace ρ = 1) :
    ∑ i, (ρ i i).re = 1 := by
  have h := congrArg Complex.re htrace
  simpa [Matrix.trace, Matrix.diag, Complex.re_sum] using h

lemma diagonalMatrix_normalized (a : ι → ℝ) :
    diagonalMatrix (normalizedSpectrum a) =
      ((1 / (∑ i, a i) : ℝ) : ℂ) • diagonalMatrix a := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [diagonalMatrix, normalizedSpectrum, div_eq_mul_inv, mul_comm]
  · simp [diagonalMatrix, hij]

/-- The right-inverse diagonal matrix is the actual matrix inverse. -/
theorem diagonalMatrix_inverse (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    diagonalMatrix a * diagonalMatrix (fun i => 1 / a i) = 1 ∧
    diagonalMatrix (fun i => 1 / a i) * diagonalMatrix a = 1 := by
  constructor <;> ext i j <;> by_cases hij : i = j
  all_goals
    simp [diagonalMatrix, Matrix.mul_diagonal, Matrix.one_apply, hij, ha,
      Complex.ofReal_eq_zero]

/-- All of Lemma 5.2 for the Bures trace energy, in finite spectral coordinates. -/
theorem lemma_5_2_bures_matrix [Nonempty ι] (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (hρ : ρ.conjTranspose = ρ) (ha : ∀ i, 0 < a i)
    (htrace : Matrix.trace ρ = 1) :
    let t := ∑ i, a i
    let E := (Matrix.trace ((ρ - diagonalMatrix a) *
      inverseJordan a (ρ - diagonalMatrix a))).re
    buresEnergy ρ (normalizedSpectrum a) = t * E - (t - 1) ^ 2 ∧
      (t - 1) ^ 2 ≤ t * E ∧
      (E ≤ 1 / 2 → t ≤ 2 ∧ buresEnergy ρ (normalizedSpectrum a) ≤ 2 * E) := by
  dsimp
  rw [← buresEnergy_eq_trace ρ a hρ]
  have ht := spectrum_trace_pos a ha
  have htr := trace_one_coordinates ρ htrace
  exact ⟨bures_normalization_formula ρ a ha (ne_of_gt ht) htr,
    bures_trace_discrepancy ρ a ha htr, bures_small_energy ρ a ha htr⟩

/-- All of Lemma 5.2 for the right-inverse trace energy, in finite spectral coordinates. -/
theorem lemma_5_2_right_matrix [Nonempty ι] (ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (hρ : ρ.conjTranspose = ρ) (ha : ∀ i, 0 < a i)
    (htrace : Matrix.trace ρ = 1) :
    let t := ∑ i, a i
    let E := (Matrix.trace ((ρ - diagonalMatrix a) * (ρ - diagonalMatrix a) *
      diagonalMatrix (fun i => 1 / a i))).re
    rightEnergy ρ (normalizedSpectrum a) = t * E - (t - 1) ^ 2 ∧
      (t - 1) ^ 2 ≤ t * E ∧
      (E ≤ 1 / 2 → t ≤ 2 ∧ rightEnergy ρ (normalizedSpectrum a) ≤ 2 * E) := by
  dsimp
  rw [← rightEnergy_eq_trace ρ a hρ]
  have ht := spectrum_trace_pos a ha
  have htr := trace_one_coordinates ρ htrace
  exact ⟨right_normalization_formula ρ a ha (ne_of_gt ht) htr,
    right_trace_discrepancy ρ a ha htr, right_small_energy ρ a ha htr⟩

end Paper26.Normalization

namespace Paper26.Normalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unitary change from spectral coordinates to the original basis. -/
def conjugate (U X : Matrix ι ι ℂ) : Matrix ι ι ℂ := U * X * U.conjTranspose

/-- Matrix entries in the orthonormal basis whose columns are `U`. -/
def coordinates (U X : Matrix ι ι ℂ) : Matrix ι ι ℂ := U.conjTranspose * X * U

lemma conjugate_sub (U X Y : Matrix ι ι ℂ) :
    conjugate U (X - Y) = conjugate U X - conjugate U Y := by
  simp [conjugate, Matrix.mul_sub, Matrix.sub_mul]

lemma coordinates_sub (U X Y : Matrix ι ι ℂ) :
    coordinates U (X - Y) = coordinates U X - coordinates U Y := by
  simp [coordinates, Matrix.mul_sub, Matrix.sub_mul]

lemma conjugate_mul (U X Y : Matrix ι ι ℂ) (hU : U.conjTranspose * U = 1) :
    conjugate U (X * Y) = conjugate U X * conjugate U Y := by
  unfold conjugate
  calc
    U * (X * Y) * U.conjTranspose = U * X * (U.conjTranspose * U) * Y *
        U.conjTranspose := by rw [hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = (U * X * U.conjTranspose) * (U * Y * U.conjTranspose) := by
      simp only [Matrix.mul_assoc]

lemma coordinates_conjugate (U X : Matrix ι ι ℂ) (hU : U.conjTranspose * U = 1) :
    coordinates U (conjugate U X) = X := by
  unfold coordinates conjugate
  calc
    U.conjTranspose * (U * X * U.conjTranspose) * U =
        (U.conjTranspose * U) * X * (U.conjTranspose * U) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [hU]; simp

lemma conjugate_coordinates (U X : Matrix ι ι ℂ) (hU : U * U.conjTranspose = 1) :
    conjugate U (coordinates U X) = X := by
  unfold coordinates conjugate
  calc
    U * (U.conjTranspose * X * U) * U.conjTranspose =
        (U * U.conjTranspose) * X * (U * U.conjTranspose) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [hU]; simp

lemma trace_conjugate (U X : Matrix ι ι ℂ) (hU : U.conjTranspose * U = 1) :
    Matrix.trace (conjugate U X) = Matrix.trace X := by
  rw [conjugate, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

lemma trace_coordinates (U X : Matrix ι ι ℂ) (hU : U * U.conjTranspose = 1) :
    Matrix.trace (coordinates U X) = Matrix.trace X := by
  rw [coordinates, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

lemma coordinates_hermitian (U X : Matrix ι ι ℂ) (hX : X.conjTranspose = X) :
    (coordinates U X).conjTranspose = coordinates U X := by
  simp [coordinates, Matrix.conjTranspose_mul, hX, Matrix.mul_assoc]

/-- Jordan inverse transported back to the original matrix basis. -/
def transportedInverseJordan (U : Matrix ι ι ℂ) (a : ι → ℝ)
    (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  conjugate U (inverseJordan a (coordinates U X))

/-- Actual Bures trace energy in the original basis. -/
def matrixBuresEnergy (U : Matrix ι ι ℂ) (a : ι → ℝ) (ρ : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace ((ρ - conjugate U (diagonalMatrix a)) *
    transportedInverseJordan U a (ρ - conjugate U (diagonalMatrix a)))).re

/-- Actual right-inverse trace energy in the original basis. -/
def matrixRightEnergy (U : Matrix ι ι ℂ) (a : ι → ℝ) (ρ : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace ((ρ - conjugate U (diagonalMatrix a)) *
    (ρ - conjugate U (diagonalMatrix a)) *
    conjugate U (diagonalMatrix (fun i => 1 / a i)))).re

lemma conjugate_error (U ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (hU : U * U.conjTranspose = 1) :
    ρ - conjugate U (diagonalMatrix a) =
      conjugate U (coordinates U ρ - diagonalMatrix a) := by
  rw [conjugate_sub, conjugate_coordinates U ρ hU]

lemma matrixBuresEnergy_coordinates (U ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (hU₁ : U.conjTranspose * U = 1) (hU₂ : U * U.conjTranspose = 1)
    (hρ : ρ.conjTranspose = ρ) :
    matrixBuresEnergy U a ρ = buresEnergy (coordinates U ρ) a := by
  unfold matrixBuresEnergy transportedInverseJordan
  rw [conjugate_error U ρ a hU₂, coordinates_conjugate U _ hU₁,
    ← conjugate_mul U _ _ hU₁, trace_conjugate U _ hU₁,
    buresEnergy_eq_trace _ _ (coordinates_hermitian U ρ hρ)]

lemma matrixRightEnergy_coordinates (U ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (hU₁ : U.conjTranspose * U = 1) (hU₂ : U * U.conjTranspose = 1)
    (hρ : ρ.conjTranspose = ρ) :
    matrixRightEnergy U a ρ = rightEnergy (coordinates U ρ) a := by
  unfold matrixRightEnergy
  rw [conjugate_error U ρ a hU₂, ← conjugate_mul U _ _ hU₁,
    ← conjugate_mul U _ _ hU₁, trace_conjugate U _ hU₁,
    rightEnergy_eq_trace _ _ (coordinates_hermitian U ρ hρ)]

lemma conjugate_smul (U X : Matrix ι ι ℂ) (c : ℂ) :
    conjugate U (c • X) = c • conjugate U X := by
  simp [conjugate, Matrix.mul_smul, Matrix.smul_mul]

/-- In the original basis the normalized spectrum gives exactly `A / Tr A`. -/
theorem conjugate_normalizedSpectrum (U : Matrix ι ι ℂ) (a : ι → ℝ) :
    conjugate U (diagonalMatrix (normalizedSpectrum a)) =
      ((1 / (∑ i, a i) : ℝ) : ℂ) • conjugate U (diagonalMatrix a) := by
  rw [diagonalMatrix_normalized, conjugate_smul]

/-- Equation (40) and both small-energy conclusions after any unitary change of basis. -/
theorem lemma_5_2_unitary [Nonempty ι] (U ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (hU₁ : U.conjTranspose * U = 1) (hU₂ : U * U.conjTranspose = 1)
    (hρ : ρ.conjTranspose = ρ) (ha : ∀ i, 0 < a i)
    (htrace : Matrix.trace ρ = 1) :
    let t := ∑ i, a i
    let EB := matrixBuresEnergy U a ρ
    let ER := matrixRightEnergy U a ρ
    (matrixBuresEnergy U (normalizedSpectrum a) ρ = t * EB - (t - 1) ^ 2 ∧
      (t - 1) ^ 2 ≤ t * EB ∧
      (EB ≤ 1 / 2 → t ≤ 2 ∧ matrixBuresEnergy U (normalizedSpectrum a) ρ ≤ 2 * EB)) ∧
    (matrixRightEnergy U (normalizedSpectrum a) ρ = t * ER - (t - 1) ^ 2 ∧
      (t - 1) ^ 2 ≤ t * ER ∧
      (ER ≤ 1 / 2 → t ≤ 2 ∧ matrixRightEnergy U (normalizedSpectrum a) ρ ≤ 2 * ER)) := by
  dsimp
  simp only [matrixBuresEnergy_coordinates U ρ _ hU₁ hU₂ hρ,
    matrixRightEnergy_coordinates U ρ _ hU₁ hU₂ hρ]
  have htr : Matrix.trace (coordinates U ρ) = 1 := by
    rw [trace_coordinates U ρ hU₂, htrace]
  have ht := spectrum_trace_pos a ha
  have hc := trace_one_coordinates _ htr
  exact ⟨⟨bures_normalization_formula _ _ ha (ne_of_gt ht) hc,
    bures_trace_discrepancy _ _ ha hc, bures_small_energy _ _ ha hc⟩,
    ⟨right_normalization_formula _ _ ha (ne_of_gt ht) hc,
    right_trace_discrepancy _ _ ha hc, right_small_energy _ _ ha hc⟩⟩

/-- Every positive definite finite complex matrix has the positive spectral
representation required above.  Thus the unitary theorem covers arbitrary `A > 0`. -/
theorem exists_positive_spectral_representation (A : Matrix ι ι ℂ) (hA : A.PosDef) :
    ∃ (U : Matrix ι ι ℂ) (a : ι → ℝ),
      U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      (∀ i, 0 < a i) ∧ A = conjugate U (diagonalMatrix a) := by
  refine ⟨hA.1.eigenvectorUnitary, hA.1.eigenvalues, ?_, ?_, hA.eigenvalues_pos, ?_⟩
  · simpa only [unitary.coe_star, Matrix.star_eq_conjTranspose] using
      unitary.coe_star_mul_self hA.1.eigenvectorUnitary
  · simpa only [unitary.coe_star, Matrix.star_eq_conjTranspose] using
      unitary.coe_mul_star_self hA.1.eigenvectorUnitary
  · simpa only [conjugate, diagonalMatrix, Function.comp_def,
      Matrix.star_eq_conjTranspose] using hA.1.spectral_theorem

end Paper26.Normalization

namespace Paper26.Normalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma conjugate_add (U X Y : Matrix ι ι ℂ) :
    conjugate U (X + Y) = conjugate U X + conjugate U Y := by
  simp [conjugate, Matrix.mul_add, Matrix.add_mul]

/-- The transported Jordan inverse solves the original-basis Jordan equation. -/
theorem transportedInverseJordan_equation (U X : Matrix ι ι ℂ) (a : ι → ℝ)
    (hU₁ : U.conjTranspose * U = 1) (hU₂ : U * U.conjTranspose = 1)
    (ha : ∀ i, 0 < a i) :
    conjugate U (diagonalMatrix a) * transportedInverseJordan U a X +
      transportedInverseJordan U a X * conjugate U (diagonalMatrix a) =
      (2 : ℂ) • X := by
  have h := congrArg (conjugate U) (inverseJordan_equation a ha (coordinates U X))
  rw [conjugate_add, conjugate_mul U _ _ hU₁, conjugate_mul U _ _ hU₁,
    conjugate_smul, conjugate_coordinates U X hU₂] at h
  exact h

/-- Spectral inversion gives the actual nonsingular matrix inverse in every basis. -/
theorem conjugate_diagonal_inverse (U : Matrix ι ι ℂ) (a : ι → ℝ)
    (hU₁ : U.conjTranspose * U = 1) (hU₂ : U * U.conjTranspose = 1)
    (ha : ∀ i, 0 < a i) :
    (conjugate U (diagonalMatrix a))⁻¹ =
      conjugate U (diagonalMatrix (fun i => 1 / a i)) := by
  apply Matrix.inv_eq_right_inv
  rw [← conjugate_mul U _ _ hU₁,
    (diagonalMatrix_inverse a (fun i => ne_of_gt (ha i))).1]
  simpa [conjugate] using hU₂

/-- Right-inverse quadratic error using the actual matrix inverse. -/
def standardRightEnergy (ρ A : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace ((ρ - A) * (ρ - A) * A⁻¹)).re

lemma matrixRightEnergy_standard (U ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (hU₁ : U.conjTranspose * U = 1) (hU₂ : U * U.conjTranspose = 1)
    (ha : ∀ i, 0 < a i) :
    matrixRightEnergy U a ρ = standardRightEnergy ρ (conjugate U (diagonalMatrix a)) := by
  unfold matrixRightEnergy standardRightEnergy
  rw [conjugate_diagonal_inverse U a hU₁ hU₂ ha]

lemma trace_conjugate_diagonal (U : Matrix ι ι ℂ) (a : ι → ℝ)
    (hU : U.conjTranspose * U = 1) :
    (Matrix.trace (conjugate U (diagonalMatrix a))).re = ∑ i, a i := by
  rw [trace_conjugate U _ hU]
  simp [Matrix.trace, Matrix.diag, diagonalMatrix, Complex.re_sum]

/-- Lemma 5.2 for an arbitrary positive definite complex matrix, with the
right-inverse loss written using its actual nonsingular inverse. -/
theorem lemma_5_2_right_posDef [Nonempty ι] (ρ A : Matrix ι ι ℂ)
    (hρ : ρ.conjTranspose = ρ) (hA : A.PosDef) (htrace : Matrix.trace ρ = 1) :
    let t := (Matrix.trace A).re
    let E := standardRightEnergy ρ A
    let σ := ((1 / t : ℝ) : ℂ) • A
    standardRightEnergy ρ σ = t * E - (t - 1) ^ 2 ∧
      (t - 1) ^ 2 ≤ t * E ∧
      (E ≤ 1 / 2 → t ≤ 2 ∧ standardRightEnergy ρ σ ≤ 2 * E) := by
  obtain ⟨U, a, hU₁, hU₂, ha, hAeq⟩ := exists_positive_spectral_representation A hA
  have ht : (Matrix.trace A).re = ∑ i, a i := by
    rw [hAeq, trace_conjugate_diagonal U a hU₁]
  have hp := (lemma_5_2_unitary U ρ a hU₁ hU₂ hρ ha htrace).2
  dsimp at hp ⊢
  have han : ∀ i, 0 < normalizedSpectrum a i :=
    fun i => div_pos (ha i) (spectrum_trace_pos a ha)
  rw [matrixRightEnergy_standard U ρ _ hU₁ hU₂ han,
    matrixRightEnergy_standard U ρ _ hU₁ hU₂ ha,
    conjugate_normalizedSpectrum, ← hAeq] at hp
  simpa only [ht] using hp

end Paper26.Normalization

namespace Paper26.Normalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma inverseJordan_unique (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (X Y : Matrix ι ι ℂ)
    (hY : diagonalMatrix a * Y + Y * diagonalMatrix a = (2 : ℂ) • X) :
    Y = inverseJordan a X := by
  have hJ := inverseJordan_equation a ha X
  ext i j
  have hy := congrArg (fun M : Matrix ι ι ℂ => M i j) hY
  have hj := congrArg (fun M : Matrix ι ι ℂ => M i j) hJ
  simp only [Matrix.add_apply, diagonalMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul] at hy hj
  have hc : ((a i : ℂ) + (a j : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (add_pos (ha i) (ha j)))
  apply mul_left_cancel₀ hc
  calc
    ((a i : ℂ) + (a j : ℂ)) * Y i j =
        (a i : ℂ) * Y i j + Y i j * (a j : ℂ) := by ring
    _ = 2 * X i j := hy
    _ = (a i : ℂ) * inverseJordan a X i j + inverseJordan a X i j * (a j : ℂ) := hj.symm
    _ = ((a i : ℂ) + (a j : ℂ)) * inverseJordan a X i j := by ring

lemma coordinates_add (U X Y : Matrix ι ι ℂ) :
    coordinates U (X + Y) = coordinates U X + coordinates U Y := by
  simp [coordinates, Matrix.mul_add, Matrix.add_mul]

lemma coordinates_smul (U X : Matrix ι ι ℂ) (c : ℂ) :
    coordinates U (c • X) = c • coordinates U X := by
  simp [coordinates, Matrix.mul_smul, Matrix.smul_mul]

lemma coordinates_mul (U X Y : Matrix ι ι ℂ) (hU : U * U.conjTranspose = 1) :
    coordinates U (X * Y) = coordinates U X * coordinates U Y := by
  have h := conjugate_mul U.conjTranspose X Y (by simpa using hU)
  simpa only [conjugate, coordinates, Matrix.conjTranspose_conjTranspose] using h

/-- Positivity of the spectrum gives uniqueness of the inverse-Jordan equation
also in the original basis. -/
theorem transportedInverseJordan_unique (U X Y : Matrix ι ι ℂ) (a : ι → ℝ)
    (hU₁ : U.conjTranspose * U = 1) (hU₂ : U * U.conjTranspose = 1)
    (ha : ∀ i, 0 < a i)
    (hY : conjugate U (diagonalMatrix a) * Y + Y * conjugate U (diagonalMatrix a) =
      (2 : ℂ) • X) : Y = transportedInverseJordan U a X := by
  have h := congrArg (coordinates U) hY
  rw [coordinates_add, coordinates_mul U _ _ hU₂, coordinates_mul U _ _ hU₂,
    coordinates_conjugate U _ hU₁, coordinates_smul] at h
  have hy := inverseJordan_unique a ha (coordinates U X) (coordinates U Y) h
  have hc := congrArg (conjugate U) hy
  rw [conjugate_coordinates U Y hU₂] at hc
  exact hc

/-- The intrinsic inverse of `Y ↦ (AY+YA)/2`, defined by its unique solution
whenever it exists.  Positive definiteness supplies existence and uniqueness. -/
def jordanInverse (A X : Matrix ι ι ℂ) : Matrix ι ι ℂ := by
  classical
  exact if h : ∃ Y : Matrix ι ι ℂ, A * Y + Y * A = (2 : ℂ) • X
    then Classical.choose h else 0

lemma jordanInverse_equation_of_exists (A X : Matrix ι ι ℂ)
    (h : ∃ Y : Matrix ι ι ℂ, A * Y + Y * A = (2 : ℂ) • X) :
    A * jordanInverse A X + jordanInverse A X * A = (2 : ℂ) • X := by
  unfold jordanInverse
  rw [dif_pos h]
  exact Classical.choose_spec h

lemma jordanInverse_eq_transported (U X : Matrix ι ι ℂ) (a : ι → ℝ)
    (hU₁ : U.conjTranspose * U = 1) (hU₂ : U * U.conjTranspose = 1)
    (ha : ∀ i, 0 < a i) :
    jordanInverse (conjugate U (diagonalMatrix a)) X = transportedInverseJordan U a X := by
  apply transportedInverseJordan_unique U X _ a hU₁ hU₂ ha
  apply jordanInverse_equation_of_exists
  exact ⟨transportedInverseJordan U a X,
    transportedInverseJordan_equation U X a hU₁ hU₂ ha⟩

/-- The Bures energy with the intrinsic inverse-Jordan operator. -/
def standardBuresEnergy (ρ A : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace ((ρ - A) * jordanInverse A (ρ - A))).re

lemma matrixBuresEnergy_standard (U ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (hU₁ : U.conjTranspose * U = 1) (hU₂ : U * U.conjTranspose = 1)
    (ha : ∀ i, 0 < a i) :
    matrixBuresEnergy U a ρ = standardBuresEnergy ρ (conjugate U (diagonalMatrix a)) := by
  unfold matrixBuresEnergy standardBuresEnergy
  rw [jordanInverse_eq_transported U _ a hU₁ hU₂ ha]

/-- Lemma 5.2 for arbitrary positive definite complex matrices in the Bures case.
The inverse-Jordan operator is characterized by a unique matrix equation. -/
theorem lemma_5_2_bures_posDef [Nonempty ι] (ρ A : Matrix ι ι ℂ)
    (hρ : ρ.conjTranspose = ρ) (hA : A.PosDef) (htrace : Matrix.trace ρ = 1) :
    let t := (Matrix.trace A).re
    let E := standardBuresEnergy ρ A
    let σ := ((1 / t : ℝ) : ℂ) • A
    standardBuresEnergy ρ σ = t * E - (t - 1) ^ 2 ∧
      (t - 1) ^ 2 ≤ t * E ∧
      (E ≤ 1 / 2 → t ≤ 2 ∧ standardBuresEnergy ρ σ ≤ 2 * E) := by
  obtain ⟨U, a, hU₁, hU₂, ha, hAeq⟩ := exists_positive_spectral_representation A hA
  have ht : (Matrix.trace A).re = ∑ i, a i := by
    rw [hAeq, trace_conjugate_diagonal U a hU₁]
  have hp := (lemma_5_2_unitary U ρ a hU₁ hU₂ hρ ha htrace).1
  dsimp at hp ⊢
  have han : ∀ i, 0 < normalizedSpectrum a i :=
    fun i => div_pos (ha i) (spectrum_trace_pos a ha)
  rw [matrixBuresEnergy_standard U ρ _ hU₁ hU₂ han,
    matrixBuresEnergy_standard U ρ _ hU₁ hU₂ ha,
    conjugate_normalizedSpectrum, ← hAeq] at hp
  simpa only [ht] using hp

end Paper26.Normalization

namespace Paper26.Normalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For every positive definite matrix, `jordanInverse` solves the defining
inverse-Jordan equation for every input matrix. -/
theorem jordanInverse_equation_posDef (A X : Matrix ι ι ℂ) (hA : A.PosDef) :
    A * jordanInverse A X + jordanInverse A X * A = (2 : ℂ) • X := by
  obtain ⟨U, a, hU₁, hU₂, ha, hAeq⟩ := exists_positive_spectral_representation A hA
  rw [hAeq, jordanInverse_eq_transported U X a hU₁ hU₂ ha]
  exact transportedInverseJordan_equation U X a hU₁ hU₂ ha

/-- The inverse-Jordan equation has exactly one solution for positive definite
`A`; hence the intrinsic definition has no dependence on the chosen eigenbasis. -/
theorem jordanInverse_unique_posDef (A X Y : Matrix ι ι ℂ) (hA : A.PosDef)
    (hY : A * Y + Y * A = (2 : ℂ) • X) : Y = jordanInverse A X := by
  obtain ⟨U, a, hU₁, hU₂, ha, hAeq⟩ := exists_positive_spectral_representation A hA
  rw [hAeq] at hY ⊢
  rw [jordanInverse_eq_transported U X a hU₁ hU₂ ha]
  exact transportedInverseJordan_unique U X Y a hU₁ hU₂ ha hY

/-- Positive definiteness makes `Re Tr A` precisely the real scalar `Tr A`. -/
theorem posDef_trace_real (A : Matrix ι ι ℂ) (hA : A.PosDef) :
    ((Matrix.trace A).re : ℂ) = Matrix.trace A := by
  obtain ⟨U, a, hU₁, _, _, hAeq⟩ := exists_positive_spectral_representation A hA
  rw [hAeq, trace_conjugate U _ hU₁]
  simp [Matrix.trace, Matrix.diag, diagonalMatrix, Complex.re_sum, ← Complex.ofReal_sum]

lemma nonempty_of_trace_one (ρ : Matrix ι ι ℂ) (htrace : Matrix.trace ρ = 1) :
    Nonempty ι := by
  classical
  by_contra h
  haveI : IsEmpty ι := not_nonempty_iff.mp h
  simp [Matrix.trace] at htrace

/-- The complete Bures normalization lemma, without an extra assumption that
the index type is nonempty: trace one already entails that fact. -/
theorem lemma_5_2_bures (ρ A : Matrix ι ι ℂ)
    (hρ : ρ.conjTranspose = ρ) (hA : A.PosDef) (htrace : Matrix.trace ρ = 1) :
    let t := (Matrix.trace A).re
    let E := standardBuresEnergy ρ A
    let σ := ((1 / t : ℝ) : ℂ) • A
    standardBuresEnergy ρ σ = t * E - (t - 1) ^ 2 ∧
      (t - 1) ^ 2 ≤ t * E ∧
      (E ≤ 1 / 2 → t ≤ 2 ∧ standardBuresEnergy ρ σ ≤ 2 * E) := by
  letI : Nonempty ι := nonempty_of_trace_one ρ htrace
  exact lemma_5_2_bures_posDef ρ A hρ hA htrace

/-- The complete right-inverse normalization lemma, with the source hypotheses. -/
theorem lemma_5_2_right (ρ A : Matrix ι ι ℂ)
    (hρ : ρ.conjTranspose = ρ) (hA : A.PosDef) (htrace : Matrix.trace ρ = 1) :
    let t := (Matrix.trace A).re
    let E := standardRightEnergy ρ A
    let σ := ((1 / t : ℝ) : ℂ) • A
    standardRightEnergy ρ σ = t * E - (t - 1) ^ 2 ∧
      (t - 1) ^ 2 ≤ t * E ∧
      (E ≤ 1 / 2 → t ≤ 2 ∧ standardRightEnergy ρ σ ≤ 2 * E) := by
  letI : Nonempty ι := nonempty_of_trace_one ρ htrace
  exact lemma_5_2_right_posDef ρ A hρ hA htrace

end Paper26.Normalization
