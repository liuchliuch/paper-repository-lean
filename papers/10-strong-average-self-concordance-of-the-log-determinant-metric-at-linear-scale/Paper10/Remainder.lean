import Paper10.Basic
import Paper10.Spectral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Lemma 3.1 (Metric-change remainder)

If `A ∈ S^q`, `t > 0` and `t ‖A‖_op ≤ 1/2`, then
  `|F_t(A)| ≤ 2t |Tr(A³)| + 8t² Tr(A⁴)`
where `F_t(A) = Tr[A²((I + tA)^{-2} - I)]`.

The scalar identity behind the bound is, for `|y| ≤ 1/2`,
  `y²((1+y)^{-2} - 1) = -2y³ + y⁴ (3+2y)/(1+y)²`
with `0 ≤ (3+2y)/(1+y)² ≤ 8`.
-/

noncomputable section

open Matrix

namespace Paper10

variable {q : ℕ}

/-- Helper: `(1+y)^{-2} = ((1+y)^2)⁻¹` for real `y`. -/
theorem one_add_zpow_neg_two (y : ℝ) :
    (1 + y) ^ (-2 : ℤ) = ((1 + y) ^ 2)⁻¹ := by
  rw [_root_.zpow_neg, _root_.zpow_ofNat]

/-- Scalar remainder identity of Lemma 3.1. -/
theorem scalar_remainder_id (y : ℝ) (hy : |y| ≤ 1 / 2) :
    y ^ 2 * ((1 + y) ^ (-2 : ℤ) - 1)
      = -2 * y ^ 3 + y ^ 4 * (3 + 2 * y) / (1 + y) ^ 2 := by
  have hy1 : 0 < 1 + y := by
    have hlt : (-1 : ℝ) < y := by
      have h := abs_lt.mp (lt_of_le_of_lt hy (by norm_num : (1 / 2 : ℝ) < 1))
      linarith
    linarith
  have hsq : ((1 + y : ℝ) ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt hy1)
  have key : y ^ 2 * (((1 + y) ^ 2)⁻¹ - 1)
      = -2 * y ^ 3 + y ^ 4 * (3 + 2 * y) / (1 + y) ^ 2 := by
    field_simp [hsq]
    ring
  rw [one_add_zpow_neg_two]
  exact key

/-- Coefficient bound `0 ≤ (3+2y)/(1+y)² ≤ 8` for `|y| ≤ 1/2`. -/
theorem scalar_coeff_bound (y : ℝ) (hy : |y| ≤ 1 / 2) :
    0 ≤ (3 + 2 * y) / (1 + y) ^ 2 ∧ (3 + 2 * y) / (1 + y) ^ 2 ≤ 8 := by
  have hy1 : 0 < 1 + y := by
    have hlt : (-1 : ℝ) < y := by
      have h := abs_lt.mp (lt_of_le_of_lt hy (by norm_num : (1 / 2 : ℝ) < 1))
      linarith
    linarith
  have hsq : (0 : ℝ) < (1 + y) ^ 2 := sq_pos_of_ne_zero (ne_of_gt hy1)
  have hnum : (0 : ℝ) ≤ 3 + 2 * y := by
    have hge : (-(1 / 2 : ℝ)) ≤ y := (abs_le.mp hy).1
    linarith
  constructor
  · exact div_nonneg hnum (le_of_lt hsq)
  · rw [div_le_iff₀ hsq]
    have h2y : (0 : ℝ) ≤ 2 * y + 1 := by
      have hge : (-(1 / 2 : ℝ)) ≤ y := (abs_le.mp hy).1
      linarith
    have h4y : (0 : ℝ) ≤ 4 * y + 5 := by
      have hge : (-(1 / 2 : ℝ)) ≤ y := (abs_le.mp hy).1
      linarith
    have hfac : (8 : ℝ) * (1 + y) ^ 2 - (3 + 2 * y) = (2 * y + 1) * (4 * y + 5) := by ring
    nlinarith [mul_nonneg h2y h4y, hfac]

/-- The remainder function `F_t(A) = Tr[A²((I + tA)^{-2} - I)]` for a diagonalizable
symmetric matrix, expressed in its eigenvalues. -/
def Ft (t : ℝ) (A : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  Matrix.trace (A * A * ((1 : Matrix (Fin q) (Fin q) ℝ) + t • A) ^ (-2 : ℤ)
    - A * A)

theorem Ft_eq (t : ℝ) (A : Matrix (Fin q) (Fin q) ℝ) :
    Ft t A = Matrix.trace (A * A * ((1 : Matrix (Fin q) (Fin q) ℝ) + t • A) ^ (-2 : ℤ)
      - A * A) :=
  rfl

/-- Triangle inequality for real absolute value. -/
theorem abs_add_le (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_total 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    exact add_le_add (le_abs_self x) (le_abs_self y)
  · rw [abs_of_nonpos h]
    calc -(x + y) = (-x) + (-y) := by ring
      _ ≤ |x| + |y| := add_le_add (neg_le_abs x) (neg_le_abs y)

/-- Exact scalar form of Lemma 3.1 used by the probabilistic argument.
With `y = t μᵢ` and `|y| ≤ 1/2`,
`∑ μᵢ²((1+tμᵢ)^{-2}-1) = -2t ∑ μᵢ³ + t² ∑ μᵢ⁴ (3+2tμᵢ)/(1+tμᵢ)²`. -/
theorem lemma_3_1_scalar (t : ℝ) (μ : Fin q → ℝ)
    (ht : 0 < t) (hμ : ∀ i, |t * μ i| ≤ 1 / 2) :
    |∑ i, (μ i) ^ 2 * (((1 + t * μ i) ^ (-2 : ℤ)) - 1)|
      ≤ 2 * t * |∑ i, μ i ^ 3| + 8 * t ^ 2 * ∑ i, μ i ^ 4 := by
  -- Per-summand identity
  have hterm : ∀ i, (μ i) ^ 2 * (((1 + t * μ i) ^ (-2 : ℤ)) - 1)
      = -2 * t * (μ i) ^ 3
        + t ^ 2 * ((μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2) := by
    intro i
    have h := scalar_remainder_id (t * μ i) (hμ i)
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ht)
    have hne : (1 + t * μ i : ℝ) ≠ 0 := by
      have hlt : (-1 : ℝ) < t * μ i := by
        have := abs_lt.mp (lt_of_le_of_lt (hμ i) (by norm_num : (1 / 2 : ℝ) < 1))
        linarith
      linarith
    have hsq : ((1 + t * μ i : ℝ) ^ 2) ≠ 0 := pow_ne_zero 2 hne
    have hdiv : (μ i) ^ 2 * (((1 + t * μ i) ^ (-2 : ℤ)) - 1)
        = ((t * μ i) ^ 2 * (((1 + t * μ i) ^ (-2 : ℤ)) - 1)) / t ^ 2 := by
      field_simp [ht2]
    rw [hdiv, h]
    field_simp [ht2, hsq]
  -- Sum form
  have hsum : (∑ i, (μ i) ^ 2 * (((1 + t * μ i) ^ (-2 : ℤ)) - 1))
      = -2 * t * (∑ i, μ i ^ 3)
        + t ^ 2 * (∑ i, (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2) := by
    have hrewrite : (∑ i, (μ i) ^ 2 * (((1 + t * μ i) ^ (-2 : ℤ)) - 1))
        = ∑ i, (-2 * t * (μ i) ^ 3
          + t ^ 2 * ((μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2)) :=
      Finset.sum_congr rfl fun i _ => hterm i
    rw [hrewrite, Finset.sum_add_distrib]
    have hA : (∑ i, -2 * t * (μ i) ^ 3) = -2 * t * (∑ i, μ i ^ 3) := by
      rw [← Finset.mul_sum]
    have hB : (∑ i, t ^ 2 * ((μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2))
        = t ^ 2 * (∑ i, (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2) :=
      (Finset.mul_sum ..).symm
    rw [hA, hB]
  -- Coefficient bounds
  have hcoeff : ∀ i, 0 ≤ (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2
      ∧ (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2 ≤ 8 :=
    fun i => scalar_coeff_bound _ (hμ i)
  have hterm_assoc : ∀ i, (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2
      = (μ i) ^ 4 * ((3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2) := by
    intro i
    field_simp
  have hterm_nonneg : ∀ i,
      0 ≤ (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2 := by
    intro i
    have h4 : (0 : ℝ) ≤ (μ i) ^ 4 := by
      rw [show (4:ℕ) = 2 * 2 by norm_num, pow_mul]
      exact sq_nonneg _
    rw [hterm_assoc i]
    exact mul_nonneg h4 (hcoeff i).1
  have hrem_nonneg : 0 ≤ ∑ i, (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2 :=
    Finset.sum_nonneg fun i _ => hterm_nonneg i
  have hterm_le : ∀ i,
      (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2 ≤ 8 * (μ i) ^ 4 := by
    intro i
    have h4 : (0 : ℝ) ≤ (μ i) ^ 4 := by
      rw [show (4:ℕ) = 2 * 2 by norm_num, pow_mul]
      exact sq_nonneg _
    rw [hterm_assoc i, mul_comm 8]
    exact mul_le_mul_of_nonneg_left (hcoeff i).2 h4
  have hrem_le : ∑ i, (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2
      ≤ 8 * ∑ i, (μ i) ^ 4 :=
    calc ∑ i, (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2
        ≤ ∑ i, 8 * (μ i) ^ 4 := Finset.sum_le_sum fun i _ => hterm_le i
      _ = 8 * ∑ i, (μ i) ^ 4 := (Finset.mul_sum ..).symm
  -- Triangle inequality
  have habs : |∑ i, (μ i) ^ 2 * (((1 + t * μ i) ^ (-2 : ℤ)) - 1)|
      ≤ |(-2 * t : ℝ) * (∑ i, μ i ^ 3)|
        + |(t ^ 2 : ℝ) * (∑ i, (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2)| := by
    rw [hsum]
    exact abs_add_le _ _
  have h1 : |(-2 * t : ℝ) * (∑ i, μ i ^ 3)| = 2 * t * |∑ i, μ i ^ 3| := by
    have h2t : (0 : ℝ) ≤ 2 * t := by positivity
    have heq : ((-2 * t : ℝ) * (∑ i, μ i ^ 3)) = -(2 * t * ∑ i, μ i ^ 3) := by ring
    rw [heq, abs_neg, abs_mul, abs_of_nonneg h2t]
  have h2 : |(t ^ 2 : ℝ) * (∑ i, (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2)|
      = t ^ 2 * (∑ i, (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg t), abs_of_nonneg hrem_nonneg]
  have h3 : t ^ 2 * (∑ i, (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2)
      ≤ 8 * t ^ 2 * ∑ i, (μ i) ^ 4 := by
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    calc t ^ 2 * (∑ i, (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2)
        ≤ t ^ 2 * (8 * ∑ i, (μ i) ^ 4) := mul_le_mul_of_nonneg_left hrem_le ht2
      _ = 8 * t ^ 2 * ∑ i, (μ i) ^ 4 := by ring
  calc |∑ i, (μ i) ^ 2 * (((1 + t * μ i) ^ (-2 : ℤ)) - 1)|
      ≤ |(-2 * t : ℝ) * (∑ i, μ i ^ 3)|
        + |(t ^ 2 : ℝ) * (∑ i, (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2)| := habs
    _ = 2 * t * |∑ i, μ i ^ 3|
        + t ^ 2 * (∑ i, (μ i) ^ 4 * (3 + 2 * (t * μ i)) / (1 + t * μ i) ^ 2) := by rw [h1, h2]
    _ ≤ 2 * t * |∑ i, μ i ^ 3| + 8 * t ^ 2 * ∑ i, (μ i) ^ 4 := add_le_add_left h3 _

/-- Lemma 3.1 (17): the metric-change remainder bound, in the spectral (eigenvalue) form
used by the probabilistic argument. The eigenvalues `μᵢ` of `A` satisfy
`F_t(A) = ∑ᵢ μᵢ²((1+tμᵢ)^{-2}-1)`, and the bound is
`|F_t(A)| ≤ 2t |Tr(A³)| + 8t² Tr(A⁴)`. -/
theorem lemma_3_1 (t : ℝ) (μ : Fin q → ℝ)
    (ht : 0 < t) (hμ : ∀ i, |t * μ i| ≤ 1 / 2) :
    |∑ i, (μ i) ^ 2 * (((1 + t * μ i) ^ (-2 : ℤ)) - 1)|
      ≤ 2 * t * |∑ i, μ i ^ 3| + 8 * t ^ 2 * ∑ i, μ i ^ 4 :=
  lemma_3_1_scalar t μ ht hμ

/-- Coefficient identity used in the proof of Lemma 3.1:
`(3+2y)/(1+y)² = 2/(1+y) + 1/(1+y)²`. -/
theorem coeff_decomp (y : ℝ) (hy : y ≠ -1) :
    (3 + 2 * y) / (1 + y) ^ 2 = 2 / (1 + y) + 1 / (1 + y) ^ 2 := by
  have h1 : (1 + y) ≠ 0 := by
    intro hc
    apply hy
    linarith
  have h : (1 + y) ^ 2 ≠ 0 := pow_ne_zero 2 h1
  field_simp [h]
  ring

/-- The matrix remainder equals the scalar sum over the eigenvalues. -/
theorem Ft_spectral (t : ℝ) (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.IsSymm)
    (hμ : ∀ i, |t * (real_isHermitian hA).eigenvalues i| ≤ 1 / 2) :
    Ft t A = ∑ i, ((real_isHermitian hA).eigenvalues i) ^ 2 *
      ((1 + t * (real_isHermitian hA).eigenvalues i) ^ (-2 : ℤ) - 1) := by
  let U := (real_isHermitian hA).eigenvectorUnitary
  let μ := (real_isHermitian hA).eigenvalues
  have hAD : A = (U : Matrix _ _ ℝ) * Matrix.diagonal μ * (U : Matrix _ _ ℝ)ᴴ :=
    real_spectral_theorem A hA
  have hshift : 1 + t • A = (U : Matrix _ _ ℝ) *
      Matrix.diagonal (fun i => 1 + t * μ i) * (U : Matrix _ _ ℝ)ᴴ := by
    rw [orthogonal_conj_one_add_smul, ← hAD]
  have hd : ∀ i, 1 + t * μ i ≠ 0 := by
    intro i
    have hh := (abs_le.mp (hμ i)).1
    dsimp [μ]
    linarith
  have hi : (1 + t • A)⁻¹ = (U : Matrix _ _ ℝ) *
      Matrix.diagonal (fun i => (1 + t * μ i)⁻¹) * (U : Matrix _ _ ℝ)ᴴ := by
    rw [hshift, orthogonal_conj_diagonal_inv U _ hd]
  have hp : (1 + t • A) ^ (-2 : ℤ) = (U : Matrix _ _ ℝ) *
      Matrix.diagonal (fun i => (1 + t * μ i) ^ (-2 : ℤ)) * (U : Matrix _ _ ℝ)ᴴ := by
    rw [show (-2 : ℤ) = -(2 : ℕ) by norm_num, Matrix.zpow_neg_natCast, ← Matrix.inv_pow', hi,
      pow_two, orthogonal_conj_mul, Matrix.diagonal_mul_diagonal]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      norm_num
      field_simp [hd i]
      <;> ring
    · simp only [Matrix.diagonal_apply_ne _ hij]
  have hAA : A * A = (U : Matrix _ _ ℝ) *
      Matrix.diagonal (fun i => μ i ^ 2) * (U : Matrix _ _ ℝ)ᴴ := by
    calc
      A * A = ((U : Matrix _ _ ℝ) * Matrix.diagonal μ * (U : Matrix _ _ ℝ)ᴴ) *
          ((U : Matrix _ _ ℝ) * Matrix.diagonal μ * (U : Matrix _ _ ℝ)ᴴ) := congrArg₂ (· * ·) hAD hAD
      _ = _ := by rw [orthogonal_conj_mul, Matrix.diagonal_mul_diagonal]; simp [pow_two]
  unfold Ft
  rw [hp, hAA, orthogonal_conj_mul, Matrix.trace_sub,
    trace_orthogonal_conj, trace_orthogonal_conj, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Matrix.trace_diagonal, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Lemma 3.1 for the actual matrix remainder and actual matrix trace powers. -/
theorem lemma_3_1_matrix (t : ℝ) (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.IsSymm)
    (ht : 0 < t) (hμ : ∀ i, |t * (real_isHermitian hA).eigenvalues i| ≤ 1 / 2) :
    |Ft t A| ≤ 2 * t * |Matrix.trace (A ^ 3)| + 8 * t ^ 2 * Matrix.trace (A ^ 4) := by
  rw [Ft_spectral t A hA hμ, trace_pow_spectral A hA 3, trace_pow_spectral A hA 4]
  exact lemma_3_1_scalar t _ ht hμ

end Paper10
