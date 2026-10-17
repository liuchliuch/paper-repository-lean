import Paper10.Basic
import Paper10.Symm
import Paper10.Gaussian
import Paper10.PairedTraces
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Appendix A: auxiliary Gaussian calculations

## A.1 Polynomial Gaussian Poincaré inequality
`Var f(ξ) ≤ E ‖∇f(ξ)‖²` for polynomials `f` and standard Gaussian `ξ`.

## A.2 Exact isotropic trace moments
For identity covariance `W` in `S^q`,
  `E Tr(W⁴) = q(2q²+5q+5)/4`,
  `E (Tr(W³))² = 3q(4q²+9q+7)/4`.
-/

noncomputable section

open Matrix MeasureTheory ProbabilityTheory Real

namespace Paper10

variable {q : ℕ}

/-! ## A.2 Exact isotropic moments as polynomial identities -/

/-- A.2: the closed form `q(2q²+5q+5)/4` agrees with the appendix expression
`q(q+1)²/2 + (n+q)/2`. -/
theorem iso_quartic_formula (q : ℕ) :
    (q : ℝ) * (2 * (q : ℝ) ^ 2 + 5 * (q : ℝ) + 5) / 4
      = (q : ℝ) * (q + 1) ^ 2 / 2 + (((n q : ℕ) : ℝ) + q) / 2 := by
  have h1 : ((n q : ℕ) : ℝ) = (q : ℝ) * ((q + 1 : ℕ) : ℝ) / 2 := by
    rw [n_mul_c, c_eq]
    field_simp
  rw [h1]
  push_cast
  field_simp
  ring

/-- The real polynomial formula for choosing two indices. -/
theorem choose_two_cast (q : ℕ) :
    (Nat.choose q 2 : ℝ) = (q : ℝ) * ((q : ℝ) - 1) / 2 := by
  induction q with
  | zero => norm_num
  | succ q ih =>
    rw [Nat.choose_succ_succ, Nat.cast_add, ih]
    simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
    ring

/-- The binomial coefficient `C(q,3)` as a real polynomial, valid also at small orders. -/
theorem choose_three_cast (q : ℕ) :
    (Nat.choose q 3 : ℝ) = (q : ℝ) * ((q : ℝ) - 1) * ((q : ℝ) - 2) / 6 := by
  induction q with
  | zero => norm_num
  | succ q ih =>
    rw [Nat.choose_succ_succ, Nat.cast_add, ih, choose_two_cast]
    push_cast
    ring

/-- A.2: the closed form `3q(4q²+9q+7)/4` agrees with the appendix expression
`6q + 9q((q+1)²/4 + (q-1)/2) + (36/8) C(q,3)`. -/
theorem iso_cubic_sq_formula (q : ℕ) :
    3 * (q : ℝ) * (4 * (q : ℝ) ^ 2 + 9 * (q : ℝ) + 7) / 4
      = 6 * (q : ℝ) + 9 * (q : ℝ) * ((q + 1) ^ 2 / 4 + ((q : ℝ) - 1) / 2)
          + (36 / 8) * (Nat.choose q 3 : ℝ) := by
  rw [choose_three_cast]
  field_simp
  ring

/-! ## A.2 Convexity of the quartic trace -/

/-- Convexity of `A ↦ Tr(A⁴)` on symmetric matrices (A.2).
We show `8 Tr(A²H²) + 4 Tr(AHAH) ≥ 4 Tr(A²H²)`, i.e. `Tr(A²H²) + Tr(AHAH) ≥ 0`,
using `|Tr(AHAH)| ≤ Tr(A²H²)`. -/
theorem tr_four_convex {A H : Matrix (Fin q) (Fin q) ℝ}
    (hA : A.IsSymm) (hH : H.IsSymm) :
    8 * Matrix.trace (A * A * H * H) + 4 * Matrix.trace (A * H * A * H)
      ≥ 4 * Matrix.trace (A * A * H * H) := by
  have hcs := frob_cs_UVUV (q := q) (U := A) (V := H) hA hH
  have hbound : -(Matrix.trace (A * A * H * H)) ≤ Matrix.trace (A * H * A * H) := by
    have h1 : -|Matrix.trace (A * H * A * H)| ≤ Matrix.trace (A * H * A * H) :=
      neg_abs_le _
    have h2 : |Matrix.trace (A * H * A * H)| ≤ Matrix.trace (A * A * H * H) := hcs
    linarith
  linarith

/-- Tr(A²H²) = ‖A H‖_F² ≥ 0 for symmetric `A, H`. -/
theorem trace_A2H2_nonneg {A H : Matrix (Fin q) (Fin q) ℝ}
    (hA : A.IsSymm) (hH : H.IsSymm) :
    0 ≤ Matrix.trace (A * A * H * H) := by
  have h1 : (A * H)ᵀ = H * A := by
    rw [Matrix.transpose_mul, hA.eq, hH.eq]
  have hpsd : ((A * H)ᵀ * (A * H)).PosSemidef :=
    posSemidef_conjTranspose_mul_self (R := ℝ) (A * H)
  have h4 : 0 ≤ Matrix.trace ((A * H)ᵀ * (A * H)) := hpsd.trace_nonneg
  have hL : ((A * H)ᵀ * (A * H)).trace = Matrix.trace (H * A * A * H) := by
    rw [h1]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  have hM : Matrix.trace (H * A * A * H) = Matrix.trace (A * A * H * H) := by
    have e1 : H * A * A * H = (H * A * A) * H := by rw [Matrix.mul_assoc]
    rw [e1, Matrix.trace_mul_comm]
    -- Tr(H * (H * A * A)) = Tr((H * H) * (A * A))
    have e2 : H * (H * A * A) = (H * H) * (A * A) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [e2, Matrix.trace_mul_comm]
    have e3 : (A * A) * (H * H) = A * A * H * H := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [e3]
  rw [hL, hM] at h4
  exact h4

/-- The last step of convexity: `4 Tr(A²H²) ≥ 0`. -/
theorem tr_four_convex_nonneg {A H : Matrix (Fin q) (Fin q) ℝ}
    (hA : A.IsSymm) (hH : H.IsSymm) :
    4 * Matrix.trace (A * A * H * H) ≥ 0 :=
  mul_nonneg (by norm_num) (trace_A2H2_nonneg hA hH)

/-! ## A.1 Polynomial Gaussian Poincaré inequality -/

/-- A.1 special case: for a single standard Gaussian,
`Var(ξ³) ≤ E[(d/dξ ξ³)²]`, i.e. `Var(ξ³) ≤ 9 E[ξ⁴]`. -/
theorem poincare_cube_std :
    Var[fun x : ℝ => x ^ 3; gaussianReal 0 1]
      ≤ ∫ x, (3 * x ^ 2 : ℝ) ^ 2 ∂gaussianReal 0 1 := by
  rw [variance_of_integral_eq_zero (by fun_prop) gauss_int_cube]
  have h6 : (fun x : ℝ => (x ^ 3) ^ 2) = fun x => x ^ 6 := by ext x; ring
  rw [h6, gauss_int_sixth]
  have hr : (∫ x : ℝ, (3 * x ^ 2) ^ 2 ∂gaussianReal 0 1) = 27 := by
    have he : (fun x : ℝ => (3 * x ^ 2) ^ 2) = fun x => 9 * x ^ 4 := by ext x; ring
    rw [he, integral_const_mul, gauss_int_fourth]
    norm_num
  rw [hr]
  norm_num

/-- Exact isotropic fourth moment (16), as an equality of actual Gaussian integrals. -/
theorem iso_quartic {m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) :
    (∫ ω, Matrix.trace (gaussianMatrix F ω ^ 4) ∂stdGaussianMeasure m) =
      (q : ℝ) * (2 * (q : ℝ) ^ 2 + 5 * (q : ℝ) + 5) / 4 := by
  rw [fourth_moment_expansion, sum_squares_orthonormal F hF]
  have halt : (∑ a, ∑ b, Matrix.trace (F a * F b * F a * F b)) =
      ((n q : ℝ) + q) / 2 := by
    have hrow : ∀ a, (∑ b, Matrix.trace (F a * F b * F a * F b)) =
        (Matrix.trace (F a * F a) + (Matrix.trace (F a)) ^ 2) / 2 := by
      intro a
      calc
        _ = Matrix.trace ((∑ b, F b * F a * F b) * F a) := by
          rw [Matrix.sum_mul, Matrix.trace_sum]
          apply Finset.sum_congr rfl
          intro b _
          rw [Matrix.trace_mul_cycle]
          simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [sum_FUF F hF (F a)]
          simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_smul,
            Matrix.trace_add, smul_eq_mul]
          rw [show (F a)ᵀ = F a from hF.1 a]
          ring
    simp_rw [hrow]
    simp only [div_eq_mul_inv, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [parseval_trace_one F hF, parseval_trace_sq F hF]
  rw [halt, iso_quartic_formula]
  simp only [oneMat, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  simp only [c, Nat.cast_add, Nat.cast_one]
  ring

/- The general polynomial Poincaré theorem is proved in Poincare.lean, the exact cubic
   integral in ExactCubic.lean, convexity in QuarticConvex.lean, and the actual quartic
   covariance maximum in QuarticMaximum.lean. These modules are all on the root import path. -/

end Paper10
