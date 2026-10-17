import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

/-!
# The matrix Stein mobility in Lemma 4.1

This file uses the usual real dot product and the Frobenius product
`trace (Aᵀ * B)`. All matrix products and inverses are mathlib matrix operations.
The algebraic results do not assert the analytic Gaussian differentiation formula
(4.2); the gradient supplied in the final algebraic substitution is explicit.
-/
namespace Paper38.Mobility

set_option linter.unusedSectionVars false

open Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

abbrev Vec (d : Type*) := d → ℝ
abbrev Mat (d : Type*) := Matrix d d ℝ

/-- The ordinary Frobenius product of two real matrices. -/
def frobenius (A B : Mat d) : ℝ := Matrix.trace (Aᵀ * B)

/-- The product pairing on vectors and symmetric matrices, as in Section 4. -/
def pairing (a : Vec d) (B : Mat d) (u : Vec d) (H : Mat d) : ℝ :=
  a ⬝ᵥ u + frobenius B H

/-- The matrix appearing on the right side of (4.6). -/
def feature (μ : Vec d) (S : Mat d) (a : Vec d) (B : Mat d) : Mat d :=
  (2 : ℝ) • (B * S) + Matrix.vecMulVec a μ

/-- The vector component (4.3a), in its displayed source form. -/
def mobilityMean (μ : Vec d) (S : Mat d) (a : Vec d) (B : Mat d) : Vec d :=
  (2 : ℝ) • ((B * S) *ᵥ μ) + (1 + μ ⬝ᵥ μ) • a

/-- The matrix component (4.3b), in its displayed source form. -/
def mobilityCov (μ : Vec d) (S : Mat d) (a : Vec d) (B : Mat d) : Mat d :=
  S * ((2 : ℝ) • (S * B) + Matrix.vecMulVec μ a) +
    ((2 : ℝ) • (B * S) + Matrix.vecMulVec a μ) * S

@[simp] theorem frobenius_add_left (A B C : Mat d) :
    frobenius (A + B) C = frobenius A C + frobenius B C := by
  simp [frobenius, Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add]

@[simp] theorem frobenius_add_right (A B C : Mat d) :
    frobenius A (B + C) = frobenius A B + frobenius A C := by
  simp [frobenius, Matrix.mul_add, Matrix.trace_add]

@[simp] theorem frobenius_smul_left (r : ℝ) (A B : Mat d) :
    frobenius (r • A) B = r * frobenius A B := by
  simp [frobenius, Matrix.transpose_smul, Matrix.trace_smul]

@[simp] theorem frobenius_smul_right (r : ℝ) (A B : Mat d) :
    frobenius A (r • B) = r * frobenius A B := by
  simp [frobenius, Matrix.trace_smul]

theorem frobenius_comm (A B : Mat d) : frobenius A B = frobenius B A := by
  unfold frobenius
  rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem frobenius_mul_right (A B C : Mat d) :
    frobenius A (B * C) = frobenius (A * Cᵀ) B := by
  unfold frobenius
  rw [Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.trace_mul_cycle', ← Matrix.mul_assoc]

theorem frobenius_mul_left (A B C : Mat d) :
    frobenius A (B * C) = frobenius (Bᵀ * A) C := by
  simp [frobenius, Matrix.transpose_mul, Matrix.mul_assoc]

theorem frobenius_transpose_right (A B : Mat d) :
    frobenius A Bᵀ = frobenius Aᵀ B := by
  simp [frobenius]

theorem frobenius_vecMulVec (a μ : Vec d) (L : Mat d) :
    frobenius (Matrix.vecMulVec a μ) L = a ⬝ᵥ (L *ᵥ μ) := by
  simp only [frobenius, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem mobilityMean_feature (μ : Vec d) (S : Mat d) (a : Vec d) (B : Mat d) :
    mobilityMean μ S a B = feature μ S a B *ᵥ μ + a := by
  simp only [mobilityMean, feature, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_smul]
  ring

theorem feature_transpose (μ : Vec d) (S B : Mat d) (a : Vec d)
    (hS : Sᵀ = S) (hB : Bᵀ = B) :
    (feature μ S a B)ᵀ = (2 : ℝ) • (S * B) + Matrix.vecMulVec μ a := by
  simp [feature, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_smul, Matrix.transpose_vecMulVec, hS, hB]

theorem mobilityCov_feature (μ : Vec d) (S : Mat d) (a : Vec d) (B : Mat d)
    (hS : Sᵀ = S) (hB : Bᵀ = B) :
    mobilityCov μ S a B = S * (feature μ S a B)ᵀ + feature μ S a B * S := by
  rw [feature_transpose μ S B a hS hB]
  rfl

/-- The bilinear sum-of-squares factorization (4.6), for the genuine mobility (4.3). -/
theorem bilinear_identity (μ : Vec d) (S : Mat d) (a a' : Vec d) (B B' : Mat d)
    (hS : Sᵀ = S) (hB : Bᵀ = B) (hB' : B'ᵀ = B') :
    pairing a B (mobilityMean μ S a' B') (mobilityCov μ S a' B') =
      frobenius (feature μ S a B) (feature μ S a' B') + a ⬝ᵥ a' := by
  rw [pairing, mobilityMean_feature, mobilityCov_feature μ S a' B' hS hB']
  rw [dotProduct_add, frobenius_add_right, frobenius_mul_left,
    frobenius_transpose_right, Matrix.transpose_mul, Matrix.transpose_transpose,
    frobenius_mul_right, hS, hB]
  simp only [feature, frobenius_add_left, frobenius_smul_left,
    frobenius_vecMulVec]
  ring

/-- On symmetric matrices, our Frobenius definition is exactly `trace (B * H)`. -/
theorem pairing_source (a u : Vec d) (B H : Mat d) (hB : Bᵀ = B) :
    pairing a B u H = a ⬝ᵥ u + Matrix.trace (B * H) := by
  simp [pairing, frobenius, hB]

/-- Self-adjointness follows from the genuine bilinear identity. -/
theorem self_adjoint (μ : Vec d) (S : Mat d) (a a' : Vec d) (B B' : Mat d)
    (hS : Sᵀ = S) (hB : Bᵀ = B) (hB' : B'ᵀ = B') :
    pairing a B (mobilityMean μ S a' B') (mobilityCov μ S a' B') =
      pairing a' B' (mobilityMean μ S a B) (mobilityCov μ S a B) := by
  rw [bilinear_identity μ S a a' B B' hS hB hB',
    bilinear_identity μ S a' a B' B hS hB' hB,
    frobenius_comm (feature μ S a B), dotProduct_comm a a']

/-- The sum-of-squares identity (4.4). -/
theorem quadratic_identity (μ : Vec d) (S : Mat d) (a : Vec d) (B : Mat d)
    (hS : Sᵀ = S) (hB : Bᵀ = B) :
    pairing a B (mobilityMean μ S a B) (mobilityCov μ S a B) =
      frobenius (feature μ S a B) (feature μ S a B) + a ⬝ᵥ a :=
  bilinear_identity μ S a a B B hS hB hB

/-- The Frobenius square is the ordinary sum of squared matrix entries. -/
theorem frobenius_self_eq_sum (A : Mat d) :
    frobenius A A = ∑ i, ∑ j, (A i j) ^ 2 := by
  simp only [frobenius, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [pow_two]

theorem frobenius_self_nonneg (A : Mat d) : 0 ≤ frobenius A A := by
  rw [frobenius_self_eq_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

@[simp] theorem frobenius_self_eq_zero (A : Mat d) : frobenius A A = 0 ↔ A = 0 := by
  simpa only [frobenius, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.trace_conjTranspose_mul_self_eq_zero_iff (A := A))

theorem vector_self_nonneg (a : Vec d) : 0 ≤ a ⬝ᵥ a :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)

/-- Positive semidefiniteness, needing only symmetry of the covariance. -/
theorem quadratic_nonneg (μ : Vec d) (S : Mat d) (a : Vec d) (B : Mat d)
    (hS : Sᵀ = S) (hB : Bᵀ = B) :
    0 ≤ pairing a B (mobilityMean μ S a B) (mobilityCov μ S a B) := by
  rw [quadratic_identity μ S a B hS hB]
  exact add_nonneg (frobenius_self_nonneg _) (vector_self_nonneg _)

/-- The exact null space is trivial when the covariance is positive definite. -/
theorem quadratic_eq_zero_iff (μ : Vec d) (S : Mat d) (a : Vec d) (B : Mat d)
    (hS : S.PosDef) (hB : Bᵀ = B) :
    pairing a B (mobilityMean μ S a B) (mobilityCov μ S a B) = 0 ↔
      a = 0 ∧ B = 0 := by
  have hs : Sᵀ = S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
  rw [quadratic_identity μ S a B hs hB]
  constructor
  · intro h
    have hF := frobenius_self_nonneg (feature μ S a B)
    have haN := vector_self_nonneg a
    have ha : a = 0 := dotProduct_self_eq_zero.mp (by linarith)
    have hf : feature μ S a B = 0 := (frobenius_self_eq_zero _).mp (by linarith)
    have hm : B * S = 0 := by
      rw [feature, ha, Matrix.zero_vecMulVec, add_zero] at hf
      ext i j
      change (B * S) i j = 0
      have hij := congrFun (congrFun hf i) j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hij
      linarith
    have hd : IsUnit S.det := isUnit_iff_ne_zero.mpr (ne_of_gt hS.det_pos)
    have hb : B = 0 := by
      calc
        B = B * S * S⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
        _ = 0 := by rw [hm, Matrix.zero_mul]
    exact ⟨ha, hb⟩
  · rintro ⟨rfl, rfl⟩
    simp [feature, frobenius]

/-- Strict positive definiteness on the vector/symmetric-matrix tangent space. -/
theorem quadratic_pos (μ : Vec d) (S : Mat d) (a : Vec d) (B : Mat d)
    (hS : S.PosDef) (hB : Bᵀ = B) (hne : a ≠ 0 ∨ B ≠ 0) :
    0 < pairing a B (mobilityMean μ S a B) (mobilityCov μ S a B) := by
  have hs : Sᵀ = S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
  refine lt_of_le_of_ne (quadratic_nonneg μ S a B hs hB) ?_
  intro he
  have hz := (quadratic_eq_zero_iff μ S a B hS hB).mp he.symm
  exact hne.elim (fun h => h hz.1) (fun h => h hz.2)

/-- The covariance output is again a symmetric tangent matrix. -/
theorem mobilityCov_symmetric (μ : Vec d) (S : Mat d) (a : Vec d) (B : Mat d)
    (hS : Sᵀ = S) (hB : Bᵀ = B) :
    (mobilityCov μ S a B)ᵀ = mobilityCov μ S a B := by
  rw [mobilityCov_feature μ S a B hS hB]
  simp [Matrix.transpose_add, Matrix.transpose_mul, hS, add_comm]

/-- Additivity of the vector component in its tangent/cotangent argument. -/
theorem mobilityMean_add (μ : Vec d) (S : Mat d) (a a' : Vec d) (B B' : Mat d) :
    mobilityMean μ S (a + a') (B + B') =
      mobilityMean μ S a B + mobilityMean μ S a' B' := by
  simp only [mobilityMean, Matrix.add_mul, Matrix.add_mulVec, smul_add]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Additivity of the matrix component in its tangent/cotangent argument. -/
theorem mobilityCov_add (μ : Vec d) (S : Mat d) (a a' : Vec d) (B B' : Mat d) :
    mobilityCov μ S (a + a') (B + B') =
      mobilityCov μ S a B + mobilityCov μ S a' B' := by
  simp only [mobilityCov, Matrix.add_mul, Matrix.mul_add, smul_add,
    Matrix.add_vecMulVec, Matrix.vecMulVec_add]
  noncomm_ring

/-- Homogeneity of the vector component. -/
theorem mobilityMean_smul (μ : Vec d) (S : Mat d) (r : ℝ) (a : Vec d) (B : Mat d) :
    mobilityMean μ S (r • a) (r • B) = r • mobilityMean μ S a B := by
  simp only [mobilityMean, Matrix.smul_mul, Matrix.smul_mulVec, smul_add, smul_smul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Homogeneity of the matrix component. -/
theorem mobilityCov_smul (μ : Vec d) (S : Mat d) (r : ℝ) (a : Vec d) (B : Mat d) :
    mobilityCov μ S (r • a) (r • B) = r • mobilityCov μ S a B := by
  have hl : (2 : ℝ) • (S * (r • B)) + Matrix.vecMulVec μ (r • a) =
      r • ((2 : ℝ) • (S * B) + Matrix.vecMulVec μ a) := by
    simp only [Matrix.mul_smul, Matrix.vecMulVec_smul, smul_add, smul_smul,
      mul_comm (2 : ℝ) r]
  have hr : (2 : ℝ) • ((r • B) * S) + Matrix.vecMulVec (r • a) μ =
      r • ((2 : ℝ) • (B * S) + Matrix.vecMulVec a μ) := by
    simp only [Matrix.smul_mul, Matrix.smul_vecMulVec, smul_add, smul_smul,
      mul_comm (2 : ℝ) r]
  unfold mobilityCov
  rw [hl, hr, Matrix.mul_smul, Matrix.smul_mul, smul_add]

/-- The covariance part of the energy gradient from (4.2), considered algebraically. -/
noncomputable def energyCovGradient (S Γ : Mat d) : Mat d :=
  (1 / 2 : ℝ) • (Γ - S⁻¹)

/-- The actual moment vector field (2.3a). -/
def momentMean (μ m : Vec d) (S Γ : Mat d) : Vec d :=
  (1 - Γ * S) *ᵥ μ - (1 + μ ⬝ᵥ μ) • m

/-- The actual moment vector field (2.3b). -/
def momentCov (μ m : Vec d) (S Γ : Mat d) : Mat d :=
  (2 : ℝ) • S - S * (S * Γ + Matrix.vecMulVec μ m) -
    (Γ * S + Matrix.vecMulVec m μ) * S

private theorem twice_gradient_mul (S Γ : Mat d) (hS : S.PosDef) :
    (2 : ℝ) • (energyCovGradient S Γ * S) = Γ * S - 1 := by
  have hd : IsUnit S.det := isUnit_iff_ne_zero.mpr (ne_of_gt hS.det_pos)
  simp only [energyCovGradient, Matrix.smul_mul, smul_smul]
  norm_num
  rw [Matrix.sub_mul, Matrix.nonsing_inv_mul _ hd]

private theorem twice_mul_gradient (S Γ : Mat d) (hS : S.PosDef) :
    (2 : ℝ) • (S * energyCovGradient S Γ) = S * Γ - 1 := by
  have hd : IsUnit S.det := isUnit_iff_ne_zero.mpr (ne_of_gt hS.det_pos)
  simp only [energyCovGradient, Matrix.mul_smul, smul_smul]
  norm_num
  rw [Matrix.mul_sub, Matrix.mul_nonsing_inv _ hd]

/-- The vector component of (4.5), with the exact formula (4.2) substituted. -/
theorem momentMean_eq_neg_mobility (μ m : Vec d) (S Γ : Mat d) (hS : S.PosDef) :
    momentMean μ m S Γ = -mobilityMean μ S m (energyCovGradient S Γ) := by
  simp only [momentMean, mobilityMean, ← Matrix.smul_mulVec,
    twice_gradient_mul S Γ hS, Matrix.sub_mulVec, Matrix.one_mulVec]
  ext i
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply]
  ring

/-- The covariance component of (4.5), with the exact formula (4.2) substituted. -/
theorem momentCov_eq_neg_mobility (μ m : Vec d) (S Γ : Mat d) (hS : S.PosDef) :
    momentCov μ m S Γ = -mobilityCov μ S m (energyCovGradient S Γ) := by
  simp only [momentCov, mobilityCov, twice_gradient_mul S Γ hS,
    twice_mul_gradient S Γ hS, two_smul ℝ S]
  noncomm_ring

/-- The algebraic moment-gradient-flow identity (4.5). The analytic assertion that
these entries are the derivative of the Gaussian reverse-KL energy is separate. -/
theorem moment_eq_neg_mobility (μ m : Vec d) (S Γ : Mat d) (hS : S.PosDef) :
    (momentMean μ m S Γ, momentCov μ m S Γ) =
      (-mobilityMean μ S m (energyCovGradient S Γ),
        -mobilityCov μ S m (energyCovGradient S Γ)) := by
  rw [momentMean_eq_neg_mobility μ m S Γ hS,
    momentCov_eq_neg_mobility μ m S Γ hS]

end Paper38.Mobility
