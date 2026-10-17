import Paper29.Defs
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Weighted leverage mass and exact scalar changes of weights

These are the finite matrix identities used in Lemmas 3.2 and 3.3 and Appendix
A.1/A.2. Invertibility is derived from full column rank and positive weights;
it is not an additional premise of the full-rank results.
-/
noncomputable section
open scoped BigOperators Matrix

namespace Paper29.Leverage

/-- The weighted column Gram matrix. -/
def gram {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := Aᵀ * Matrix.diagonal w * A

/-- The squared row radius `aᵢᵀ (Aᵀ diag(w) A)⁻¹ aᵢ`. -/
def radiusSq {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (i : Fin n) : ℝ := A i ⬝ᵥ (gram A w)⁻¹.mulVec (A i)

/-- The nonnegative row radius used by the weight schemes. -/
def radius {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (i : Fin n) : ℝ := Real.sqrt (radiusSq A w i)

def leverage {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (i : Fin n) : ℝ := w i * radiusSq A w i

/-- Full column rank in the dimension formulation implies actual injectivity. -/
theorem mulVec_injective_of_rank_eq {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : A.rank = d) : Function.Injective A.mulVec := by
  have hd := A.mulVecLin.finrank_range_add_finrank_ker
  change A.rank + Module.finrank ℝ (LinearMap.ker A.mulVecLin) =
    Module.finrank ℝ (Fin d → ℝ) at hd
  rw [hA] at hd
  have hdim : Module.finrank ℝ (Fin d → ℝ) = d := by simp
  rw [hdim] at hd
  have hk : Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

/-- The positive diagonal form stays positive definite after pullback by an
injective matrix. This proves the required Gram invertibility from the data. -/
theorem gram_posDef {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) :
    (gram A w).PosDef := by
  have h := (Matrix.PosDef.diagonal hw).conjTranspose_mul_mul_same (B := A) hA
  simpa [gram] using h

theorem gram_isUnit {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) : IsUnit (gram A w) :=
  (gram_posDef A w hA hw).isUnit

theorem gram_det_isUnit {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) : IsUnit (gram A w).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (gram_isUnit A w hA hw)

theorem gram_mul_inv {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) :
    gram A w * (gram A w)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (gram_det_isUnit A w hA hw)

theorem gram_inv_mul {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) :
    (gram A w)⁻¹ * gram A w = 1 :=
  Matrix.nonsing_inv_mul _ (gram_det_isUnit A w hA hw)

theorem radiusSq_nonneg {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) (i : Fin n) :
    0 ≤ radiusSq A w i := by
  have h := (gram_posDef A w hA hw).inv.posSemidef.2 (A i)
  simpa [radiusSq] using h

theorem radiusSq_pos {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) (i : Fin n)
    (hi : A i ≠ 0) : 0 < radiusSq A w i := by
  have h := (gram_posDef A w hA hw).inv.2 (A i) hi
  simpa [radiusSq] using h

theorem radius_sq {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) (i : Fin n) :
    radius A w i ^ 2 = radiusSq A w i :=
  Real.sq_sqrt (radiusSq_nonneg A w hA hw i)

/-- The row quadratic form is the corresponding diagonal of the hat matrix. -/
theorem radiusSq_eq_diagonal {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w : Fin n → ℝ) (i : Fin n) :
    radiusSq A w i = (A * (gram A w)⁻¹ * Aᵀ) i i := by
  unfold radiusSq
  simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The trace identity, before applying inverse cancellation. -/
theorem leverage_sum_eq_trace {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w : Fin n → ℝ) :
    (∑ i, leverage A w i) = Matrix.trace (gram A w * (gram A w)⁻¹) := by
  calc
    (∑ i, leverage A w i) =
        Matrix.trace ((Matrix.diagonal w * A) * (gram A w)⁻¹ * Aᵀ) := by
      simp only [leverage, radiusSq_eq_diagonal, Matrix.trace]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Matrix.mul_assoc, Matrix.diagonal_mul]
    _ = Matrix.trace (Aᵀ * (Matrix.diagonal w * A) * (gram A w)⁻¹) :=
      Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (gram A w * (gram A w)⁻¹) := by simp only [gram, Matrix.mul_assoc]

/-- The exact mass `∑ᵢ wᵢ vᵢ² = d`, derived from actual full column rank. -/
theorem leverage_sum {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) :
    (∑ i, leverage A w i) = (d : ℝ) := by
  rw [leverage_sum_eq_trace, gram_mul_inv A w hA hw]
  simp

theorem weighted_radius_sq_sum {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w : Fin n → ℝ) (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) :
    (∑ i, w i * radius A w i ^ 2) = (d : ℝ) := by
  simp only [radius_sq A w hA hw]
  exact leverage_sum A w hA hw

theorem leverage_sum_of_rank_eq {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w : Fin n → ℝ) (hA : A.rank = d) (hw : ∀ i, 0 < w i) :
    (∑ i, leverage A w i) = (d : ℝ) :=
  leverage_sum A w (mulVec_injective_of_rank_eq A hA) hw

/-- The source trace mass stated directly using the nonnegative row radii
and the rank formulation of full column rank. -/
theorem weighted_radius_sq_sum_of_rank_eq {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : A.rank = d) (hw : ∀ i, 0 < w i) :
    (∑ i, w i * radius A w i ^ 2) = (d : ℝ) :=
  weighted_radius_sq_sum A w (mulVec_injective_of_rank_eq A hA) hw

/-- Invertibility of the actual weighted Gram from column rank and weight
positivity alone. -/
theorem gram_isUnit_of_rank_eq {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w : Fin n → ℝ) (hA : A.rank = d) (hw : ∀ i, 0 < w i) : IsUnit (gram A w) :=
  gram_isUnit A w (mulVec_injective_of_rank_eq A hA) hw

/-- Scalar changes of row weights scale the Gram matrix exactly. -/
theorem gram_rescale {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (c : ℝ) : gram A (fun i => c * w i) = c • gram A w := by
  have hd : Matrix.diagonal (fun i => c * w i) = c • Matrix.diagonal w := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  simp only [gram, hd, Matrix.mul_smul, Matrix.smul_mul]

/-- The inverse Gram scales by the reciprocal scalar, with its invertibility
proved from full column rank and positive original weights. -/
theorem gram_inv_rescale {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) (c : ℝ) (hc : c ≠ 0) :
    (gram A (fun i => c * w i))⁻¹ = c⁻¹ • (gram A w)⁻¹ := by
  rw [gram_rescale]
  apply Matrix.inv_eq_left_inv
  simp [smul_smul, hc, gram_inv_mul A w hA hw]

theorem radiusSq_rescale {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) (c : ℝ) (hc : c ≠ 0)
    (i : Fin n) : radiusSq A (fun j => c * w j) i = c⁻¹ * radiusSq A w i := by
  simp [radiusSq, gram_inv_rescale A w hA hw c hc, Matrix.smul_mulVec, dotProduct_smul]

theorem radius_rescale {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) (c : ℝ) (hc : 0 < c)
    (i : Fin n) : radius A (fun j => c * w j) i = Real.sqrt c⁻¹ * radius A w i := by
  simp only [radius, radiusSq_rescale A w hA hw c (ne_of_gt hc),
    Real.sqrt_mul (inv_nonneg.mpr hc.le)]

/-- Row leverage scores are invariant under positive scalar changes of all weights. -/
theorem leverage_rescale {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) (c : ℝ) (hc : c ≠ 0)
    (i : Fin n) : leverage A (fun j => c * w j) i = leverage A w i := by
  rw [leverage, radiusSq_rescale A w hA hw c hc]
  unfold leverage
  field_simp

/-- The exact endpoint weight multiplier in Appendix A.2. -/
def endpointFactor (p j : ℝ) : ℝ := (2 : ℝ) ^ (-2 * j / p)

theorem endpointFactor_pos (p j : ℝ) : 0 < endpointFactor p j :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem endpoint_radius_factor (p j : ℝ) :
    Real.sqrt (endpointFactor p j)⁻¹ = (2 : ℝ) ^ (j / p) := by
  unfold endpointFactor
  rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem endpoint_radius {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) (p j : ℝ) (i : Fin n) :
    radius A (fun k => endpointFactor p j * w k) i =
      (2 : ℝ) ^ (j / p) * radius A w i := by
  rw [radius_rescale A w hA hw _ (endpointFactor_pos p j), endpoint_radius_factor]

theorem endpoint_leverage {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i) (p j : ℝ) (i : Fin n) :
    leverage A (fun k => endpointFactor p j * w k) i = leverage A w i :=
  leverage_rescale A w hA hw _ (ne_of_gt (endpointFactor_pos p j)) i

/-- Consecutive endpoint scales differ by the exact fixed multiplier. -/
theorem endpointFactor_step (p j : ℝ) :
    endpointFactor p (j + 1) = (2 : ℝ) ^ (-2 / p) * endpointFactor p j := by
  unfold endpointFactor
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- The endpoint scheme has nonincreasing weights for every positive exponent. -/
theorem endpoint_weight_step_le {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (p j : ℝ) (hp : 0 < p) (i : Fin n) :
    endpointFactor p (j + 1) * w i ≤ endpointFactor p j * w i := by
  rw [endpointFactor_step, mul_assoc]
  have hle : (2 : ℝ) ^ (-2 / p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hp.le)
  exact mul_le_of_le_one_left (mul_nonneg (endpointFactor_pos p j).le (hw i)) hle

/-- A normalized endpoint solution gives the exact equation (A.2) at every
scale. The premise is only the endpoint normalization; all scaled radii,
inverses and leverage invariance are derived above. -/
theorem endpoint_power_identity {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w : Fin n → ℝ) (hA : Function.Injective A.mulVec) (hw : ∀ i, 0 < w i)
    (p j : ℝ) (hp : 0 < p) (i : Fin n)
    (hbase : radius A w i ^ p / leverage A w i = 1) :
    radius A (fun k => endpointFactor p j * w k) i ^ p /
        leverage A (fun k => endpointFactor p j * w k) i = (2 : ℝ) ^ j := by
  rw [endpoint_radius A w hA hw p j i, endpoint_leverage A w hA hw p j i]
  have htwo : 0 ≤ (2 : ℝ) ^ (j / p) := Real.rpow_nonneg (by norm_num) _
  have hr : 0 ≤ radius A w i := Real.sqrt_nonneg _
  rw [Real.mul_rpow htwo hr]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), div_mul_cancel₀ j (ne_of_gt hp)]
  calc
    (2 : ℝ) ^ j * radius A w i ^ p / leverage A w i =
        (2 : ℝ) ^ j * (radius A w i ^ p / leverage A w i) := by ring
    _ = (2 : ℝ) ^ j := by rw [hbase, mul_one]

end Paper29.Leverage
