import PsgEst.QuantumRelativeEntropy
import PsgEst.QuantumVariational

/-! Finite-distribution Lieb concavity and the actual one-step trace potential.
The proof uses the established joint convexity of the actual matrix relative
entropy and the proved finite-dimensional Gibbs inequality. Neither assertion
is a hypothesis of the exported concentration step. -/

open Matrix BigOperators Real
open scoped Matrix.Norms.L2Operator

namespace PsgEst

open QuantumVariational

section Lieb

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Lieb's finite Jensen inequality for the actual trace exponential and CFC
logarithm. Its proof uses actual matrix entropy joint convexity, rather than
introducing concavity or an equivalent trace potential as an assumption. -/
theorem lieb_trace_finite_jensen (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
    (A : α → Matrix ι ι ℝ) (hA : ∀ a, (A a).PosDef)
    (B : Matrix ι ι ℝ) (hB : B.PosDef) (hmean : ∑ a, p a • A a = B) :
    (∑ a, p a * traceExp (H + CFC.log (A a))) ≤ traceExp (H + CFC.log B) := by
  let X (a : α) := NormedSpace.exp ℝ (H + CFC.log (A a))
  have hX (a : α) : (X a).PosDef :=
    matrixExp_posDef (hH.add (log_isHermitian (hA a).isHermitian))
  let Xbar := ∑ a, p a • X a
  have hXbar : Xbar.PosDef := weighted_sum_posDef p hp hsum X hX
  have hjoint := QuantumRelativeEntropy.relativeEntropy_joint_convex p hp hsum X A hX hA
  rw [hmean] at hjoint
  change relativeEntropy Xbar B ≤ ∑ a, p a * relativeEntropy (X a) (A a) at hjoint
  have hXH : (∑ a, p a * Matrix.trace (X a * H)) = Matrix.trace (Xbar * H) := by
    dsimp [Xbar]
    simp only [Matrix.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have hXt : (∑ a, p a * Matrix.trace (X a)) = Matrix.trace Xbar := by
    dsimp [Xbar]
    simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  have hvalues (a : α) : traceExp (H + CFC.log (A a)) =
      Matrix.trace (X a * H) - relativeEntropy (X a) (A a) + Matrix.trace (X a) :=
    (variational_attainment hH (hA a)).2.symm
  have hsumvalues : (∑ a, p a * traceExp (H + CFC.log (A a))) =
      Matrix.trace (Xbar * H) - (∑ a, p a * relativeEntropy (X a) (A a)) + Matrix.trace Xbar := by
    simp_rw [hvalues, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hXH, hXt]
  rw [hsumvalues]
  have hcmp : Matrix.trace (Xbar * H) - (∑ a, p a * relativeEntropy (X a) (A a)) +
      Matrix.trace Xbar ≤ Matrix.trace (Xbar * H) - relativeEntropy Xbar B + Matrix.trace Xbar := by
    linarith only [hjoint]
  exact hcmp.trans (variational_bound hH hB hXbar)

/-- The elementary scalar `log x ≤ x−1`, lifted at the actual positive spectrum. -/
theorem matrixLog_le_sub_one {Y : Matrix ι ι ℝ} (hY : Y.PosDef) :
    (Y - 1 - CFC.log Y).PosSemidef := by
  have hf (i : ι) : Real.log (hY.isHermitian.eigenvalues i) ≤ hY.isHermitian.eigenvalues i - 1 :=
    Real.log_le_sub_one_of_pos (hY.eigenvalues_pos i)
  have hupper : spectralMap hY.isHermitian (fun x => x-1) = Y-1 := by
    rw [spectralMap_sub]
    change spectralMap hY.isHermitian id - spectralMap hY.isHermitian (fun _ => 1) = Y-1
    rw [spectralMap_id, spectralMap_one]
  rw [log_eq_spectralMap hY.isHermitian, ← hupper]
  exact spectralMap_mono hY.isHermitian _ _ hf

/-- The genuine noncommutative one-step trace potential for finite conditional
distributions. The centered increments, variance, and mgf are the actual
weighted sums; no martingale tail or equivalent trace step is assumed. -/
theorem matrix_trace_potential_step (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
    (X : α → Matrix ι ι ℝ) (hX : ∀ a, (X a).IsHermitian)
    (θ R : ℝ) (hθ : 0 ≤ θ) (hR : 0 < R)
    (hbound : ∀ a, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (X a)‖ ≤ R)
    (hcenter : ∑ a, p a • X a = 0) :
    (∑ a, p a * traceExp (H + θ • X a -
      ((Real.exp (θ*R)-θ*R-1)/R^2) • (∑ a, p a • (X a * X a)))) ≤ traceExp H := by
  let g := (Real.exp (θ*R)-θ*R-1)/R^2
  let V := ∑ a, p a • (X a * X a)
  let E (a : α) := NormedSpace.exp ℝ (θ • X a)
  let Y := ∑ a, p a • E a
  have hθX (a : α) : (θ • X a).IsHermitian := by
    change (θ • X a)ᴴ = θ • X a
    rw [Matrix.conjTranspose_smul, star_trivial, (hX a).eq]
  have hE (a : α) : (E a).PosDef := matrixExp_posDef (hθX a)
  have hY : Y.PosDef := weighted_sum_posDef p hp hsum E hE
  have hV : V.PosSemidef := weighted_sum_posSemidef p hp _ (by
    intro a
    simpa only [(hX a).eq] using Matrix.posSemidef_conjTranspose_mul_self (X a))
  have hgV : (g • V).IsHermitian := by
    change (g • V)ᴴ = g • V
    rw [Matrix.conjTranspose_smul, star_trivial, hV.isHermitian.eq]
  have hmgf : ((1 : Matrix ι ι ℝ) + g • V - Y).PosSemidef :=
    matrix_mgf_bennett p hp hsum X hX θ R hθ hR hbound hcenter
  have hlogY : (g • V - CFC.log Y).PosSemidef := by
    have hsum := hmgf.add (matrixLog_le_sub_one hY)
    convert hsum using 1
    abel
  have hjensen := lieb_trace_finite_jensen p hp hsum (H - g • V) (hH.sub hgV) E hE Y hY rfl
  have hleft (a : α) : (H - g • V) + CFC.log (E a) = H + θ • X a - g • V := by
    rw [show CFC.log (E a) = θ • X a from CFC.log_exp _ (hθX a).isSelfAdjoint]
    abel
  simp_rw [hleft] at hjensen
  have hlast : traceExp ((H-g • V)+CFC.log Y) ≤ traceExp H := by
    apply traceExp_mono ((hH.sub hgV).add (log_isHermitian hY.isHermitian)) hH
    convert hlogY using 1
    abel
  exact hjensen.trans hlast

end Lieb

end PsgEst
