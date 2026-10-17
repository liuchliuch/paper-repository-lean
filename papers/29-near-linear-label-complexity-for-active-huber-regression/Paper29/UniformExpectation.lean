import Paper29.ProcessComparison
import Paper29.Bootstrap

noncomputable section
open scoped BigOperators ENNReal
namespace Paper29.ProcessTools

/-- Lemma3.5's own self-bounding argument, with the precise general external
process theorem and upstream score geometry exposed separately. -/
theorem unshifted_expectation_bound {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (τ π : Fin n → ℝ) (T C G : ℝ) (hT : 0 < T) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (external : ExternalProcess.AnchoredChaining C)
    (hτ : ∀ i, 0 < τ i) (hπ : ∀ i, 0 < π i) (hsum : ∑ i, π i = 1)
    (hm : 0 < m) (hrel : ∀ i, τ i = T * π i) (cover : ScoreGeometry A τ G)
    (ha : alpha C G T m ≤ 1) {R : ℝ} (hR : 0 < R) :
    Sampling.expectation π (unshiftedError (m := m) A π R) ≤ 2 * alpha C G T m * R ∧
      Sampling.expectation π (unshiftedEnvelope (m := m) A π R) ≤ 3 * R := by
  have hπ0 (i) := (hπ i).le
  have hα0 : 0 ≤ alpha C G T m := by unfold alpha; positivity
  have hc := affine_chaining_comparison A 0 τ π T C G hT hC hG external
    hτ hπ hsum hm hrel cover hR
  have heqf : affineClass A (0 : Fin n → ℝ) R =
      (fun i (h : Ball A R) => huber ((A.mulVec h) i)) := by
    funext i h
    simp [affineClass]
  have heqL : shiftedEnvelope (m := m) A (0 : Fin n → ℝ) π R =
      unshiftedEnvelope A π R := by
    funext ν
    unfold shiftedEnvelope unshiftedEnvelope
    congr 1
    funext h
    simp [Sampling.sampledShifted, Sampling.sampledUnshifted]
  rw [heqf, heqL] at hc
  change Sampling.expectation π (unshiftedError (m := m) A π R) ≤ _ at hc
  let X := Sampling.expectation π (unshiftedError (m := m) A π R)
  let L := Sampling.expectation π (unshiftedEnvelope (m := m) A π R)
  have hX : 0 ≤ X := Finset.sum_nonneg fun ν _ => mul_nonneg
    (Sampling.iidMass_nonneg π hπ0 ν) (unshiftedError_nonneg A π hπ0 hR.le ν)
  have hL : L ≤ R + X := by
    have he := expectation_mono π hπ0 (unshiftedEnvelope (m := m) A π R)
      (fun ν => R + unshiftedError A π R ν) (unshiftedEnvelope_le A π hπ0 hR.le)
    rw [expectation_add, expectation_const π hsum] at he
    exact he
  have hj := expectation_sqrt_le π hπ0 hsum (unshiftedEnvelope (m := m) A π R)
    (unshiftedEnvelope_nonneg A π hπ0 hR.le)
  have hb : X ≤ alpha C G T m * Real.sqrt R * Real.sqrt (R + X) := by
    calc
      X ≤ alpha C G T m * Real.sqrt R *
          Sampling.expectation π (fun ν : Fin m → Fin n => Real.sqrt (unshiftedEnvelope A π R ν)) := hc
      _ ≤ alpha C G T m * Real.sqrt R * Real.sqrt L :=
        mul_le_mul_of_nonneg_left hj (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hL) (by positivity)
  have hbound := expectation_bootstrap hX hα0 ha hR hb
  refine ⟨hbound, ?_⟩
  have hp := mul_le_mul_of_nonneg_right ha hR.le
  nlinarith only [hL, hbound, hp]

def baseline {n : ℕ} (z : Fin n → ℝ) : ℝ := ∑ i, huber (z i)

/-- Equation(3.18) of the affine proof: the expected shifted random envelope
is bounded without any uniform affine-baseline preservation premise. -/
theorem shifted_envelope_expectation {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z τ π : Fin n → ℝ) (T C G B : ℝ) (hT : 0 < T) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (external : ExternalProcess.AnchoredChaining C)
    (hτ : ∀ i, 0 < τ i) (hπ : ∀ i, 0 < π i) (hsum : ∑ i, π i = 1)
    (hm : 0 < m) (hrel : ∀ i, τ i = T * π i) (cover : ScoreGeometry A τ G)
    (ha : alpha C G T m ≤ 1) (hB : 1 ≤ B) (hR : 0 < baseline z) :
    Sampling.expectation π (shiftedEnvelope (m := m) A z π (B * baseline z)) ≤
      (2 + 6 * B) * baseline z := by
  have hBR : 0 < B * baseline z := mul_pos (by linarith) hR
  have hφ := (unshifted_expectation_bound A τ π T C G hT hC hG external hτ hπ hsum
    hm hrel cover ha hBR).2
  have hzero : Sampling.expectation π (fun ν : Fin m → Fin n =>
      Sampling.sampledShifted π ν A z 0) = baseline z := by
    simpa [baseline, Matrix.mulVec_zero] using Sampling.sampledShifted_unbiased π A z 0 hπ hsum hm
  have he := expectation_mono π (fun i => (hπ i).le)
    (shiftedEnvelope (m := m) A z π (B * baseline z))
    (fun ν => 2 * Sampling.sampledShifted π ν A z 0 +
      2 * unshiftedEnvelope A π (B * baseline z) ν)
    (shiftedEnvelope_le A z π (fun i => (hπ i).le) hBR.le)
  rw [expectation_add, expectation_mul_const, expectation_mul_const, hzero] at he
  linarith

/-- The paper's D_B=O(B) centered-error expectation, fully derived from the
universal external process theorem, score geometry and Huber-specific bounds. -/
theorem centered_error_expectation {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z τ π : Fin n → ℝ) (T C G B : ℝ) (hT : 0 < T) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (external : ExternalProcess.AnchoredChaining C)
    (hτ : ∀ i, 0 < τ i) (hπ : ∀ i, 0 < π i) (hsum : ∑ i, π i = 1)
    (hm : 0 < m) (hrel : ∀ i, τ i = T * π i) (cover : ScoreGeometry A τ G)
    (ha : alpha C G T m ≤ 1) (hB : 1 ≤ B) (hR : 0 < baseline z) :
    Sampling.expectation π (errorSup (m := m) π (affineClass A z (B * baseline z))) ≤
      alpha C G T m * Real.sqrt (B * (2 + 6 * B)) * baseline z := by
  have hBR : 0 < B * baseline z := mul_pos (by linarith) hR
  have hα : 0 ≤ alpha C G T m := by unfold alpha; positivity
  have hc := affine_chaining_comparison A z τ π T C G hT hC hG external hτ hπ hsum
    hm hrel cover hBR
  have hj := expectation_sqrt_le π (fun i => (hπ i).le) hsum
    (shiftedEnvelope (m := m) A z π (B * baseline z))
    (shiftedEnvelope_nonneg A z π (fun i => (hπ i).le) hBR.le)
  have he := shifted_envelope_expectation A z τ π T C G B hT hC hG external hτ hπ
    hsum hm hrel cover ha hB hR
  calc
    _ ≤ alpha C G T m * Real.sqrt (B * baseline z) *
        Real.sqrt (Sampling.expectation π (shiftedEnvelope (m := m) A z π (B * baseline z))) :=
      hc.trans (mul_le_mul_of_nonneg_left hj (by positivity))
    _ ≤ alpha C G T m * Real.sqrt (B * baseline z) *
        Real.sqrt ((2 + 6 * B) * baseline z) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (by positivity)
    _ = _ := by
      rw [Real.sqrt_mul (by linarith : 0 ≤ B), Real.sqrt_mul (by linarith : 0 ≤ 2 + 6 * B)]
      calc
        _ = alpha C G T m * (Real.sqrt B * Real.sqrt (2 + 6 * B)) * Real.sqrt (baseline z) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hR.le, ← Real.sqrt_mul (by linarith : 0 ≤ B)]

end Paper29.ProcessTools
