import Paper29.UniformExpectation
import Paper29.CenteredEvents

noncomputable section
open scoped BigOperators ENNReal Classical
namespace Paper29.ProcessTools

/-- The exact B-dependent constant used in the sample lower bound. -/
def transferConstant (C G B : ℝ) : ℝ := (2 * C * G) ^ 2 * (B * (2 + 6 * B))

theorem transferConstant_quadratic {C G B : ℝ} (hB : 1 ≤ B) :
    transferConstant C G B ≤ 8 * (2 * C * G) ^ 2 * B ^ 2 := by
  have hcoef : B * (2 + 6 * B) ≤ 8 * B ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ B) (by linarith : 0 ≤ B-1)]
  have hh := mul_le_mul_of_nonneg_left hcoef (sq_nonneg (2*C*G))
  unfold transferConstant
  convert hh using 1 <;> ring

/-- The numerical sample condition gives both the unshifted bootstrap
condition and the desired centered expectation coefficient. -/
theorem sample_size_effect {C G T B η δ : ℝ} {m : ℕ}
    (hC : 0 < C) (hG : 0 < G) (hT : 0 < T) (hB : 1 ≤ B)
    (hη : 0 < η) (hηhi : η < 1/2) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hm : 0 < m)
    (hsize : transferConstant C G B * T / (η ^ 2 * δ ^ 2) ≤ (m : ℝ)) :
    alpha C G T m ≤ 1 ∧ alpha C G T m * Real.sqrt (B * (2 + 6 * B)) ≤ δ * η := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcoef : 1 ≤ B * (2 + 6 * B) := by nlinarith [sq_nonneg (B-1)]
  have hα0 : 0 ≤ alpha C G T m := by unfold alpha; positivity
  have hpoly := (div_le_iff₀ (mul_pos (sq_pos_of_pos hη) (sq_pos_of_pos hδ))).1 hsize
  have hsquare : (alpha C G T m * Real.sqrt (B * (2 + 6 * B))) ^ 2 ≤ (δ * η) ^ 2 := by
    have heq : (alpha C G T m * Real.sqrt (B * (2 + 6 * B))) ^ 2 =
        transferConstant C G B * T / m := by
      unfold alpha transferConstant
      rw [mul_pow, mul_pow, mul_pow, mul_pow,
        Real.sq_sqrt (div_nonneg hT.le hmR.le), Real.sq_sqrt (by linarith : 0 ≤ B*(2+6*B))]
      ring
    rw [heq]
    apply (div_le_iff₀ hmR).2
    convert hpoly using 1 <;> ring
  have hfactor := (sq_le_sq₀ (mul_nonneg hα0 (Real.sqrt_nonneg _))
    (mul_nonneg hδ.le hη.le)).1 hsquare
  have ha : alpha C G T m ≤ alpha C G T m * Real.sqrt (B * (2 + 6 * B)) := by
    simpa using mul_le_mul_of_nonneg_left (Real.one_le_sqrt.mpr hcoef) hα0
  have hηδ : δ * η ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hηhi.le hδ.le
    nlinarith
  exact ⟨ha.trans (hfactor.trans hηδ), hfactor⟩

/-- Lemma3.6: actual finite-IID sampling probability of the uniform centered
affine increment event. Only the universal external process theorem and the
upstream design-only score geometry are inputs; the centered transfer itself,
its random-envelope bound and its B² constant are proved here. -/
theorem centered_affine_transfer {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z τ π : Fin n → ℝ) (T C G B η δ : ℝ)
    (hT : 0 < T) (hC : 0 < C) (hG : 0 < G)
    (external : ExternalProcess.AnchoredChaining C)
    (hτ : ∀ i, 0 < τ i) (hπ : ∀ i, 0 < π i) (hsum : ∑ i, π i = 1)
    (hrel : ∀ i, τ i = T * π i) (cover : ScoreGeometry A τ G)
    (hB : 1 ≤ B) (hη : 0 < η) (hηhi : η < 1/2) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hR : 0 < baseline z)
    (hsize : transferConstant C G B * T / (η ^ 2 * δ ^ 2) ≤ (m : ℝ)) :
    1 - δ ≤ Sampling.eventMass (Sampling.iidMass π)
      (Finset.univ.filter (fun ν : Fin m → Fin n =>
        CenteredTransferEvent A z π (B * baseline z) (η * baseline z) ν)) := by
  classical
  have hB0 : 0 < B := by linarith
  have hcoef : 0 < B * (2 + 6 * B) := mul_pos hB0 (by linarith)
  have hszpos : 0 < transferConstant C G B * T / (η^2*δ^2) := by
    unfold transferConstant
    positivity
  have hmR : (0 : ℝ) < m := hszpos.trans_le hsize
  have hm : 0 < m := by exact_mod_cast hmR
  obtain ⟨ha, hfactor⟩ := sample_size_effect hC hG hT hB hη hηhi hδ hδhi hm hsize
  have he := centered_error_expectation A z τ π T C G B hT hC.le hG.le external
    hτ hπ hsum hm hrel cover ha hB hR
  have hp := mul_le_mul_of_nonneg_right hfactor hR.le
  have hbound : Sampling.expectation π
      (errorSup (m := m) π (affineClass A z (B * baseline z))) ≤ δ * (η * baseline z) := by
    nlinarith only [he, hp]
  have hBR : 0 ≤ B * baseline z := mul_nonneg hB0.le hR.le
  have hg := good_event_of_expectation (Sampling.iidMass π)
    (errorSup (m := m) π (affineClass A z (B * baseline z)))
    (Sampling.iidMass_nonneg π (fun i => (hπ i).le)) (Sampling.iidMass_sum π hsum)
    (centered_error_nonneg A z π (fun i => (hπ i).le) hBR) (mul_pos hη hR) hbound
  simpa only [← centered_event_iff A z π (fun i => (hπ i).le) hBR] using hg

end Paper29.ProcessTools
