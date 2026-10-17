import Paper29.CenteredTransfer

noncomputable section
open scoped BigOperators ENNReal Classical
namespace Paper29.ProcessTools

def logFactor (n : ℕ) : ℝ := Real.sqrt (Real.log (2 * (n : ℝ)) ^ 3)

theorem logFactor_pos {n : ℕ} (hn : 1 ≤ n) : 0 < logFactor n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by linarith)
  exact Real.sqrt_pos.2 (pow_pos hl 3)

theorem logFactor_sq {n : ℕ} (hn : 1 ≤ n) :
    logFactor n ^ 2 = Real.log (2 * (n : ℝ)) ^ 3 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log (2 * (n : ℝ)) := (Real.log_pos (by linarith : 1 < 2*(n:ℝ))).le
  exact Real.sq_sqrt (pow_nonneg hl 3)

theorem logFactor_eq_rpow {n : ℕ} (hn : 1 ≤ n) :
    logFactor n = Real.log (2 * (n : ℝ)) ^ (3/2 : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log (2 * (n : ℝ)) := (Real.log_pos (by linarith : 1 < 2*(n:ℝ))).le
  unfold logFactor
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hl]
  norm_num

/-- Factoring out log³ leaves a constant depending only on B and the two
universal external/covering constants, exactly as in (3.26). -/
theorem transferConstant_log {n : ℕ} (hn : 1 ≤ n) (C G B : ℝ) :
    transferConstant C (G * logFactor n) B =
      transferConstant C G B * Real.log (2 * (n : ℝ)) ^ 3 := by
  unfold transferConstant
  rw [mul_pow, mul_pow, mul_pow, logFactor_sq hn]
  ring

/-- Positive, label-oblivious distribution π=τ/∑τ. -/
def scoreProbability {n : ℕ} (τ : Fin n → ℝ) (i : Fin n) : ℝ := τ i / ∑ j, τ j

theorem scoreProbability_spec {n : ℕ} (hn : 1 ≤ n) (τ : Fin n → ℝ)
    (hτ : ∀ i, 0 < τ i) :
    0 < (∑ i, τ i) ∧ (∀ i, 0 < scoreProbability τ i) ∧
      (∑ i, scoreProbability τ i) = 1 ∧
      (∀ i, τ i = (∑ j, τ j) * scoreProbability τ i) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hT : 0 < ∑ i, τ i := Finset.sum_pos (fun i _ => hτ i) Finset.univ_nonempty
  refine ⟨hT, (fun i => div_pos (hτ i) hT), ?_, ?_⟩
  · simp only [scoreProbability, ← Finset.sum_div, div_self (ne_of_gt hT)]
  · intro i
    unfold scoreProbability
    field_simp

/-- Original log³ sample dependence and all shifts, using one fixed score-only
sampling distribution. The conditional input is the general external theorem;
`cover` is the separately exposed upstream Lemma3.4 score-geometry obligation. -/
theorem centered_affine_transfer_scores {n d m : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (hn : 1 ≤ n) (τ : Fin n → ℝ)
    (hτ : ∀ i, 0 < τ i) (C G B η δ : ℝ) (hC : 0 < C) (hG : 0 < G)
    (external : ExternalProcess.AnchoredChaining C)
    (cover : ScoreGeometry A τ (G * logFactor n))
    (hB : 1 ≤ B) (hη : 0 < η) (hηhi : η < 1/2) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (z : Fin n → ℝ) (hR : 0 < baseline z)
    (hsize : transferConstant C G B * (∑ i, τ i) * Real.log (2 * (n : ℝ)) ^ 3 /
      (η ^ 2 * δ ^ 2) ≤ (m : ℝ)) :
    transferConstant C G B ≤ 8 * (2*C*G)^2 * B^2 ∧
    1 - δ ≤ Sampling.eventMass (Sampling.iidMass (scoreProbability τ))
      (Finset.univ.filter (fun ν : Fin m → Fin n =>
        CenteredTransferEvent A z (scoreProbability τ) (B * baseline z) (η * baseline z) ν)) := by
  obtain ⟨hT, hπ, hsum, hrel⟩ := scoreProbability_spec hn τ hτ
  refine ⟨transferConstant_quadratic hB, ?_⟩
  have hsize' : transferConstant C (G * logFactor n) B * (∑ i, τ i) /
      (η^2*δ^2) ≤ (m:ℝ) := by
    rw [transferConstant_log hn]
    convert hsize using 1 <;> ring
  exact centered_affine_transfer A z τ (scoreProbability τ) (∑ i,τ i) C (G*logFactor n) B η δ
    hT hC (mul_pos hG (logFactor_pos hn)) external hτ hπ hsum hrel cover
    hB hη hηhi hδ hδhi hR hsize'

end Paper29.ProcessTools
