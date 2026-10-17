import Paper29.PilotSampling

noncomputable section
open scoped BigOperators Classical
namespace Paper29.ProcessTools

theorem pilot_full_guarantee {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hn : 16 < n) (τ : Fin n → ℝ) (hτ : ∀ i, 0 < τ i)
    (C G δ : ℝ) (hC : 0 < C) (hG : 0 < G) (hδ : 0 < δ) (hδhi : δ ≤ 1)
    (external : ExternalProcess.AnchoredChaining C)
    (cover : ScoreGeometry A τ (G * logFactor n))
    (hsize : (128*C*G)^2 * (2 * ∑ i, τ i) * Real.log (2*(n:ℝ))^3 *
      ((pilotGrid n).card : ℝ)^2 / δ^2 ≤ (m : ℝ))
    (b : Fin n → ℝ) (xstar : Fin d → ℝ) :
    (1 - δ ≤ Sampling.eventMass (Sampling.iidMass (scoreProbability (pilotScores τ)))
      (Finset.univ.filter (fun ν : Fin m → Fin n => ∀ h,
        |Sampling.sampledUnshifted (scoreProbability (pilotScores τ)) ν A h-unshifted A h| ≤
          (1/8)*unshifted A h))) ∧
    1 - 2*δ ≤ Sampling.eventMass (Sampling.iidMass (scoreProbability (pilotScores τ)))
      (Finset.univ.filter (fun ν : Fin m → Fin n =>
        objective A b (pilotCenter A b (scoreProbability (pilotScores τ))
          (pilotProbability_nonneg (by omega) τ hτ) ν) ≤
        (1 + 2 / Real.sqrt ((1-1/8)*δ))^2 * objective A b xstar)) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hτ', hmass, hlower⟩ := pilotScores_spec hn1 τ hτ
  obtain ⟨hT, hπ, hsum, hrel⟩ := scoreProbability_spec hn1 (pilotScores τ) hτ'
  have hJ : (1 : ℝ) ≤ (pilotGrid n).card := by
    exact_mod_cast Finset.one_le_card.mpr (pilotGrid_nonempty hn1)
  have hsize' : (128*C*(G*logFactor n))^2 * (∑ i, pilotScores τ i) *
      ((pilotGrid n).card : ℝ)^2 / δ^2 ≤ (m : ℝ) := by
    rw [hmass]
    convert hsize using 1
    rw [mul_pow, mul_pow, mul_pow, logFactor_sq hn1]
    ring
  obtain ⟨hm, ha, hbudget⟩ := pilot_sample_effect hC (mul_pos hG (logFactor_pos hn1))
    hT hδ hδhi hJ hsize'
  refine ⟨?_,pilot_guarantee A hn τ hτ C G δ hC hG hδ hδhi external cover hsize b xstar⟩
  exact pilot_embedding_probability A (pilotScores τ) (scoreProbability (pilotScores τ))
    (∑ i, pilotScores τ i) C (G*logFactor n) δ hn hT hC.le
    (mul_pos hG (logFactor_pos hn1)).le external hτ' hπ hsum hlower hm hrel (cover.mono hτ (fun i => le_add_of_nonneg_right (div_nonneg (le_of_lt (scoreProbability_spec hn1 τ hτ).1) (Nat.cast_nonneg n))))
    ha (pilotGrid n) (pilotGrid_pos n) (pilotGrid_covers A) hbudget

end Paper29.ProcessTools
