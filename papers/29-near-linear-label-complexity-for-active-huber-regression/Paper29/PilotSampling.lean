import Paper29.DyadicGrid
import Paper29.PilotConclusion
import Paper29.ScoreMonotonicity

noncomputable section
open scoped BigOperators Classical
namespace Paper29.ProcessTools

/-- The explicit quadratic sample condition supplies the finite-grid union
budget and the unshifted self-bounding condition simultaneously. -/
theorem pilot_sample_effect {C G T δ J : ℝ} {m : ℕ}
    (hC : 0 < C) (hG : 0 < G) (hT : 0 < T) (hδ : 0 < δ) (hδhi : δ ≤ 1)
    (hJ : 1 ≤ J)
    (hsize : (128*C*G)^2 * T * J^2 / δ^2 ≤ (m : ℝ)) :
    0 < m ∧ alpha C G T m ≤ 1 ∧ 64 * alpha C G T m * J ≤ δ := by
  have hJ0 : 0 < J := by linarith
  have hszpos : 0 < (128*C*G)^2 * T * J^2 / δ^2 := by positivity
  have hmR : (0 : ℝ) < m := hszpos.trans_le hsize
  have hm : 0 < m := by exact_mod_cast hmR
  have hα0 : 0 ≤ alpha C G T m := by unfold alpha; positivity
  have hpoly := (div_le_iff₀ (sq_pos_of_pos hδ)).1 hsize
  have hs : (64 * alpha C G T m * J)^2 ≤ δ^2 := by
    have he : (64 * alpha C G T m * J)^2 = (128*C*G)^2 * T * J^2 / m := by
      unfold alpha
      rw [mul_pow, mul_pow, mul_pow, mul_pow,
        Real.sq_sqrt (div_nonneg hT.le hmR.le)]
      ring
    rw [he]
    exact (div_le_iff₀ hmR).2 (by convert hpoly using 1 <;> ring)
  have hb : 64 * alpha C G T m * J ≤ δ :=
    (sq_le_sq₀ (by positivity) hδ.le).1 hs
  have ha : alpha C G T m ≤ 64 * alpha C G T m * J := by nlinarith
  exact ⟨hm, ha.trans (hb.trans hδhi), hb⟩

/-- Pilot mixing (3.30) is label-oblivious and has a uniform lower bound. -/
def pilotScores {n : ℕ} (τ : Fin n → ℝ) (i : Fin n) : ℝ :=
  τ i + (∑ j, τ j) / n

theorem pilotScores_spec {n : ℕ} (hn : 1 ≤ n) (τ : Fin n → ℝ)
    (hτ : ∀ i, 0 < τ i) :
    (∀ i, 0 < pilotScores τ i) ∧
      (∑ i, pilotScores τ i) = 2 * ∑ i, τ i ∧
      (∀ i, 1 / (2 * (n : ℝ)) ≤ scoreProbability (pilotScores τ) i) := by
  obtain ⟨hT, _, _, _⟩ := scoreProbability_spec hn τ hτ
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hpos (i) : 0 < pilotScores τ i :=
    add_pos (hτ i) (div_pos hT hnR)
  have hsum : (∑ i, pilotScores τ i) = 2 * ∑ i, τ i := by
    simp only [pilotScores, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  refine ⟨hpos, hsum, ?_⟩
  intro i
  unfold scoreProbability
  rw [hsum]
  apply (le_div_iff₀ (mul_pos (by norm_num) hT)).2
  have he : 1 / (2 * (n : ℝ)) * (2 * ∑ j, τ j) = (∑ j, τ j) / n := by ring
  rw [he]
  exact le_add_of_nonneg_left (hτ i).le

theorem pilotProbability_nonneg {n : ℕ} (hn : 1 ≤ n) (τ : Fin n → ℝ)
    (hτ : ∀ i, 0 < τ i) : ∀ i, 0 ≤ scoreProbability (pilotScores τ) i :=
  fun i => ((scoreProbability_spec hn _ (pilotScores_spec hn τ hτ).1).2.1 i).le

/-- Full finite-IID pilot bound (3.36), relative only to the separately exposed
score geometry and the disclosed universal chaining input. The sample bound is
exactly the paper's `T log³(2N) J² / δ²` dependence. -/
theorem pilot_guarantee {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hn : 16 < n) (τ : Fin n → ℝ) (hτ : ∀ i, 0 < τ i)
    (C G δ : ℝ) (hC : 0 < C) (hG : 0 < G) (hδ : 0 < δ) (hδhi : δ ≤ 1)
    (external : ExternalProcess.AnchoredChaining C)
    (cover : ScoreGeometry A τ (G * logFactor n))
    (hsize : (128*C*G)^2 * (2 * ∑ i, τ i) * Real.log (2*(n:ℝ))^3 *
      ((pilotGrid n).card : ℝ)^2 / δ^2 ≤ (m : ℝ))
    (b : Fin n → ℝ) (xstar : Fin d → ℝ) :
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
  apply pilot_center_probability A b (scoreProbability (pilotScores τ)) hπ hsum hm xstar hδ
  exact pilot_embedding_probability A (pilotScores τ) (scoreProbability (pilotScores τ))
    (∑ i, pilotScores τ i) C (G*logFactor n) δ hn hT hC.le
    (mul_pos hG (logFactor_pos hn1)).le external hτ' hπ hsum hlower hm hrel (cover.mono hτ (fun i => le_add_of_nonneg_right (div_nonneg (le_of_lt (scoreProbability_spec hn1 τ hτ).1) (Nat.cast_nonneg n))))
    ha (pilotGrid n) (pilotGrid_pos n) (pilotGrid_covers A) hbudget

end Paper29.ProcessTools
