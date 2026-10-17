import Paper25.Basic
import Paper25.Norms
import Paper25.Liouville
import Paper25.History
import Paper25.TraceReadout
import Paper25.CPTP
import Paper25.Regularization
import Paper25.Filter
import Paper25.PhaseEst
import Paper25.Bias
import Paper25.Model

/-!
# Numerical decision-gap consequences for Theorem 1

This module proves the scalar consequences of the trace approximation. The
actual circuit existence theorem and its uniform compiler must additionally
connect the channel history, spectral-filter circuit and operational readout.
The auxiliary positivity theorem at the end is not such a circuit theorem.
-/

set_option maxHeartbeats 800000

noncomputable section

open scoped ComplexConjugate

namespace Paper25

/-! ## Theorem 1: signed gap and decision bias -/

/-- Theorem 1, numerical core: on yes instances `a_x ≥ lam/(4√K)`, on no
instances `a_x ≤ -lam/(4√K)`, using `e_x ≥ 1/3` or `e_x ≤ -1/3` and (22). -/
theorem theorem1_decision_gap (lam K e a : ℝ)
    (hlam : 0 < lam) (hK : 1 ≤ K) (he : (1 / 3 : ℝ) ≤ |e|)
    (herr : |a - lam * e / Real.sqrt K| ≤ lam / (100 * K)) :
    (0 < e → lam / (4 * Real.sqrt K) ≤ a) ∧
    (e < 0 → a ≤ -lam / (4 * Real.sqrt K)) :=
  theorem1_signed_gap lam K e a hlam hK he herr

/-- Lemma 6 readout: the probe expectation is `a_x / 2^k`, so the acceptance
probability is `1/2 + a_x / 2^{k+1}`.  Combining with the decision gap gives
the DQC1 bias `γ = lam / (2^{k+3} √K)`. -/
theorem theorem1_prob_gap (lam K a : ℝ) (k : ℕ)
    (hlam : 0 < lam) (hK : 0 < K)
    (ha : lam / (4 * Real.sqrt K) ≤ a) :
    (1 / 2 : ℝ) + lam / ((2 : ℝ) ^ (k + 3) * Real.sqrt K)
      ≤ 1 / 2 + a / (2 : ℝ) ^ (k + 1) := by
  have hs : (0 : ℝ) < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hpow3 : (0 : ℝ) < (2 : ℝ) ^ (k + 3) := by positivity
  have h4 : ((2 : ℝ) ^ (k + 3)) = 4 * (2 : ℝ) ^ (k + 1) := by
    have h : (k + 3 : ℕ) = (k + 1) + 2 := by omega
    rw [h, pow_add]
    ring_nf
  have hle : lam / ((2 : ℝ) ^ (k + 3) * Real.sqrt K) ≤ a / (2 : ℝ) ^ (k + 1) := by
    rw [h4]
    have hdiv : lam / (4 * (2 : ℝ) ^ (k + 1) * Real.sqrt K)
        = (lam / (4 * Real.sqrt K)) / (2 : ℝ) ^ (k + 1) := by
      field_simp
    rw [hdiv]
    exact div_le_div_of_nonneg_right ha (le_of_lt hpow)
  linarith

/-- The weaker gap `γ/2` survives gate synthesis when `2ξ ≤ γ/4`. -/
theorem gap_survives_synthesis (gamma xi : ℝ)
    (h : 2 * xi ≤ gamma / 4) (hγ : 0 < gamma) :
    (1 / 2 : ℝ) + gamma - 2 * xi ≥ 1 / 2 + gamma / 2 := by
  linarith

/-! ## Auxiliary numerical positivity -/

/-- Historical auxiliary contract: positivity for some numerical dimensions.
This deliberately makes no claim about circuit existence, running time or
uniformity; `2^(T+1)` here is only a numerical witness. The actual least-power
clock and polynomial bounds are in `Resources.lean`. -/
theorem theorem1_certificate_exists (s c T k : ℕ) (_hc : 0 ≤ c)
    (hT : 1 ≤ T) (hs : 1 ≤ s) (hk : 0 ≤ k) :
    ∃ J K : ℝ, (1 ≤ J) ∧ (1 ≤ K) ∧
      (0 : ℝ) < biasLam J K ∧
      (0 : ℝ) < biasGamma (biasLam J K) K k := by
  refine ⟨(2 ^ (T + 1) : ℝ), (2 ^ s : ℝ), ?_, ?_, ?_, ?_⟩
  · have h : (1 : ℝ) ≤ 2 ^ (T + 1) := by
      have h1 : (0:ℕ) < T + 1 := Nat.succ_pos _
      have h2 : (2 : ℝ) ^ (T + 1) ≥ 2 ^ 1 := by
        exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
      norm_num at h2
      linarith
    exact h
  · have h : (1 : ℝ) ≤ 2 ^ s := by
      have h2 : (2 : ℝ) ^ s ≥ 2 ^ 1 := by
        exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
      norm_num at h2
      linarith
    exact h
  · exact biasLam_pos (by positivity) (by positivity)
  · exact biasGamma_pos (biasLam_pos (by positivity) (by positivity)) (by positivity)

end Paper25
