import PsgEst.Estimator

/-!
# Early stopping and necessity of separate normalizations

These are the two deterministic observations following the estimator definition
in Section 2: later lag candidates are bounded by the reciprocal lag, and using
the outgoing degree vector on both sides need not produce a contraction.
-/

open Matrix BigOperators Real

namespace PsgEst

variable {d : ℕ}

/-- Once the current maximum reaches `1/(k+1)`, every later lag is bounded by
it. All candidates here use the same fixed trajectory `X`. -/
theorem later_lag_le_of_stopping_threshold {n : ℕ}
    (X : Fin (n + 1) → Fin d) (k j : ℕ) (b : ℝ)
    (hstop : (1 : ℝ) / (k + 1) ≤ b) (hj : k < j) :
    aHat (skipPath X j) / j ≤ b := by
  have hjpos : 0 < j := by omega
  have hkpos : (0 : ℝ) < k + 1 := by positivity
  have hkj : (k : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hj)
  apply (lag_bound X j hjpos).trans
  exact (one_div_le_one_div_of_le hkpos hkj).trans hstop

/-- A bound on the candidates already inspected becomes a bound on the entire
estimator as soon as the stopping threshold is reached. -/
theorem gammaHat_le_of_early_stopping {n : ℕ}
    (X : Fin (n + 1) → Fin d) (k : ℕ) (b : ℝ)
    (hstop : (1 : ℝ) / (k + 1) ≤ b)
    (hprefix : ∀ j : ℕ, 0 < j → j ≤ k → aHat (skipPath X j) / j ≤ b) :
    gammaHat X ≤ b := by
  apply gammaHat_le X b ((by positivity : (0 : ℝ) ≤ 1 / (k + 1)).trans hstop)
  intro j hj _
  by_cases hjk : j ≤ k
  · exact hprefix j hj hjk
  · exact later_lag_le_of_stopping_threshold X k j b hstop (Nat.lt_of_not_ge hjk)

/-- If an inspected candidate attains the current maximum and the threshold,
no remaining lag changes the answer. -/
theorem gammaHat_eq_of_early_stopping {n : ℕ}
    (X : Fin (n + 1) → Fin d) (k j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
    (hstop : (1 : ℝ) / (k + 1) ≤ aHat (skipPath X j) / j)
    (hprefix : ∀ l : ℕ, 0 < l → l ≤ k →
      aHat (skipPath X l) / l ≤ aHat (skipPath X j) / j) :
    gammaHat X = aHat (skipPath X j) / j := by
  exact le_antisymm (gammaHat_le_of_early_stopping X k _ hstop hprefix)
    (gammaHat_candidate_le X j hj hjn)

/-- The path `(1,1,2,2)` from the paper, with zero-based state labels. -/
def normalizationCounterexamplePath : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- Incorrect normalization using the outgoing degrees on both sides. -/
noncomputable def outgoingBoth {m : ℕ} (Y : Fin (m + 1) → Fin d) :
    Matrix (Fin d) (Fin d) ℝ :=
  diagonal (fun i => (outDeg Y i : ℝ) ^ (-(1 / 2 : ℝ))) * countMatR Y *
    diagonal (fun j => (outDeg Y j : ℝ) ^ (-(1 / 2 : ℝ)))

theorem normalizationCounterexample_counts :
    countMat normalizationCounterexamplePath = !![1, 1; 0, 1] := by
  decide

theorem normalizationCounterexample_outDeg :
    outDeg normalizationCounterexamplePath = ![2, 1] := by
  funext i
  fin_cases i <;> decide

theorem normalizationCounterexample_inDeg :
    inDeg normalizationCounterexamplePath = ![1, 2] := by
  funext i
  fin_cases i <;> decide

/-- The incorrect operator sends the second coordinate vector to
`(1/√2,1)`. -/
theorem outgoingBoth_counterexample_mulVec :
    outgoingBoth normalizationCounterexamplePath *ᵥ ![(0 : ℝ), 1] =
      ![(2 : ℝ) ^ (-(1 / 2 : ℝ)), 1] := by
  have hC : countMatR normalizationCounterexamplePath = !![(1 : ℝ), 1; 0, 1] := by
    ext i j
    simp only [countMatR_apply, normalizationCounterexample_counts]
    fin_cases i <;> fin_cases j <;> norm_num
  rw [outgoingBoth, normalizationCounterexample_outDeg, hC]
  ext i
  fin_cases i <;>
    norm_num [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.diagonal_apply, Real.one_rpow]

/-- Its output squared Euclidean norm is `3/2`, exceeding the input norm `1`.
Thus outgoing-degree normalization on both sides is not a contraction. -/
theorem outgoingBoth_counterexample_norm_sq :
    (∑ i, (outgoingBoth normalizationCounterexamplePath *ᵥ ![(0 : ℝ), 1]) i ^ 2) =
      (3 / 2 : ℝ) := by
  have hpow : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / 2 := by
    rw [pow_two, rpow_neg_half_sq 2 (by norm_num), Real.rpow_neg_one]
    norm_num
  rw [outgoingBoth_counterexample_mulVec]
  norm_num [Fin.sum_univ_two, hpow]

theorem outgoingBoth_not_contraction :
    ¬ (∀ u : Fin 2 → ℝ,
      (∑ i, (outgoingBoth normalizationCounterexamplePath *ᵥ u) i ^ 2) ≤
        ∑ i, u i ^ 2) := by
  intro h
  have hv := h ![(0 : ℝ), 1]
  rw [outgoingBoth_counterexample_norm_sq] at hv
  norm_num [Fin.sum_univ_two] at hv

end PsgEst
