import PsgEst.Ergodicity
import PsgEst.Mixing

/-!
# Convergence and ergodicity of powered chains

The source convergence statements for a fixed stochastic matrix and stationary
law, derived from the actual centered operator and the proved positive-gap
estimates. No stationary-law existence theorem is assumed.
-/

open Matrix BigOperators Real Finset Classical Filter Topology

namespace PsgEst

variable {d : ℕ}

/-- The contraction norm of the centered Markov powers tends to zero. -/
theorem bNorm_tendsto_zero (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) :
    Tendsto (fun t : ℕ => bNorm S st t) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := positive_gap_bNorm_small S st hgap ε hε
  refine ⟨N, fun t ht => ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (bNorm_nonneg S st t)] using hN t ht

/-- The paper's actual weighted operator norm `‖P^t-Π‖_π` tends to zero. -/
theorem weightedOperatorNorm_tendsto_zero (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) :
    Tendsto (fun t : ℕ => weightedOperatorNorm st.mu ((S.pow t).P - piMat st.mu))
      atTop (𝓝 0) := by
  simpa only [bNorm_eq_weightedOperatorNorm] using bNorm_tendsto_zero S st hgap

/-- Every relative transition-probability error tends to zero. -/
theorem relative_transition_tendsto_zero (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) (i j : Fin d) :
    Tendsto (fun t : ℕ => (S.pow t).P i j / st.mu j - 1) atTop (𝓝 0) := by
  letI : NeZero d := ⟨by have hi := i.isLt; omega⟩
  apply squeeze_zero_norm (fun t => by
    simpa only [Real.norm_eq_abs] using relative_entry_abs_le_bNorm S st t i j)
  simpa only [mul_zero] using
    (bNorm_tendsto_zero S st hgap).const_mul ((Stationary.star st)⁻¹)

/-- Each entry of the actual transition powers converges to the stationary law. -/
theorem transition_tendsto_stationary (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) (i j : Fin d) :
    Tendsto (fun t : ℕ => (S.pow t).P i j) atTop (𝓝 (st.mu j)) := by
  have h := ((relative_transition_tendsto_zero S st hgap i j).add_const (1 : ℝ)).mul_const (st.mu j)
  simpa only [sub_add_cancel, div_mul_cancel₀ _ (ne_of_gt (st.pos j)),
    zero_add, one_mul] using h

/-- The singular-value deficit tends to one as the lag tends to infinity. -/
theorem aK_tendsto_one (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) :
    Tendsto (fun t : ℕ => aK S st t) atTop (𝓝 1) := by
  simp_rw [aK_eq_one_sub_bNorm_sq]
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using
    (tendsto_const_nhds.sub ((bNorm_tendsto_zero S st hgap).pow 2))

/-- Every positive integer power has a positive pseudo-spectral gap with the
same stationary law, as used for the lagged chains in Section 3. -/
theorem powered_positive_gap (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) (k : ℕ) (hk : 0 < k) :
    0 < gammaPS (S.pow k) (stationaryPow S st k) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hmin : 0 < min ((k : ℝ) * gammaPS S st) 1 :=
    lt_min (mul_pos hkr hgap) zero_lt_one
  exact (mul_pos (by norm_num : (0 : ℝ) < 1 / 4) hmin).trans_le
    (((lemma_1 S st hgap).1 k hk).1)

/-- A positive power of a chain in the standard model remains irreducible and
aperiodic, with exactly `stationaryPow S st k` as its stationary-law witness. -/
theorem powered_standard_ergodicity (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) (k : ℕ) (hk : 0 < k) :
    MatrixIrreducible (S.pow k) ∧ MatrixAperiodic (S.pow k) :=
  (positive_gap_iff_irreducible_aperiodic (S.pow k) (stationaryPow S st k)).mp
    (powered_positive_gap S st hgap k hk)

end PsgEst
