import Paper26.SampleLowerBounds

/-! The rank/dimension comparison at the end of Section 3.3. The input
family has rank `min r (d/2)` and lies in the original rank-at-most-r class. -/
noncomputable section

namespace Paper26.RankReduction

def reducedRank (d r : ℕ) : ℕ := min r (d / 2)

theorem reducedRank_properties (d r : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d) :
    0 < reducedRank d r ∧ reducedRank d r ≤ r ∧
    reducedRank d r ≤ d - reducedRank d r ∧
    r ≤ 3 * reducedRank d r ∧ d ≤ 2 * (d - reducedRank d r) := by
  unfold reducedRank
  omega

/-- Only scalar comparisons remain in the passage from `s=d-k` to `d`.
The common factor 32 suffices for all four rates. -/
theorem compare_rates {r d k s : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hk : 0 ≤ k) (hs : 0 ≤ s) (hrk : r ≤ 3 * k) (hds : d ≤ 2 * s) :
    Real.sqrt r * d * Real.sqrt d ≤ 32 * (Real.sqrt k * s * Real.sqrt s) ∧
    r * Real.sqrt r * d * Real.sqrt d ≤ 32 * (k * Real.sqrt k * s * Real.sqrt s) ∧
    d ^ 2 ≤ 32 * s ^ 2 ∧ r * d ^ 2 ≤ 32 * (k * s ^ 2) := by
  have hsr : Real.sqrt r ≤ 2 * Real.sqrt k := by
    have hp : 0 ≤ 2 * Real.sqrt k := by positivity
    exact (Real.sqrt_le_iff).2 ⟨hp, by nlinarith [Real.sq_sqrt hk]⟩
  have hsd : Real.sqrt d ≤ 2 * Real.sqrt s := by
    have hp : 0 ≤ 2 * Real.sqrt s := by positivity
    exact (Real.sqrt_le_iff).2 ⟨hp, by nlinarith [Real.sq_sqrt hs]⟩
  have hB : Real.sqrt r * d * Real.sqrt d ≤
      8 * (Real.sqrt k * s * Real.sqrt s) := by
    calc
      _ ≤ (2 * Real.sqrt k) * (2 * s) * (2 * Real.sqrt s) :=
        mul_le_mul (mul_le_mul hsr hds hd (by positivity)) hsd
          (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have hB1 := mul_le_mul hrk hB (by positivity : 0 ≤ Real.sqrt r * d * Real.sqrt d)
    (by positivity : 0 ≤ 3 * k)
  have hR : d ^ 2 ≤ 4 * s ^ 2 := by nlinarith
  have hR1 := mul_le_mul hrk hR (sq_nonneg d) (by positivity : 0 ≤ 3 * k)
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [show 0 ≤ Real.sqrt k * s * Real.sqrt s by positivity]
  · nlinarith [show 0 ≤ k * Real.sqrt k * s * Real.sqrt s by positivity]
  · nlinarith [sq_nonneg s]
  · nlinarith [show 0 ≤ k * s ^ 2 by positivity]

theorem compare_reduced_rates (d r : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d) :
    let k := reducedRank d r
    let s := d - k
    Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) ≤
        32 * (Real.sqrt (k : ℝ) * s * Real.sqrt (s : ℝ)) ∧
    (r : ℝ) * Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) ≤
        32 * ((k : ℝ) * Real.sqrt (k : ℝ) * s * Real.sqrt (s : ℝ)) ∧
    (d : ℝ) ^ 2 ≤ 32 * (s : ℝ) ^ 2 ∧
    (r : ℝ) * (d : ℝ) ^ 2 ≤ 32 * ((k : ℝ) * (s : ℝ) ^ 2) := by
  have h := reducedRank_properties d r hd hr hrd
  apply compare_rates (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact_mod_cast h.2.2.2.1
  · exact_mod_cast h.2.2.2.2

end Paper26.RankReduction
