import Paper20.FastHilbertTotal
import Paper20.LogSeries

namespace Paper20.HilbertSeriesProof
open Paper20.FastHilbert
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def hookInverse (a : ℕ) : PowerSeries ℚ := (1-PowerSeries.X^a)⁻¹

theorem hook_constant (a : ℕ) (ha : 0 < a) :
    PowerSeries.constantCoeff (1-PowerSeries.X^a:PowerSeries ℚ) = 1 := by
  simp [ne_of_gt ha]

theorem inverse_product_recurrence (F : PowerSeries ℚ) (a : ℕ) (ha : 0 < a) (i : ℕ) :
    PowerSeries.coeff i (F*hookInverse a) = PowerSeries.coeff i F+
      if a ≤ i then PowerSeries.coeff (i-a) (F*hookInverse a) else 0 := by
  have he : (1-PowerSeries.X^a)*(F*hookInverse a) = F := by
    calc
      _ = F*((1-PowerSeries.X^a)*hookInverse a) := by ring
      _ = F := by rw [hookInverse, PowerSeries.mul_inv_cancel _ (by rw [hook_constant a ha]; norm_num), mul_one]
  have hc := congrArg (PowerSeries.coeff i) he
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul'] at hc
  linear_combination (norm := ring_nf) hc

/-- A single actual geometric update computes multiplication by the
genuine formal-series inverse of `1-q^a`, through the whole truncation. -/
theorem geom_coeff (t : List ℕ) (a : ℕ) (ha : 0 < a) (F : PowerSeries ℚ)
    (hF : ∀ i < t.length, (t.getD i 0:ℚ) = PowerSeries.coeff i F)
    (i : ℕ) (hi : i < t.length) :
    ((geom t a).getD i 0:ℚ) = PowerSeries.coeff i (F*hookInverse a) := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    rw [geom_recurrence t a ha i hi, Nat.cast_add, hF i hi,
      inverse_product_recurrence F a ha i]
    by_cases hia : a ≤ i
    · rw [if_pos hia, if_pos hia]
      exact congrArg (fun x => PowerSeries.coeff i F+x)
        (ih (i-a) (by omega) (by omega))
    · simp [hia]

theorem fold_geom_coeff (hooks : List ℕ) (hh : ∀ a ∈ hooks, 0 < a)
    (t : List ℕ) (F : PowerSeries ℚ)
    (hF : ∀ i < t.length, (t.getD i 0:ℚ) = PowerSeries.coeff i F) :
    ∀ i < t.length, ((hooks.foldl geom t).getD i 0:ℚ) =
      PowerSeries.coeff i (F*(hooks.map hookInverse).prod) := by
  induction hooks generalizing t F with
  | nil => simpa using hF
  | cons a hooks ih =>
    have ha := hh a (by simp)
    have ht := ih (fun b hb => hh b (by simp [hb])) (geom t a) (F*hookInverse a)
      (fun i hi => geom_coeff t a ha F hF i (by simpa only [geom_length] using hi))
    simpa only [List.foldl_cons, geom_length, List.map_cons, List.prod_cons, mul_assoc] using ht

theorem initial_length (len : ℕ) : ((1::List.replicate (len-1) 0).take len).length=len := by
  cases len <;> simp

theorem initial_coeff (len i : ℕ) (hi : i < len) :
    ((((1:ℕ)::List.replicate (len-1) 0).take len).getD i 0:ℚ) =
      PowerSeries.coeff i (1:PowerSeries ℚ) := by
  rw [getD_take_lt _ len i hi]
  cases i with
  | zero => simp
  | succ i => simp [PowerSeries.coeff_one]

/-- The complete executable hook-denominator series has the original
formal power-series meaning, with no certificate coefficient premise. -/
theorem series_coeff (hooks : List ℕ) (hh : ∀ a ∈ hooks, 0 < a)
    (len i : ℕ) (hi : i < len) :
    ((FastHilbert.series hooks len).getD i 0:ℚ) =
      PowerSeries.coeff i (hooks.map hookInverse).prod := by
  have h := fold_geom_coeff hooks hh ((1::List.replicate (len-1) 0).take len) 1
    (fun j hj => initial_coeff len j (by simpa only [initial_length] using hj)) i
    (by simpa only [initial_length] using hi)
  simpa only [FastHilbert.series, one_mul] using h

end
end Paper20.HilbertSeriesProof
