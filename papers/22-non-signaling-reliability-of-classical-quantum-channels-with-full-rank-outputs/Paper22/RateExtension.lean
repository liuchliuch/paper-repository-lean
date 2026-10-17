import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semifield

noncomputable section
namespace Paper22

lemma floor_half_natCast (L : ℕ) : ⌊(L : ℝ) / 2⌋₊ = L / 2 := by
  simpa using Nat.floor_div_natCast (L : ℝ) 2

lemma ceil_half_natCast (L : ℕ) : ⌈(L : ℝ) / 2⌉₊ = (L + 1) / 2 := by
  by_cases hL : L = 0
  · subst L
    norm_num
  apply (Nat.ceil_eq_iff (show (L + 1) / 2 ≠ 0 by omega)).mpr
  constructor
  · apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    exact_mod_cast (show ((L + 1) / 2 - 1) * 2 < L by omega)
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    exact_mod_cast (show L ≤ (L + 1) / 2 * 2 by omega)

/-- Continuity extends a family of exponential-rate limits to every sequence
with the same normalized logarithmic rate. The only order input is antitonicity
of the finite-block exponent as the message parameter increases. -/
theorem rate_sequence_extension
    (F : ℕ → ℝ → ℝ) (E : ℝ → ℝ) {C r : ℝ}
    (hr : 0 < r) (hrC : r < C)
    (hmono : ∀ k, AntitoneOn (F k) (Set.Ioi 1))
    (hExp : ∀ s, 0 < s → s < C →
      Filter.Tendsto (fun k : ℕ => F k ((2 : ℝ) ^ ((k : ℝ) * s)))
        Filter.atTop (nhds (E s)))
    (hcont : ContinuousAt E r)
    (L : ℕ → ℝ) (hL : ∀ k, 1 ≤ L k)
    (hLim : Filter.Tendsto (fun k : ℕ => (1 / (k : ℝ)) * Real.logb 2 (L k))
      Filter.atTop (nhds r)) :
    Filter.Tendsto (fun k => F k (L k)) Filter.atTop (nhds (E r)) := by
  have bounds {s t : ℝ} (hs : 0 < s) (hsr : s < r) (hrt : r < t) :
      ∀ᶠ k : ℕ in Filter.atTop,
        1 < (2 : ℝ) ^ ((k : ℝ) * s) ∧
        (2 : ℝ) ^ ((k : ℝ) * s) ≤ L k ∧
        L k ≤ (2 : ℝ) ^ ((k : ℝ) * t) := by
    filter_upwards [hLim.eventually (Ioo_mem_nhds hsr hrt),
      Filter.eventually_gt_atTop 0] with k hk hk0
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk0
    have hLpos : 0 < L k := lt_of_lt_of_le zero_lt_one (hL k)
    refine ⟨Real.one_lt_rpow (by norm_num) (mul_pos hkpos hs), ?_, ?_⟩
    · apply (Real.le_logb_iff_rpow_le (by norm_num) hLpos).mp
      have hv : s ≤ Real.logb 2 (L k) / (k : ℝ) := by
        simpa only [one_div, mul_comm, div_eq_mul_inv, mul_one] using hk.1.le
      simpa only [mul_comm] using (le_div_iff₀ hkpos).mp hv
    · apply (Real.logb_le_iff_le_rpow (by norm_num) hLpos).mp
      have hv : Real.logb 2 (L k) / (k : ℝ) ≤ t := by
        simpa only [one_div, mul_comm, div_eq_mul_inv, mul_one] using hk.2.le
      simpa only [mul_comm] using (div_le_iff₀ hkpos).mp hv
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hcont (E r - a) (sub_pos.mpr ha)
    let u := min (δ / 2) ((C - r) / 2)
    have hu : 0 < u := lt_min (by linarith) (by linarith)
    have hud : u < δ := (min_le_left _ _).trans_lt (by linarith)
    have huC : u < C - r := (min_le_right _ _).trans_lt (by linarith)
    have hru0 : 0 < r + u := by linarith
    have hruC : r + u < C := by linarith
    have he : a < E (r + u) := by
      have hd : dist (r + u) r < δ := by rw [Real.dist_eq, abs_of_pos (by linarith)]; simpa using hud
      have hc := hclose hd
      rw [Real.dist_eq] at hc
      have := (abs_lt.mp hc).1
      linarith
    have hf := (hExp (r + u) hru0 hruC).eventually (lt_mem_nhds he)
    have hb := bounds (half_pos hr) (by linarith : r / 2 < r) (by linarith : r < r + u)
    filter_upwards [hf, hb] with k hk hb
    exact hk.trans_le (hmono k (lt_of_lt_of_le hb.1 hb.2.1)
      (lt_of_lt_of_le hb.1 (hb.2.1.trans hb.2.2)) hb.2.2)
  · intro b hb
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hcont (b - E r) (sub_pos.mpr hb)
    let u := min (δ / 2) (r / 2)
    have hu : 0 < u := lt_min (by linarith) (half_pos hr)
    have hud : u < δ := (min_le_left _ _).trans_lt (by linarith)
    have hur : u < r := (min_le_right _ _).trans_lt (by linarith)
    have hru0 : 0 < r - u := by linarith
    have hruC : r - u < C := by linarith
    have he : E (r - u) < b := by
      have hd : dist (r - u) r < δ := by
        rw [Real.dist_eq, abs_of_neg (by linarith)]
        linarith
      have hc := hclose hd
      rw [Real.dist_eq] at hc
      have := (abs_lt.mp hc).2
      linarith
    have hf := (hExp (r - u) hru0 hruC).eventually (gt_mem_nhds he)
    have hbnd := bounds hru0 (by linarith : r - u < r) (by linarith : r < C)
    filter_upwards [hf, hbnd] with k hk hbd
    exact lt_of_le_of_lt (hmono k hbd.1
      (lt_of_lt_of_le hbd.1 hbd.2.1) hbd.2.1) hk

end Paper22
end
