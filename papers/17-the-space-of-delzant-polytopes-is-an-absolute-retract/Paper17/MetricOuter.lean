import Paper17.MetricInterior

/-! A fixed interior ball and small symmetric difference force a uniform outer radius. -/
noncomputable section
open scoped Topology BigOperators symmDiff
open Set Metric MeasureTheory
namespace Paper17

/-- A distant point of a convex set containing an inner ball creates a fixed-radius
ball outside a prescribed bounded set. -/
theorem exists_ball_outside_of_distant_point {n : ℕ} {K L : Set (V n)}
    (hcL : Convex ℝ L) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hinL : Metric.ball (0 : V n) r ⊆ L) (houtK : K ⊆ Metric.ball (0 : V n) R)
    {x : V n} (hx : x ∈ L) (hfar : 2 * R + r ≤ ‖x‖) :
    ∃ c : V n, Metric.ball c (r / 2) ⊆ L \ K := by
  let c := (1 / 2 : ℝ) • x
  have hcnorm : ‖c‖ = ‖x‖ / 2 := by simp [c, norm_smul]; ring
  refine ⟨c, ?_⟩
  intro z hz
  have hzc : dist z c < r / 2 := hz
  let y := (2 : ℝ) • (z - c)
  have hynorm : ‖y‖ < r := by
    change ‖(2 : ℝ) • (z - c)‖ < r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [dist_eq_norm] at hzc
    linarith
  have hzrep : z = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y := by
    dsimp [y, c]
    rw [smul_smul]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [hzrep]
    exact hcL hx (hinL (mem_ball_zero_iff.mpr hynorm)) (by norm_num) (by norm_num) (by norm_num)
  · intro hzK
    have hzR : ‖z‖ < R := mem_ball_zero_iff.mp (houtK hzK)
    have hh := dist_triangle c z 0
    rw [dist_zero_right, dist_zero_right, dist_comm c z, hcnorm] at hh
    linarith

/-- A small symmetric difference and a common inner ball forbid distant points.
Only a fixed ball volume is needed, without a cone-volume formula. -/
theorem outer_ball_of_small_symmDiffVol {n : ℕ} {K L : Set (V n)}
    (hK : IsCompact K) (hL : IsCompact L) (hcL : Convex ℝ L)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hinL : Metric.ball (0 : V n) r ⊆ L) (houtK : K ⊆ Metric.ball (0 : V n) R)
    (hsmall : symmDiffVol K L < r ^ n) : L ⊆ Metric.ball (0 : V n) (2 * R + r) := by
  intro x hx
  rw [mem_ball_zero_iff]
  by_contra! hfar
  obtain ⟨c, hc⟩ := exists_ball_outside_of_distant_point hcL hr hR hinL houtK hx hfar
  have hsub : Metric.ball c (r / 2) ⊆ K ∆ L := fun z hz => Or.inr (hc hz)
  have hmono : volume (Metric.ball c (r / 2)) ≤ volume (K ∆ L) := measure_mono hsub
  have hfin := volume_symmDiff_ne_top_of_isCompact hK hL
  have hreal : (volume (Metric.ball c (r / 2))).toReal ≤ symmDiffVol K L :=
    (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hfin hmono) hfin).mpr hmono
  rw [Real.volume_pi_ball c (by positivity), Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have heq : 2 * (r / 2) = r := by ring
  rw [heq] at hreal
  exact (not_lt_of_ge hreal) hsmall

end Paper17
