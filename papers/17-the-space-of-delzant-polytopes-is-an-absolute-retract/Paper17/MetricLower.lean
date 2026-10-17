import Paper17.MetricCompare
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! Geometric ball inside a symmetric difference, the lower estimate in Proposition 2.5. -/
noncomputable section
open scoped Topology BigOperators Pointwise symmDiff ENNReal
open Set Metric MeasureTheory
namespace Paper17

/-- The norm of a difference of support functions is attained on the compact dual ball. -/
theorem support_gap_realized {n : ℕ} (K L : PosBody n) :
    ∃ u : dualUnitBall n,
      supportFunction K.carrier u.val - supportFunction L.carrier u.val =
          Metric.hausdorffDist K.carrier L.carrier ∨
      supportFunction L.carrier u.val - supportFunction K.carrier u.val =
          Metric.hausdorffDist K.carrier L.carrier := by
  let f := supportMap K - supportMap L
  haveI : Nonempty (dualUnitBall n) := ⟨⟨0, by simp [dualUnitBall]⟩⟩
  obtain ⟨u, hu, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_norm.comp f.continuous).continuousOn
  have hnorm : ‖f‖ = ‖f u‖ := le_antisymm
    ((ContinuousMap.norm_le f (norm_nonneg _)).mpr (fun v => hmax (Set.mem_univ v)))
    (f.norm_coe_le_norm u)
  have hgap : |supportFunction K.carrier u.val - supportFunction L.carrier u.val| =
      Metric.hausdorffDist K.carrier L.carrier := by
    rw [← dist_supportMap, dist_eq_norm, hnorm]
    rfl
  refine ⟨u, ?_⟩
  rcases le_or_gt 0 (supportFunction K.carrier u.val - supportFunction L.carrier u.val) with h | h
  · exact Or.inl (by rwa [abs_of_nonneg h] at hgap)
  · exact Or.inr (by rw [abs_of_neg h] at hgap; linarith)

/-- A support gap supplies a ball of the paper's specified radius in `K \ L`. -/
theorem ball_in_difference_of_support_gap {n : ℕ} {K L : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) (hconv : Convex ℝ K)
    (hL : IsCompact L) {r R δ : ℝ} (hr : 0 < r) (hR : 0 < R) (hδ : 0 < δ)
    (hδR : δ ≤ 2 * R) (hin : Metric.ball (0 : V n) r ⊆ K)
    (hout : K ⊆ Metric.ball (0 : V n) R) (u : dualUnitBall n)
    (hgap : supportFunction K u.val - supportFunction L u.val = δ) :
    ∃ c : V n, Metric.ball c (r * δ / (2 * (R + r))) ⊆ K \ L := by
  let tScale := δ / (2 * (R + r))
  have hden : 0 < 2 * (R + r) := by positivity
  have htScale : 0 < tScale := div_pos hδ hden
  have htScale1 : tScale < 1 := (div_lt_one hden).mpr (by linarith)
  have htScaleeq : tScale * (R + r) = δ / 2 := by dsimp [tScale]; field_simp
  obtain ⟨x, hx, hsup⟩ := exists_mem_eq_supportFunction hK hneK u.val
  have hpair : ∀ z : V n, ‖z‖ ≤ R → dot u.val z ≤ R := by
    intro z hz
    calc dot u.val z ≤ |dot u.val z| := le_abs_self _
      _ ≤ (∑ i, |u.val i|) * ‖z‖ := abs_dot_le_sum_abs_mul_norm _ _
      _ ≤ 1 * R := mul_le_mul u.property hz (norm_nonneg _) (by positivity)
      _ = R := one_mul R
  have hxR : dot u.val x ≤ R := hpair x ((mem_ball_zero_iff.mp (hout hx)).le)
  let c := (1 - tScale) • x
  refine ⟨c, ?_⟩
  intro z hz
  have hdist : ‖z - c‖ < tScale * r := by
    have heq : r * δ / (2 * (R + r)) = tScale * r := by dsimp [tScale]; ring
    simpa only [Metric.mem_ball, dist_eq_norm, heq] using hz
  let y := tScale⁻¹ • (z - c)
  have hyr : ‖y‖ < r := by
    have hh := mul_lt_mul_of_pos_left hdist (inv_pos.mpr htScale)
    have heq : tScale⁻¹ * (tScale * r) = r := by rw [← mul_assoc, inv_mul_cancel₀ htScale.ne', one_mul]
    rw [heq] at hh
    simpa only [y, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htScale)] using hh
  have hy : y ∈ Metric.ball (0 : V n) r := mem_ball_zero_iff.mpr hyr
  have hzrep : z = (1 - tScale) • x + tScale • y := by
    dsimp [y, c]
    rw [smul_smul, mul_inv_cancel₀ htScale.ne', one_smul, add_sub_cancel]
  have hybound : -r ≤ dot u.val y := by
    have habs : |dot u.val y| ≤ r := (abs_dot_le_sum_abs_mul_norm _ _).trans
      (by simpa only [one_mul] using mul_le_mul (show (∑ i, |u.val i|) ≤ 1 from u.property) hyr.le (norm_nonneg y) (by norm_num : (0:ℝ) ≤ 1))
    exact (abs_le.mp habs).1
  have houtside : supportFunction L u.val < dot u.val z := by
    rw [hzrep, dot_add_right, dot_smul_right, dot_smul_right]
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [hzrep]
    exact hconv hx (hin hy) (by linarith) htScale.le (by ring)
  · intro hzL
    exact (not_lt_of_ge (supportFunction_ub (u := u.val) hL hzL)) houtside

/-- Hausdorff distance is at most twice a common outer radius. -/
theorem hausdorffDist_le_twice_radius {n : ℕ} {K L : Set (V n)}
    (hneK : K.Nonempty) (hneL : L.Nonempty) {R : ℝ} (hR : 0 < R)
    (hK : K ⊆ Metric.ball (0 : V n) R) (hL : L ⊆ Metric.ball (0 : V n) R) :
    Metric.hausdorffDist K L ≤ 2 * R := by
  obtain ⟨x, hx⟩ := hneK
  obtain ⟨y, hy⟩ := hneL
  apply Metric.hausdorffDist_le_of_mem_dist (by positivity)
  · intro z hz
    exact ⟨y, hy, (dist_triangle z 0 y).trans (by
      have h1 := (Metric.mem_ball.mp (hK hz)).le
      have h2 := (Metric.mem_ball.mp (hL hy)).le
      rw [dist_comm 0 y]
      linarith)⟩
  · intro z hz
    exact ⟨x, hx, (dist_triangle z 0 x).trans (by
      have h1 := (Metric.mem_ball.mp (hL hz)).le
      have h2 := (Metric.mem_ball.mp (hK hx)).le
      rw [dist_comm 0 x]
      linarith)⟩

/-- The lower-volume estimate of Proposition 2.5, with the source's `n ≥ 1`. -/
theorem symmDiffVol_ball_inside_estimate {n : ℕ} (hn : 1 ≤ n)
    {K L : Set (V n)} (hK : IsCompact K) (hneK : K.Nonempty) (hcK : Convex ℝ K)
    (hL : IsCompact L) (hneL : L.Nonempty) (hcL : Convex ℝ L)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hinK : Metric.ball (0 : V n) r ⊆ K) (hinL : Metric.ball (0 : V n) r ⊆ L)
    (houtK : K ⊆ Metric.ball (0 : V n) R) (houtL : L ⊆ Metric.ball (0 : V n) R) :
    kappa n * (r * Metric.hausdorffDist K L / (2 * (R + r))) ^ n ≤ symmDiffVol K L := by
  let δ := Metric.hausdorffDist K L
  change kappa n * (r * δ / (2 * (R + r))) ^ n ≤ symmDiffVol K L
  by_cases hδ : δ = 0
  · simp only [hδ, mul_zero, zero_div, zero_pow (by omega : n ≠ 0), mul_zero]
    exact symmDiffVol_nonneg _ _
  have hδpos : 0 < δ := lt_of_le_of_ne Metric.hausdorffDist_nonneg (Ne.symm hδ)
  have hinterK : (interior K).Nonempty :=
    ⟨0, interior_maximal hinK Metric.isOpen_ball (Metric.mem_ball_self hr)⟩
  have hinterL : (interior L).Nonempty :=
    ⟨0, interior_maximal hinL Metric.isOpen_ball (Metric.mem_ball_self hr)⟩
  let KB : PosBody n := ⟨K, hcK, hK, hinterK⟩
  let LB : PosBody n := ⟨L, hcL, hL, hinterL⟩
  obtain ⟨u, hu⟩ := support_gap_realized KB LB
  have hδR : δ ≤ 2 * R := hausdorffDist_le_twice_radius hneK hneL hR houtK houtL
  have hball : ∃ c : V n, Metric.ball c (r * δ / (2 * (R + r))) ⊆ K ∆ L := by
    rcases hu with hgap | hgap
    · obtain ⟨c, hc⟩ := ball_in_difference_of_support_gap hK hneK hcK hL hr hR hδpos
        hδR hinK houtK u hgap
      exact ⟨c, hc.trans (fun z hz => Or.inl hz)⟩
    · obtain ⟨c, hc⟩ := ball_in_difference_of_support_gap hL hneL hcL hK hr hR hδpos
        hδR hinL houtL u (by simpa only [Metric.hausdorffDist_comm] using hgap)
      exact ⟨c, hc.trans (fun z hz => Or.inr hz)⟩
  obtain ⟨c, hc⟩ := hball
  have hρ : 0 < r * δ / (2 * (R + r)) := by positivity
  have hvol : (volume (Metric.ball c (r * δ / (2 * (R + r))))).toReal ≤ symmDiffVol K L :=
    (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top (volume_symmDiff_ne_top_of_isCompact hK hL) (measure_mono hc))
      (volume_symmDiff_ne_top_of_isCompact hK hL)).mpr (measure_mono hc)
  rw [Real.volume_pi_ball c hρ, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)] at hvol
  have hk : kappa n = (2 : ℝ) ^ n := by
    unfold kappa
    rw [Real.volume_pi_ball _ (by norm_num), Fintype.card_fin]
    norm_num
  rw [hk]
  simpa only [mul_pow] using hvol

end Paper17
