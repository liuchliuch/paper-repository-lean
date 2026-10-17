import Paper17.MetricLower

/-! Uniform interior-ball control from a small symmetric difference (Proposition 2.5). -/
noncomputable section
open scoped Topology BigOperators symmDiff
open Set Metric MeasureTheory
namespace Paper17

/-- If the smaller concentric ball is not contained in `L`, separation produces
an actual fixed-radius ball in `K \ L`. This avoids a postulated cap-volume bound. -/
theorem exists_ball_in_difference_of_missing_inner_ball {n : ℕ} {K L : Set (V n)}
    (hL : IsCompact L) (hneL : L.Nonempty) (hcL : Convex ℝ L)
    {r : ℝ} (hr : 0 < r) (hinK : Metric.ball (0 : V n) r ⊆ K)
    (hnot : ¬ Metric.ball (0 : V n) (r / 2) ⊆ L) :
    ∃ c : V n, Metric.ball c (r / 8) ⊆ K \ L := by
  classical
  obtain ⟨z, hz, hzL⟩ := Set.not_subset.mp hnot
  have hznorm : ‖z‖ < r / 2 := mem_ball_zero_iff.mp hz
  obtain ⟨f, t, hfl, hfz⟩ := geometric_hahn_banach_closed_point hcL hL.isClosed hzL
  obtain ⟨u, hu⟩ := exists_forall_eq_dot (f : V n →L[ℝ] ℝ).toLinearMap
  have hsep : ∀ x ∈ L, dot u x < dot u z := by
    intro x hx
    have hh := (hfl x hx).trans hfz
    change (f : V n →L[ℝ] ℝ).toLinearMap x < (f : V n →L[ℝ] ℝ).toLinearMap z at hh
    rwa [hu x, hu z] at hh
  let S : ℝ := ∑ i, |u i|
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hSpos : 0 < S := by
    by_contra! hn
    have hS : S = 0 := le_antisymm hn hS0
    have hu0 : u = 0 := by
      ext i
      have hi : |u i| ≤ S := Finset.single_le_sum (fun j _ => abs_nonneg (u j)) (Finset.mem_univ i)
      simpa only [hS, abs_nonpos_iff, Pi.zero_apply] using hi
    obtain ⟨x, hx⟩ := hneL
    have hh := hsep x hx
    simpa [hu0, dot] using hh
  let c : V n := fun i => if 0 ≤ u i then 3 * r / 4 else -(3 * r / 4)
  have hcnorm : ‖c‖ ≤ 3 * r / 4 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    dsimp [c]
    split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ 3 * r / 4 by positivity)]
  have hcdot : dot u c = (3 * r / 4) * S := by
    change (∑ i, u i * c i) = _
    rw [show (3 * r / 4) * S = ∑ i, (3 * r / 4) * |u i| by rw [← Finset.mul_sum]]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [c]
    split_ifs with hi
    · rw [abs_of_nonneg hi, mul_comm]
    · rw [abs_of_neg (lt_of_not_ge hi)]
      ring
  refine ⟨c, ?_⟩
  intro y hy
  have hydist : dist y c < r / 8 := hy
  have hynorm : ‖y‖ < r := by
    have hh := dist_triangle y c 0
    rw [dist_zero_right, dist_zero_right] at hh
    linarith
  have hdotz : dot u z < (r / 2) * S := by
    calc dot u z ≤ |dot u z| := le_abs_self _
      _ ≤ S * ‖z‖ := abs_dot_le_sum_abs_mul_norm u z
      _ < S * (r / 2) := mul_lt_mul_of_pos_left hznorm hSpos
      _ = (r / 2) * S := mul_comm _ _
  have hdotdiff : dot u c - dot u y ≤ S * (r / 8) := by
    have hdot : dot u (c - y) = dot u c - dot u y := by
      simp [dot, mul_sub, Finset.sum_sub_distrib]
    rw [← hdot]
    calc dot u (c - y) ≤ |dot u (c - y)| := le_abs_self _
      _ ≤ S * ‖c - y‖ := abs_dot_le_sum_abs_mul_norm u (c - y)
      _ ≤ S * (r / 8) := mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm, norm_sub_rev] using hydist.le) hS0
  have hdoty : dot u z < dot u y := by
    rw [hcdot] at hdotdiff
    nlinarith [mul_pos hr hSpos]
  exact ⟨hinK (mem_ball_zero_iff.mpr hynorm), fun hyL => (hsep y hyL).not_ge hdoty.le⟩

/-- Small symmetric difference forces a fixed interior ball, uniformly in `L`. -/
theorem inner_ball_of_small_symmDiffVol {n : ℕ} {K L : Set (V n)}
    (hK : IsCompact K) (hL : IsCompact L) (hneL : L.Nonempty) (hcL : Convex ℝ L)
    {r : ℝ} (hr : 0 < r) (hinK : Metric.ball (0 : V n) r ⊆ K)
    (hsmall : symmDiffVol K L < (r / 4) ^ n) : Metric.ball (0 : V n) (r / 2) ⊆ L := by
  by_contra hn
  obtain ⟨c, hc⟩ := exists_ball_in_difference_of_missing_inner_ball hL hneL hcL hr hinK hn
  have hsub : Metric.ball c (r / 8) ⊆ K ∆ L := fun x hx => Or.inl (hc hx)
  have hmono : volume (Metric.ball c (r / 8)) ≤ volume (K ∆ L) := measure_mono hsub
  have hfin := volume_symmDiff_ne_top_of_isCompact hK hL
  have hreal : (volume (Metric.ball c (r / 8))).toReal ≤ symmDiffVol K L :=
    (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hfin hmono) hfin).mpr hmono
  rw [Real.volume_pi_ball c (by positivity), Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have heq : 2 * (r / 8) = r / 4 := by ring
  rw [heq] at hreal
  exact (not_lt_of_ge hreal) hsmall

end Paper17
