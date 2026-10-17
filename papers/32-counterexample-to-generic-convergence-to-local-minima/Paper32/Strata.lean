import Paper32.VariationalBridge

open Set Filter Topology
namespace Paper32

/-- The exact horizontal-axis Fréchet value in equation (3.10). -/
theorem frechet_g_horizontal_axis_exact {x : ℝ} (hx : x ≠ 0) :
    frechetSubdiff g (x,0) = {Real.sign x} ×ˢ Icc (-2 : ℝ) 2 := by
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨h1,h2⟩ := frechet_g_active_p hw (z := (x,0)) (by simp) hx
    exact ⟨h1,abs_le.mp h2⟩
  · rintro w ⟨h1,h2⟩
    change w.1 = Real.sign x at h1
    have hs := frechet_g_horizontal_axis hx (η := w.2) (abs_le.mpr h2)
    have he : (Real.sign x,w.2) = w := Prod.ext h1.symm rfl
    rwa [he] at hs

/-- The exact vertical-axis Fréchet value in equation (3.11). -/
theorem frechet_g_vertical_axis_exact {y : ℝ} (hy : y ≠ 0) :
    frechetSubdiff g (0,y) = Icc (-7 : ℝ) 7 ×ˢ {-Real.sign y} := by
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨h1,h2⟩ := frechet_g_active_q hw (z := (0,y)) (by simp) hy
    exact ⟨abs_le.mp h1,h2⟩
  · rintro w ⟨h1,h2⟩
    change w.2 = -Real.sign y at h2
    have hs := frechet_g_vertical_axis hy (ξ := w.1) (abs_le.mpr h1)
    have he : (w.1,-Real.sign y) = w := Prod.ext rfl h2.symm
    rwa [he] at hs

lemma frechet_g_active_p_y {z w : Point} (hw : FrechetSubgradient g z w)
    (hz : |z.2| ≤ 2*|z.1|) (hy : z.2 ≠ 0) : w.2 = 2*Real.sign z.2 := by
  apply frechet_y_eq hw (abs_pos.mpr hy)
  intro t ht
  calc
    g (z+(0,t)) ≤ |z.1|+2*|z.2+t| := by
      simpa only [add_zero] using g_le_p_xy z 0 t
    _ = g z + (2*Real.sign z.2)*t := by
      rw [g_horizontal hz,abs_add_small hy ht]
      ring

lemma frechet_g_active_q_x {z w : Point} (hw : FrechetSubgradient g z w)
    (hz : 2*|z.1| ≤ |z.2|) (hx : z.1 ≠ 0) : w.1 = 7*Real.sign z.1 := by
  apply frechet_x_eq hw (abs_pos.mpr hx)
  intro t ht
  calc
    g (z+(t,0)) ≤ 7*|z.1+t|-|z.2| := by
      simpa only [add_zero] using g_le_q_xy z t 0
    _ = g z + (7*Real.sign z.1)*t := by
      rw [g_vertical hz,abs_add_small hx ht]
      ring

/-- On every nonzero branch-boundary ray the regular subdifferential is empty. -/
theorem frechet_g_boundary_empty {z : Point} (hz : z ≠ 0)
    (hb : |z.2| = 2*|z.1|) : frechetSubdiff g z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hy : z.2 ≠ 0 := by
    intro hy
    have hx : z.1 = 0 := abs_eq_zero.mp (by rw [hy,abs_zero] at hb; linarith)
    exact hz (Prod.ext hx hy)
  have hp := frechet_g_active_p_y hw hb.le hy
  have hq := (frechet_g_active_q hw hb.symm.le hy).2
  have hs : Real.sign z.2 = 0 := by linarith
  have hn := abs_sign_of_ne hy
  rw [hs] at hn
  norm_num at hn

/-- On each open sector the regular subdifferential consists of the actual gradient. -/
theorem frechet_g_off_singular {z : Point} (hx : z.1 ≠ 0) (hy : z.2 ≠ 0)
    (hb : |z.2| ≠ 2*|z.1|) : frechetSubdiff g z = {gradCore z} := by
  apply Set.Subset.antisymm
  · intro w hw
    apply mem_singleton_iff.mpr
    by_cases hh : |z.2| < 2*|z.1|
    · have h1 := (frechet_g_active_p hw hh.le hx).1
      have h2 := frechet_g_active_p_y hw hh.le hy
      simpa only [gradCore,if_pos hh] using Prod.ext h1 h2
    · have hv : 2*|z.1| ≤ |z.2| := le_of_not_gt hh
      have h1 := frechet_g_active_q_x hw hv hx
      have h2 := (frechet_g_active_q hw hv hy).2
      simpa only [gradCore,if_neg hh] using Prod.ext h1 h2
  · intro w hw
    have he : w = gradCore z := mem_singleton_iff.mp hw
    rw [he]
    exact frechet_of_hasFDerivAt (hasFDerivAt_g hx hy hb)

/-- Local equality transfers the empty regular value to the coercive extension. -/
theorem frechet_F_zero_empty : frechetSubdiff F 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hlocal := (frechetSubgradient_congr_of_eventuallyEq
    (F_eventually_eq_core (z := 0) (by norm_num))).mp hw
  have hg := (frechet_add_const 8).mp hlocal
  have hmem : w ∈ frechetSubdiff g 0 := hg
  rw [frechet_g_zero_empty] at hmem
  exact hmem

/-- The concrete mismatch used in Corollary 3.3. The implication from standard
Clarke epigraph regularity to equality of the two subdifferentials is an external
variational-analysis theorem; this result establishes its contradictory conclusion. -/
theorem frechet_limiting_F_mismatch : frechetSubdiff F 0 ≠ limitingSubdiff F 0 := by
  intro h
  have hs : ((1,0) : Point) ∈ limitingSubdiff F 0 := by
    rw [limiting_F_zero]
    left
    norm_num
  rw [← h,frechet_F_zero_empty] at hs
  exact hs

end Paper32
