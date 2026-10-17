import Paper28.ChordAngularComparison

/-! Actual joint smoothness yields a local round angular estimate for
normalized homotopies, including the time variable. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Metric
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem exists_local_homotopy_angular_bound (f : ℝ → H → H) (t : ℝ) (u : H)
    (hf : ContDiffAt ℝ 1 (fun p : ℝ×H => f p.1 p.2) (t,u)) :
    ∃ B : ℝ, 0 < B ∧ ∃ r : ℝ, 0 < r ∧ ∀ s z : ℝ, ∀ v w : H,
      dist s t < r → dist z t < r → dist v u < r → dist w u < r →
      ‖v‖ = 1 → ‖w‖ = 1 → ‖f s v‖ = 1 → ‖f z w‖ = 1 →
      angular (f s v) (f z w) ≤ B*(dist s z+angular v w) := by
  obtain ⟨K,S,hS,hLip⟩ := (hf.hasStrictFDerivAt le_rfl).exists_lipschitzOnWith
  obtain ⟨r0,hr0,hrS⟩ := Metric.mem_nhds_iff.mp hS
  obtain ⟨a,ha,hAngle⟩ := exists_angular_le_mul_chord (H := H) 2 (by norm_num)
  let b := (K : ℝ)+1
  have hb : 0 < b := by dsimp [b]; positivity
  let r := min r0 (a/(4*b))
  have hr : 0 < r := lt_min hr0 (by positivity)
  refine ⟨2*b,by positivity,r,hr,?_⟩
  intro s z v w hs hz hv hw hvU hwU hvF hwF
  have hsv : dist (s,v) (t,u) < r := max_lt hs hv
  have hzw : dist (z,w) (t,u) < r := max_lt hz hw
  have hsS : (s,v) ∈ S := hrS (hsv.trans_le (min_le_left _ _))
  have hzS : (z,w) ∈ S := hrS (hzw.trans_le (min_le_left _ _))
  have hL : ‖f s v-f z w‖ ≤ b*dist (s,v) (z,w) := by
    have h := hLip.dist_le_mul (s,v) hsS (z,w) hzS
    rw [dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by dsimp [b]; linarith : (K : ℝ) ≤ b) dist_nonneg)
  have hd : dist (s,v) (z,w) < 2*r := by
    have h := dist_triangle (s,v) (t,u) (z,w)
    rw [dist_comm (t,u) (z,w)] at h
    linarith
  have har : 4*b*r ≤ a := by
    simpa only [r,mul_comm] using
      (le_div_iff₀ (by positivity : 0 < 4*b)).mp (min_le_right r0 (a/(4*b)))
  have hfClose : ‖f s v-f z w‖ < a := by nlinarith
  have hprod : dist (s,v) (z,w) ≤ dist s z+angular v w := by
    rw [Prod.dist_eq]
    apply max_le
    · exact le_add_of_nonneg_right (Real.arccos_nonneg _)
    · have h := chord_le_angular v w hvU hwU
      rw [dist_eq_norm]
      exact h.trans (le_add_of_nonneg_left dist_nonneg)
  calc
    _ ≤ 2*‖f s v-f z w‖ := hAngle _ _ hvF hwF hfClose
    _ ≤ 2*(b*dist (s,v) (z,w)) := mul_le_mul_of_nonneg_left hL (by norm_num)
    _ ≤ (2*b)*(dist s z+angular v w) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hprod (by positivity)

end Paper28
