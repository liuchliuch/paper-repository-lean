import Paper28.ChordAngularComparison

/-! A sharp differential estimate for an actual smooth Hilbert map implies
the required local round-sphere estimate, with explicitly arbitrary slack. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Metric
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem exists_local_angular_bound (f : H → H) (u : H)
    (D : H →L[ℝ] H) (hf : ContDiffAt ℝ 1 f u) (hD : HasFDerivAt f D u)
    (b k : ℝ) (hb : 0 < b) (hDb : ‖D‖ < b) (hk : 1 < k) :
    ∃ r : ℝ, 0 < r ∧ ∀ v w : H,
      dist v u < r → dist w u < r → ‖v‖ = 1 → ‖w‖ = 1 →
      ‖f v‖ = 1 → ‖f w‖ = 1 → angular (f v) (f w) ≤ (k*b)*angular v w := by
  let B : NNReal := ⟨b,hb.le⟩
  have hDB : ‖D‖₊ < B := hDb
  obtain ⟨s,hs,hLip⟩ := (hf.hasStrictFDerivAt' hD le_rfl).exists_lipschitzOnWith_of_nnnorm_lt B hDB
  obtain ⟨r0,hr0,hrS⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨a,ha,hAngle⟩ := exists_angular_le_mul_chord (H := H) k hk
  let r := min r0 (a/(4*b))
  have hr : 0 < r := lt_min hr0 (by positivity)
  refine ⟨r,hr,?_⟩
  intro v w hv hw hvU hwU hvF hwF
  have hvS : v ∈ s := hrS ((hv.trans_le (min_le_left _ _)))
  have hwS : w ∈ s := hrS ((hw.trans_le (min_le_left _ _)))
  have hL : ‖f v-f w‖ ≤ b*‖v-w‖ := by
    simpa only [dist_eq_norm,B] using hLip.dist_le_mul v hvS w hwS
  have hdist : ‖v-w‖ < 2*r := by
    have h := dist_triangle v u w
    rw [dist_comm u w] at h
    rw [← dist_eq_norm]
    linarith
  have har : 4*b*r ≤ a := by
    simpa only [r,mul_comm] using
      (le_div_iff₀ (by positivity : 0 < 4*b)).mp (min_le_right r0 (a/(4*b)))
  have hfClose : ‖f v-f w‖ < a := by
    nlinarith
  calc
    angular (f v) (f w) ≤ k*‖f v-f w‖ := hAngle _ _ hvF hwF hfClose
    _ ≤ k*(b*‖v-w‖) := mul_le_mul_of_nonneg_left hL (by linarith)
    _ ≤ (k*b)*angular v w := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (chord_le_angular v w hvU hwU) (by positivity)

theorem exists_local_sharp_angular_bound (f : H → H) (u : H)
    (D : H →L[ℝ] H) (hf : ContDiffAt ℝ 1 f u) (hD : HasFDerivAt f D u)
    (L : ℝ) (hDL : ‖D‖ < L) :
    ∃ r : ℝ, 0 < r ∧ ∀ v w : H,
      dist v u < r → dist w u < r → ‖v‖ = 1 → ‖w‖ = 1 →
      ‖f v‖ = 1 → ‖f w‖ = 1 → angular (f v) (f w) ≤ L*angular v w := by
  let b := (‖D‖+L)/2
  have hb : 0 < b := by dsimp [b]; linarith [norm_nonneg D]
  have hDb : ‖D‖ < b := by dsimp [b]; linarith
  have hbL : b < L := by dsimp [b]; linarith
  have hk : 1 < L/b := (one_lt_div hb).mpr hbL
  obtain ⟨r,hr,h⟩ := exists_local_angular_bound f u D hf hD b (L/b) hb hDb hk
  refine ⟨r,hr,?_⟩
  intro v w hv hw hvU hwU hvF hwF
  simpa only [div_mul_cancel₀ L (ne_of_gt hb)] using h v w hv hw hvU hwU hvF hwF

end Paper28
