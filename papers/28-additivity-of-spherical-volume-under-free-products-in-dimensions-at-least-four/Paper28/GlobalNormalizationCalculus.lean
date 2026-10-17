import Paper28.GlobalProjectionCalculus

/-! Actual normalization of the global locally finite projection. Its
nonvanishing and sharp Frechet derivative bound are derived from the native
projection and cutoff estimates, including all inactive-weight cases. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Metric
open scoped Topology
variable {G J : Type*} [Group G] [DecidableEq G] [Fintype J]
variable (c : J → CoordinateHilbert G) [∀ j, Fintype (regularStabilizer (c j))]
variable (b : ∀ j, ContDiffBump (c j)) (F : J → Finset G)

theorem globalProjection_contDiffAt (hR : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hU : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (hD : 0 < cutoffDenominator c b u) (n : ℕ∞) : ContDiffAt ℝ n (globalProjection c b F) u := by
  obtain ⟨s,hs⟩ := translatedCutoff_local_finite c b hR hU u hu
  have hf : ContDiffAt ℝ n
      (fun v => ∑ i ∈ s, normalizedCutoff c b i v • translatedProjection F i v) u :=
    ContDiffAt.sum (fun i _ => (normalizedCutoff_contDiffAt c b hR hU u hu hD i n).smul
      (translatedProjection F i).contDiff.contDiffAt)
  apply hf.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds u (by norm_num : (0 : ℝ) < 1/2)] with v hv
  exact globalProjection_eq_sum c b F s v (fun i hi => hs v
    (by simpa only [mem_ball,dist_comm] using hv) i hi)

theorem globalProjection_norm_lower (hR : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hU : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (hD : 0 < cutoffDenominator c b u) (ε : ℝ) (hε : 0 ≤ ε)
    (hError : ∀ i, translatedCutoff c b i u ≠ 0 → ‖translatedProjection F i u-u‖ ≤ ε) :
    1-ε ≤ ‖globalProjection c b F u‖ := by
  obtain ⟨s,hs⟩ := translatedCutoff_local_finite c b hR hU u hu
  have he := globalProjection_error c b F u s (fun i hi => hs u (by simp) i hi) hD ε hε hError
  have hn := norm_sub_norm_le u (globalProjection c b F u)
  rw [hu,norm_sub_rev] at hn
  linarith

theorem globalProjection_ne_zero (hR : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hU : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (hD : 0 < cutoffDenominator c b u) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hError : ∀ i, translatedCutoff c b i u ≠ 0 → ‖translatedProjection F i u-u‖ ≤ ε) :
    globalProjection c b F u ≠ 0 := by
  have hn := globalProjection_norm_lower c b F hR hU u hu hD ε hε hError
  intro hz
  rw [hz,norm_zero] at hn
  linarith

theorem globalNormalizedProjection_norm (hR : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hU : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (hD : 0 < cutoffDenominator c b u) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hError : ∀ i, translatedCutoff c b i u ≠ 0 → ‖translatedProjection F i u-u‖ ≤ ε) :
    ‖globalNormalizedProjection c b F u‖ = 1 :=
  sphericalNormalize_norm _ (globalProjection_ne_zero c b F hR hU u hu hD ε hε hε1 hError)

/-- The constructed normalized map has an actual differential satisfying
the source's sharp constant (1+C0*epsilon)/(1-epsilon). -/
theorem globalNormalizedProjection_sharp_derivative (hR : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hU : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (hD : 0 < cutoffDenominator c b u) (ε C0 : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hGrad : cutoffGradientSum c b u ≤ C0)
    (hError : ∀ i, translatedCutoff c b i u ≠ 0 → ‖translatedProjection F i u-u‖ ≤ ε) :
    ∃ D : CoordinateHilbert G →L[ℝ] CoordinateHilbert G,
      HasFDerivAt (globalNormalizedProjection c b F) D u ∧
      ∀ h, ‖D h‖ ≤ ((1+C0*ε)/(1-ε))*‖h‖ := by
  obtain ⟨s,hs⟩ := translatedCutoff_local_finite c b hR hU u hu
  let DR := localGlobalProjectionDerivative c b F s u
  let D := (normalizationDerivative (globalProjection c b F u)).comp DR
  have hzero : ∀ i ∉ s, translatedCutoff c b i u = 0 := fun i hi => hs u (by simp) i hi
  have hRN := globalProjection_ne_zero c b F hR hU u hu hD ε hε hε1 hError
  refine ⟨D,(hasFDerivAt_sphericalNormalize (globalProjection c b F u) hRN).comp u
    (globalProjection_hasFDerivAt c b F hR hU u hu hD s hs),?_⟩
  intro h
  have hn := globalProjection_norm_lower c b F hR hU u hu hD ε hε hError
  have hd := localGlobalProjectionDerivative_norm c b F u h s hzero hD ε C0 hε hGrad hError
  have hC : 0 ≤ C0 := (cutoffGradientSum_nonneg c b u).trans hGrad
  have hNumer : 0 ≤ (1+C0*ε)*‖h‖ := by positivity
  change ‖normalizationDerivative (globalProjection c b F u) (DR h)‖ ≤ _
  calc
    _ ≤ ‖DR h‖/‖globalProjection c b F u‖ := normalizationDerivative_norm_le _ _
    _ ≤ ((1+C0*ε)*‖h‖)/‖globalProjection c b F u‖ := div_le_div_of_nonneg_right hd (norm_nonneg _)
    _ ≤ ((1+C0*ε)*‖h‖)/(1-ε) := div_le_div_of_nonneg_left hNumer (by linarith) hn
    _ = _ := by ring

end Paper28
