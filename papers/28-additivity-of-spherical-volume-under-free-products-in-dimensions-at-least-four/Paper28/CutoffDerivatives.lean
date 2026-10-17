import Paper28.NormalizedCutoffs
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Actual cutoff derivatives, including their zero-support behavior and
the locally finite sum of their operator norms. This supplies the finite
C0 constant independently of the later projection precision. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Metric
open scoped Topology
variable {G J : Type*} [Group G] [DecidableEq G] [Fintype J]
variable (c : J → CoordinateHilbert G) [∀ j, Fintype (regularStabilizer (c j))]
variable (b : ∀ j, ContDiffBump (c j))

def cutoffDerivative (i : J×G) (u : CoordinateHilbert G) : CoordinateHilbert G →L[ℝ] ℝ :=
  fderiv ℝ (normalizedCutoff c b i) u

def cutoffGradientSum (u : CoordinateHilbert G) : ℝ := ∑' i : J×G, ‖cutoffDerivative c b i u‖

/-- The derivative vanishes at a zero cutoff because every normalized
cutoff is globally nonnegative, even before a positive denominator is selected. -/
theorem cutoffDerivative_zero (i : J×G) (u : CoordinateHilbert G)
    (hβ : translatedCutoff c b i u = 0) : cutoffDerivative c b i u = 0 := by
  have hz : normalizedCutoff c b i u = 0 := by simp only [normalizedCutoff,hβ,zero_div]
  have hm : IsLocalMin (normalizedCutoff c b i) u := by
    apply Filter.Eventually.of_forall
    intro v
    rw [hz]
    exact normalizedCutoff_nonneg c b i v
  exact hm.fderiv_eq_zero

theorem cutoffDerivative_hasFDerivAt (hRadius : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hUnit : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (hD : 0 < cutoffDenominator c b u) (i : J×G) :
    HasFDerivAt (normalizedCutoff c b i) (cutoffDerivative c b i u) u :=
  (normalizedCutoff_contDiffAt c b hRadius hUnit u hu hD i 1).differentiableAt_one.hasFDerivAt

theorem cutoffDerivative_continuousAt (hRadius : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hUnit : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (hD : 0 < cutoffDenominator c b u) (i : J×G) :
    ContinuousAt (cutoffDerivative c b i) u :=
  ((normalizedCutoff_contDiffAt c b hRadius hUnit u hu hD i 1).fderiv_right
    (m := 0) (by norm_num)).continuousAt

theorem cutoffGradientSum_eq_sum (s : Finset (J×G)) (u : CoordinateHilbert G)
    (hzero : ∀ i ∉ s, translatedCutoff c b i u = 0) :
    cutoffGradientSum c b u = ∑ i ∈ s, ‖cutoffDerivative c b i u‖ :=
  (hasSum_sum_of_ne_finset_zero (fun i hi => by rw [cutoffDerivative_zero c b i u (hzero i hi),norm_zero])).tsum_eq

theorem cutoffGradientSum_nonneg (u : CoordinateHilbert G) : 0 ≤ cutoffGradientSum c b u :=
  tsum_nonneg (fun _ => norm_nonneg _)

theorem cutoffGradientSum_continuousAt (hRadius : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hUnit : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (hD : 0 < cutoffDenominator c b u) : ContinuousAt (cutoffGradientSum c b) u := by
  obtain ⟨s,hs⟩ := translatedCutoff_local_finite c b hRadius hUnit u hu
  have hEq : cutoffGradientSum c b =ᶠ[𝓝 u] (fun v => ∑ i ∈ s, ‖cutoffDerivative c b i v‖) := by
    filter_upwards [ball_mem_nhds u (by norm_num : (0 : ℝ) < 1/2)] with v hv
    exact cutoffGradientSum_eq_sum c b s v (fun i hi => hs v
      (by simpa only [mem_ball,dist_comm] using hv) i hi)
  have hf : ContinuousAt (fun v => ∑ i ∈ s, ‖cutoffDerivative c b i v‖) u :=
    tendsto_finset_sum s (fun i _ => (cutoffDerivative_continuousAt c b hRadius hUnit u hu hD i).norm)
  exact hf.congr_of_eventuallyEq hEq

end Paper28
