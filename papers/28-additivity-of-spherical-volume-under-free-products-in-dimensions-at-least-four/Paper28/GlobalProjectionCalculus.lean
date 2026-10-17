import Paper28.GlobalProjection
import Paper28.CutoffDerivatives
import Paper28.ActiveProjectionEstimates

/-! Actual local differentiation and sharp estimates for the constructed
infinite equivariant projection. Local finiteness reduces to the proved
finite weighted operator, with error conditions only on active cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Metric
open scoped Topology
variable {G J : Type*} [Group G] [DecidableEq G] [Fintype J]
variable (c : J → CoordinateHilbert G) [∀ j, Fintype (regularStabilizer (c j))]
variable (b : ∀ j, ContDiffBump (c j)) (F : J → Finset G)

def localProjectionWeights (s : Finset (J×G)) (i : s) : CoordinateHilbert G → ℝ :=
  normalizedCutoff c b i.val

def localProjectionWeightDerivative (s : Finset (J×G)) (i : s)
    (u : CoordinateHilbert G) : CoordinateHilbert G →L[ℝ] ℝ := cutoffDerivative c b i.val u

def localGlobalProjectionDerivative (s : Finset (J×G)) (u : CoordinateHilbert G) :
    CoordinateHilbert G →L[ℝ] CoordinateHilbert G :=
  weightedProjectionDerivative (localProjectionWeights c b s) (localProjectionWeightDerivative c b s)
    (fun i : s => translatedProjection F i.val) u

theorem globalProjection_eq_weighted (s : Finset (J×G)) (u : CoordinateHilbert G)
    (hzero : ∀ i ∉ s, translatedCutoff c b i u = 0) :
    globalProjection c b F u = weightedProjection (localProjectionWeights c b s)
      (fun i : s => translatedProjection F i.val) u := by
  rw [globalProjection_eq_sum c b F s u hzero]
  unfold weightedProjection localProjectionWeights
  exact (Finset.sum_coe_sort s (fun i : J×G => normalizedCutoff c b i u • translatedProjection F i u)).symm

theorem localProjectionWeights_sum (s : Finset (J×G)) (u : CoordinateHilbert G)
    (hzero : ∀ i ∉ s, translatedCutoff c b i u = 0) (hD : cutoffDenominator c b u ≠ 0) :
    (∑ i : s, localProjectionWeights c b s i u) = 1 := by
  unfold localProjectionWeights
  exact (Finset.sum_coe_sort s (fun i : J×G => normalizedCutoff c b i u)).trans
    (normalizedCutoff_sum c b s u hzero hD)

theorem localProjectionWeightDerivative_zero (s : Finset (J×G)) (u : CoordinateHilbert G)
    (i : s) (hi : localProjectionWeights c b s i u = 0) :
    localProjectionWeightDerivative c b s i u = 0 := by
  have hm : IsLocalMin (normalizedCutoff c b i.val) u := by
    apply Filter.Eventually.of_forall
    intro v
    rw [show normalizedCutoff c b i.val u = 0 from hi]
    exact normalizedCutoff_nonneg c b i.val v
  exact hm.fderiv_eq_zero

/-- The actual global R has the actual finite error-form derivative from
the local active index set. The local partition identity is derived here. -/
theorem globalProjection_hasFDerivAt (hR : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hU : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (hD : 0 < cutoffDenominator c b u) (s : Finset (J×G))
    (hs : ∀ v, dist u v < (1/2 : ℝ) → ∀ i ∉ s, translatedCutoff c b i v = 0) :
    HasFDerivAt (globalProjection c b F) (localGlobalProjectionDerivative c b F s u) u := by
  have hSum : (fun v => ∑ i : s, localProjectionWeights c b s i v) =ᶠ[𝓝 u] (fun _ => (1 : ℝ)) := by
    have hDP := (cutoffDenominator_contDiffAt c b hR hU u hu 0).continuousAt.eventually (Ioi_mem_nhds hD)
    filter_upwards [ball_mem_nhds u (by norm_num : (0 : ℝ) < 1/2),hDP] with v hv hDv
    exact localProjectionWeights_sum c b s v (fun i hi => hs v
      (by simpa only [mem_ball,dist_comm] using hv) i hi) (ne_of_gt hDv)
  have hFD := hasFDerivAt_weightedProjection (localProjectionWeights c b s)
    (localProjectionWeightDerivative c b s) (fun i : s => translatedProjection F i.val) u
    (fun i => cutoffDerivative_hasFDerivAt c b hR hU u hu hD i.val) hSum
  apply hFD.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds u (by norm_num : (0 : ℝ) < 1/2)] with v hv
  exact globalProjection_eq_weighted c b F s v (fun i hi => hs v
    (by simpa only [mem_ball,dist_comm] using hv) i hi)

/-- The actual constructed R inherits the active-coordinate error bound. -/
theorem globalProjection_error (u : CoordinateHilbert G) (s : Finset (J×G))
    (hzero : ∀ i ∉ s, translatedCutoff c b i u = 0) (hD : 0 < cutoffDenominator c b u)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hError : ∀ i, translatedCutoff c b i u ≠ 0 → ‖translatedProjection F i u-u‖ ≤ ε) :
    ‖globalProjection c b F u-u‖ ≤ ε := by
  rw [globalProjection_eq_weighted c b F s u hzero]
  apply weightedProjection_error_active _ _ u ε
  · exact localProjectionWeights_sum c b s u hzero (ne_of_gt hD)
  · intro i
    exact normalizedCutoff_nonneg c b i.val u
  · exact hε
  · intro i hi
    apply hError i.val
    intro hβ
    exact hi (by simp only [localProjectionWeights,normalizedCutoff,hβ,zero_div])

/-- The source's sharp derivative estimate is proved for the actual local
Frechet differential of the infinite equivariant projection. -/
theorem localGlobalProjectionDerivative_norm (u h : CoordinateHilbert G) (s : Finset (J×G))
    (hzero : ∀ i ∉ s, translatedCutoff c b i u = 0) (hD : 0 < cutoffDenominator c b u)
    (ε C0 : ℝ) (hε : 0 ≤ ε) (hGrad : cutoffGradientSum c b u ≤ C0)
    (hError : ∀ i, translatedCutoff c b i u ≠ 0 → ‖translatedProjection F i u-u‖ ≤ ε) :
    ‖localGlobalProjectionDerivative c b F s u h‖ ≤ (1+C0*ε)*‖h‖ := by
  apply weightedProjectionDerivative_norm_active
  · exact localProjectionWeights_sum c b s u hzero (ne_of_gt hD)
  · intro i
    exact normalizedCutoff_nonneg c b i.val u
  · exact localProjectionWeightDerivative_zero c b s u
  · intro i v
    exact translatedProjection_norm_le F i.val v
  · exact hε
  · intro i hi
    apply hError i.val
    intro hβ
    exact hi (by simp only [localProjectionWeights,normalizedCutoff,hβ,zero_div])
  · change (∑ i : s, ‖cutoffDerivative c b i.val u‖) ≤ C0
    rw [Finset.sum_coe_sort s (fun i : J×G => ‖cutoffDerivative c b i u‖),
      ← cutoffGradientSum_eq_sum c b s u hzero]
    exact hGrad

end Paper28
