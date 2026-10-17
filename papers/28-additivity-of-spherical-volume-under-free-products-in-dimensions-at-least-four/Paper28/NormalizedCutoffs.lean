import Paper28.TranslatedCutoffs

/-! The actual equivariant partition weights: translated cutoff sums and
their normalization. All infinite sums are shown locally finite at unit
vectors, giving actual smoothness and the partition identity. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Metric
open scoped Topology
variable {G J : Type*} [Group G] [DecidableEq G] [Fintype J]
variable (c : J → CoordinateHilbert G) [∀ j, Fintype (regularStabilizer (c j))]
variable (b : ∀ j, ContDiffBump (c j))

def cutoffDenominator (u : CoordinateHilbert G) : ℝ := ∑' i : J×G, translatedCutoff c b i u

def normalizedCutoff (i : J×G) (u : CoordinateHilbert G) : ℝ :=
  translatedCutoff c b i u / cutoffDenominator c b u

theorem cutoffDenominator_eq_sum (s : Finset (J×G)) (u : CoordinateHilbert G)
    (hzero : ∀ i ∉ s, translatedCutoff c b i u = 0) :
    cutoffDenominator c b u = ∑ i ∈ s, translatedCutoff c b i u :=
  (hasSum_sum_of_ne_finset_zero hzero).tsum_eq

theorem cutoffDenominator_nonneg (u : CoordinateHilbert G) : 0 ≤ cutoffDenominator c b u :=
  tsum_nonneg (fun i => translatedCutoff_nonneg c b i u)

theorem normalizedCutoff_nonneg (i : J×G) (u : CoordinateHilbert G) : 0 ≤ normalizedCutoff c b i u :=
  div_nonneg (translatedCutoff_nonneg c b i u) (cutoffDenominator_nonneg c b u)

theorem cutoffDenominator_contDiffAt (hRadius : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hUnit : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1) (n : ℕ∞) :
    ContDiffAt ℝ n (cutoffDenominator c b) u := by
  obtain ⟨s,hs⟩ := translatedCutoff_local_finite c b hRadius hUnit u hu
  have hEq : cutoffDenominator c b =ᶠ[𝓝 u] (fun v => ∑ i ∈ s, translatedCutoff c b i v) := by
    filter_upwards [ball_mem_nhds u (by norm_num : (0 : ℝ) < 1/2)] with v hv
    exact cutoffDenominator_eq_sum c b s v (fun i hi => hs v (by simpa only [mem_ball,dist_comm] using hv) i hi)
  exact (ContDiff.sum (fun i _ => translatedCutoff_contDiff c b i n)).contDiffAt.congr_of_eventuallyEq hEq

theorem normalizedCutoff_contDiffAt (hRadius : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hUnit : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (hD : 0 < cutoffDenominator c b u) (i : J×G) (n : ℕ∞) :
    ContDiffAt ℝ n (normalizedCutoff c b i) u :=
  (translatedCutoff_contDiff c b i n).contDiffAt.div
    (cutoffDenominator_contDiffAt c b hRadius hUnit u hu n) (ne_of_gt hD)

/-- The denominator is positive wherever at least one translated cutoff
is positive. This will be applied to the finite compact quotient cover. -/
theorem cutoffDenominator_pos (hRadius : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hUnit : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (i : J×G) (hi : 0 < translatedCutoff c b i u) : 0 < cutoffDenominator c b u := by
  obtain ⟨s,hs⟩ := translatedCutoff_local_finite c b hRadius hUnit u hu
  have hzero : ∀ k ∉ s, translatedCutoff c b k u = 0 :=
    fun k hk => hs u (by simp) k hk
  have his : i ∈ s := by
    by_contra h
    have hz := hzero i h
    linarith
  rw [cutoffDenominator_eq_sum c b s u hzero]
  exact hi.trans_le (Finset.single_le_sum (fun k _ => translatedCutoff_nonneg c b k u) his)

theorem normalizedCutoff_sum (s : Finset (J×G)) (u : CoordinateHilbert G)
    (hzero : ∀ i ∉ s, translatedCutoff c b i u = 0) (hD : cutoffDenominator c b u ≠ 0) :
    (∑ i ∈ s, normalizedCutoff c b i u) = 1 := by
  simp only [normalizedCutoff]
  rw [← Finset.sum_div, ← cutoffDenominator_eq_sum c b s u hzero, div_self hD]

/-- Equivariance of the actual infinite normalization denominator. -/
theorem cutoffDenominator_equivariant (δ : G) (u : CoordinateHilbert G) :
    cutoffDenominator c b (leftRegular δ u) = cutoffDenominator c b u := by
  let e : J×G ≃ J×G := Equiv.prodCongr (Equiv.refl J) (Equiv.mulLeft δ)
  unfold cutoffDenominator
  calc
    _ = ∑' i : J×G, translatedCutoff c b (e i) (leftRegular δ u) :=
      (e.tsum_eq (fun i => translatedCutoff c b i (leftRegular δ u))).symm
    _ = _ := tsum_congr (fun i => translatedCutoff_equivariant c b i.1 i.2 δ u)

theorem normalizedCutoff_equivariant (j : J) (γ δ : G) (u : CoordinateHilbert G) :
    normalizedCutoff c b (j,δ*γ) (leftRegular δ u) = normalizedCutoff c b (j,γ) u := by
  unfold normalizedCutoff
  rw [translatedCutoff_equivariant,cutoffDenominator_equivariant]

end Paper28
