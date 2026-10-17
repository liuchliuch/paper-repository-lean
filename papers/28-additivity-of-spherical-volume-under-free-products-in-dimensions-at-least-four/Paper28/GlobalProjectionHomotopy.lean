import Paper28.GlobalNormalizationCalculus

/-! Exact relative fixing and actual normalized homotopy of the global
construction, with denominators and ambient smoothness proved directly. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Metric
open scoped Topology
variable {G J : Type*} [Group G] [DecidableEq G] [Fintype J]
variable (c : J → CoordinateHilbert G) [∀ j, Fintype (regularStabilizer (c j))]
variable (b : ∀ j, ContDiffBump (c j)) (F : J → Finset G)

theorem globalProjection_fixed (hR : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hU : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (hD : 0 < cutoffDenominator c b u)
    (hFix : ∀ i, translatedCutoff c b i u ≠ 0 → translatedProjection F i u = u) :
    globalProjection c b F u = u := by
  obtain ⟨s,hs⟩ := translatedCutoff_local_finite c b hR hU u hu
  have hzero : ∀ i ∉ s, translatedCutoff c b i u = 0 := fun i hi => hs u (by simp) i hi
  rw [globalProjection_eq_weighted c b F s u hzero]
  apply weightedProjection_fixed
  · exact localProjectionWeights_sum c b s u hzero (ne_of_gt hD)
  · intro i hi
    apply hFix i.val
    intro hβ
    exact hi (by simp only [localProjectionWeights,normalizedCutoff,hβ,zero_div])

theorem globalProjectionHomotopy_endpoints (u : CoordinateHilbert G) (hu : ‖u‖ = 1) :
    globalProjectionHomotopy c b F 0 u = u ∧
      globalProjectionHomotopy c b F 1 u = globalNormalizedProjection c b F u := by
  simp only [globalProjectionHomotopy,sub_zero,one_smul,zero_smul,add_zero,sub_self,zero_add,
    sphericalNormalize_fixed u hu,globalNormalizedProjection,and_self]

theorem globalProjectionHomotopy_fixed (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (hFix : globalProjection c b F u = u) (t : ℝ) : globalProjectionHomotopy c b F t u = u := by
  unfold globalProjectionHomotopy
  rw [hFix]
  have he : (1-t) • u+t • u = u := by module
  rw [he,sphericalNormalize_fixed u hu]

theorem globalProjectionHomotopy_denominator (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hError : ‖globalProjection c b F u-u‖ ≤ ε)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1-ε ≤ ‖(1-t) • u+t • globalProjection c b F u‖ := by
  have he : (1-t) • u+t • globalProjection c b F u-u = t • (globalProjection c b F u-u) := by module
  have hN : ‖(1-t) • u+t • globalProjection c b F u-u‖ ≤ ε := by
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
    exact (mul_le_mul_of_nonneg_left hError ht0).trans (by nlinarith)
  have hn := norm_sub_norm_le u ((1-t) • u+t • globalProjection c b F u)
  rw [hu,norm_sub_rev] at hn
  linarith

theorem sphericalNormalize_contDiffAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : H) (hu : u ≠ 0) (n : ℕ∞) : ContDiffAt ℝ n (sphericalNormalize : H → H) u := by
  exact ((contDiffAt_id.norm ℝ hu).inv (norm_ne_zero_iff.mpr hu)).smul contDiffAt_id

theorem globalNormalizedProjection_contDiffAt (hR : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hU : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (hD : 0 < cutoffDenominator c b u) (hRN : globalProjection c b F u ≠ 0) (n : ℕ∞) :
    ContDiffAt ℝ n (globalNormalizedProjection c b F) u :=
  (sphericalNormalize_contDiffAt _ hRN n).comp u (globalProjection_contDiffAt c b F hR hU u hu hD n)

/-- The normalized straight homotopy is actually smooth near every point
where its explicitly bounded denominator is nonzero. -/
theorem globalProjectionHomotopy_contDiffAt (hR : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hU : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (hD : 0 < cutoffDenominator c b u) (t : ℝ)
    (hN : (1-t) • u+t • globalProjection c b F u ≠ 0) (n : ℕ∞) :
    ContDiffAt ℝ n (fun p : ℝ×CoordinateHilbert G => globalProjectionHomotopy c b F p.1 p.2) (t,u) := by
  have hRaw : ContDiffAt ℝ n
      (fun p : ℝ×CoordinateHilbert G => (1-p.1) • p.2+p.1 • globalProjection c b F p.2) (t,u) :=
    ((contDiffAt_const.sub contDiffAt_fst).smul contDiffAt_snd).add
      (contDiffAt_fst.smul ((globalProjection_contDiffAt c b F hR hU u hu hD n).comp (t,u) contDiffAt_snd))
  exact (sphericalNormalize_contDiffAt _ hN n).comp (t,u) hRaw

end Paper28
