import Paper28.RelativeDeformationMap
import Paper28.LocalHomotopyAngular
import Paper28.LocalHomotopyDescent
import Paper28.CompactLocalLipschitz

/-! The actual normalized straight homotopy descends, is jointly locally
Lipschitz, and is globally Lipschitz on [0,1] times the compact set. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Metric Set
open scoped Topology
variable {G : Type*} [Group G] [DecidableEq G] [Countable G]
local instance (C : Finset (RegularSphere G)) :
    ∀ j : C, Fintype (regularStabilizer (standardChartCenters C j)) := standardChartStabilizers C

abbrev DeformationInterval := Icc (0 : ℝ) 1

theorem standardGlobalHomotopy_raw_ne_zero
    (C : Finset (RegularSphere G)) (F : C → Finset G) (u : RegularSphere G)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hError : ‖standardGlobalProjection C F u.val-u.val‖ ≤ ε) (t : DeformationInterval) :
    (1-t.val) • u.val+t.val • standardGlobalProjection C F u.val ≠ 0 := by
  have h := globalProjectionHomotopy_denominator (standardChartCenters C) (standardChartBumps C) F
    u.val u.property ε hε hError t.val t.property.1 t.property.2
  intro hz
  change 1-ε ≤ ‖(1-t.val) • u.val+t.val • standardGlobalProjection C F u.val‖ at h
  rw [hz,norm_zero] at h
  linarith

theorem standardGlobalHomotopy_norm
    (C : Finset (RegularSphere G)) (F : C → Finset G) (U : Set (RegularOrbitQuotient G))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hError : ∀ u : RegularSphere G, regularQuotientMap u ∈ U →
      ‖standardGlobalProjection C F u.val-u.val‖ ≤ ε) :
    ∀ t : DeformationInterval, ∀ u : RegularSphere G, regularQuotientMap u ∈ U →
      ‖standardGlobalHomotopy C F t.val u.val‖ = 1 := by
  intro t u hu
  exact sphericalNormalize_norm _ (standardGlobalHomotopy_raw_ne_zero C F u ε hε hε1 (hError u hu) t)

theorem standardGlobalHomotopy_locallyLipschitz
    (M : SphericalQuotientMetricInput G)
    (C : Finset (RegularSphere G)) (F : C → Finset G) (U : Set (RegularOrbitQuotient G))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hPos : ∀ u : RegularSphere G, regularQuotientMap u ∈ U →
      0 < cutoffDenominator (standardChartCenters C) (standardChartBumps C) u.val)
    (hError : ∀ u : RegularSphere G, regularQuotientMap u ∈ U →
      ‖standardGlobalProjection C F u.val-u.val‖ ≤ ε) :
    letI := M.metric
    LocallyLipschitz (fun p : DeformationInterval×U =>
      equivariantSphereDescent U (standardGlobalHomotopy C F p.1.val)
        (standardGlobalHomotopy_norm C F U ε hε hε1 hError p.1) p.2) := by
  letI := M.metric
  let hNorm := standardGlobalHomotopy_norm C F U ε hε hε1 hError
  have hEq : ∀ t : DeformationInterval, ∀ γ u,
      standardGlobalHomotopy C F t.val (leftRegular γ u) =
        leftRegular γ (standardGlobalHomotopy C F t.val u) := by
    intro t γ u
    exact globalProjectionHomotopy_equivariant (standardChartCenters C) (standardChartBumps C) F γ t.val u
  intro p
  let u := p.2.val.out
  have huq : regularQuotientMap u = p.2.val := Quotient.out_eq _
  have hu : regularQuotientMap u ∈ U := huq.symm ▸ p.2.property
  have hRaw := standardGlobalHomotopy_raw_ne_zero C F u ε hε hε1 (hError u hu) p.1
  have hSmooth : ContDiffAt ℝ 1
      (fun z : ℝ×CoordinateHilbert G => standardGlobalHomotopy C F z.1 z.2) (p.1.val,u.val) :=
    globalProjectionHomotopy_contDiffAt (standardChartCenters C) (standardChartBumps C) F
      (by intro j; norm_num [standardChartBumps,regularStandardBump]) (fun j => j.val.property)
      u.val u.property (hPos u hu) p.1.val hRaw 1
  obtain ⟨B,hB,r,hr,hAngle⟩ := exists_local_homotopy_angular_bound
    (standardGlobalHomotopy C F) p.1.val u.val hSmooth
  let BN : NNReal := ⟨B,hB.le⟩
  have hLip := local_homotopy_angular_bound_descends M U
    (fun t : DeformationInterval => standardGlobalHomotopy C F t.val) hEq hNorm p.1 u hu BN hB r hr (by
      intro s z v w hs hz hv hw hvU hwU
      exact hAngle s.val z.val v.val w.val hs hz hv hw v.property w.property
        (hNorm s v hvU) (hNorm z w hwU))
  have hp : (p.1,(⟨regularQuotientMap u,hu⟩ : U)) = p := Prod.ext rfl (Subtype.ext huq)
  rw [hp] at hLip
  exact ⟨2*BN,ball p (r/8),ball_mem_nhds p (by positivity),hLip⟩

set_option maxHeartbeats 600000 in
theorem standardGlobalHomotopy_compact_lipschitz
    (M : SphericalQuotientMetricInput G)
    (C : Finset (RegularSphere G)) (F : C → Finset G) (U K : Set (RegularOrbitQuotient G))
    (hK : IsCompact K) (hKU : K ⊆ U)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hPos : ∀ u : RegularSphere G, regularQuotientMap u ∈ U →
      0 < cutoffDenominator (standardChartCenters C) (standardChartBumps C) u.val)
    (hError : ∀ u : RegularSphere G, regularQuotientMap u ∈ U →
      ‖standardGlobalProjection C F u.val-u.val‖ ≤ ε) :
    letI := M.metric
    ∃ L : NNReal, LipschitzWith L (fun p : DeformationInterval×K =>
      equivariantSphereDescent U (standardGlobalHomotopy C F p.1.val)
        (standardGlobalHomotopy_norm C F U ε hε hε1 hError p.1) ⟨p.2.val,hKU p.2.property⟩) := by
  letI := M.metric
  letI : CompactSpace DeformationInterval := isCompact_iff_compactSpace.mp isCompact_Icc
  have hLocal := standardGlobalHomotopy_locallyLipschitz M C F U ε hε hε1 hPos hError
  exact exists_lipschitzWith_compact_restriction U K hK hKU _ hLocal

end Paper28
