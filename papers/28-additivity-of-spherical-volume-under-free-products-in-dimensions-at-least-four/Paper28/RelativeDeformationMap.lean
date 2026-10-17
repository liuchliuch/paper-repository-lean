import Paper28.RelativeDeformationConstruction
import Paper28.LocalQuotientLipschitz
import Paper28.SharpLocalAngular
import Paper28.FiniteCarrierDescent

/-! Sharp local Lipschitz bounds and finite carriers for the actual map
constructed from fixed standard cutoffs and finite coordinate projections. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Metric
open scoped Topology
variable {G : Type*} [Group G] [DecidableEq G] [Countable G]
local instance (C : Finset (RegularSphere G)) :
    ∀ j : C, Fintype (regularStabilizer (standardChartCenters C j)) := standardChartStabilizers C

theorem standardGlobalProjection_ne_zero_of_error
    (C : Finset (RegularSphere G)) (F : C → Finset G)
    (u : RegularSphere G) (ε : ℝ) (hε1 : ε < 1)
    (he : ‖standardGlobalProjection C F u.val-u.val‖ ≤ ε) :
    standardGlobalProjection C F u.val ≠ 0 := by
  intro hz
  rw [hz,zero_sub,norm_neg,u.property] at he
  linarith

theorem standardGlobalNormalizedProjection_contDiffAt
    (C : Finset (RegularSphere G)) (F : C → Finset G) (u : RegularSphere G)
    (hD : 0 < cutoffDenominator (standardChartCenters C) (standardChartBumps C) u.val)
    (hN : standardGlobalProjection C F u.val ≠ 0) :
    ContDiffAt ℝ 1 (standardGlobalNormalizedProjection C F) u.val :=
  globalNormalizedProjection_contDiffAt (standardChartCenters C) (standardChartBumps C) F
    (by intro j; norm_num [standardChartBumps,regularStandardBump]) (fun j => j.val.property)
    u.val u.property hD hN 1

theorem standardGlobalNormalizedProjection_local_lipschitz
    (M : SphericalQuotientMetricInput G)
    (C : Finset (RegularSphere G)) (F : C → Finset G) (U : Set (RegularOrbitQuotient G))
    (hNorm : ∀ u : RegularSphere G, regularQuotientMap u ∈ U →
      ‖standardGlobalNormalizedProjection C F u.val‖ = 1)
    (η : ℝ) (hη : 0 < η)
    (hData : ∀ u : RegularSphere G, regularQuotientMap u ∈ U →
      (0 < cutoffDenominator (standardChartCenters C) (standardChartBumps C) u.val) ∧
      (standardGlobalProjection C F u.val ≠ 0) ∧
      ∃ D : CoordinateHilbert G →L[ℝ] CoordinateHilbert G,
        HasFDerivAt (standardGlobalNormalizedProjection C F) D u.val ∧
          ∀ v, ‖D v‖ ≤ (1+η/4)*‖v‖) :
    letI := M.metric
    ∀ q : U, ∃ V : Set U, V ∈ 𝓝 q ∧
      LipschitzOnWith ⟨1+η,by linarith⟩
        (equivariantSphereDescent U (standardGlobalNormalizedProjection C F) hNorm) V := by
  letI := M.metric
  intro q
  let u := q.val.out
  have huq : regularQuotientMap u = q.val := Quotient.out_eq _
  have hu : regularQuotientMap u ∈ U := huq.symm ▸ q.property
  obtain ⟨hPos,hN,D,hD,hDb⟩ := hData u hu
  have hf := standardGlobalNormalizedProjection_contDiffAt C F u hPos hN
  have hDnorm : ‖D‖ ≤ 1+η/4 := D.opNorm_le_bound (by linarith) hDb
  obtain ⟨r,hr,hAngle⟩ := exists_local_sharp_angular_bound
    (standardGlobalNormalizedProjection C F) u.val D hf hD (1+η) (by linarith)
  have hEq := globalNormalizedProjection_equivariant (standardChartCenters C) (standardChartBumps C) F
  have hLip := local_angular_bound_descends M U (standardGlobalNormalizedProjection C F)
    hEq hNorm u hu ⟨1+η,by linarith⟩ (by change 0 < 1+η; linarith) r hr (by
      intro v w hv hw hvU hwU
      exact hAngle v.val w.val hv hw v.property w.property (hNorm v hvU) (hNorm w hwU))
  have hq : (⟨regularQuotientMap u,hu⟩ : U) = q := Subtype.ext huq
  rw [hq] at hLip
  exact ⟨ball q (r/8),ball_mem_nhds q (by positivity),hLip⟩

theorem standardGlobalNormalizedProjection_finite_carrier
    (C : Finset (RegularSphere G)) (F : C → Finset G)
    (U K : Set (RegularOrbitQuotient G)) (hK : IsCompact K) (hKU : K ⊆ U)
    (hNorm : ∀ u : RegularSphere G, regularQuotientMap u ∈ U →
      ‖standardGlobalNormalizedProjection C F u.val‖ = 1) :
    ∃ families : Finset (Finset G), (∀ E ∈ families, (1 : G) ∈ E) ∧
      (∀ q : U, q.val ∈ K → equivariantSphereDescent U
        (standardGlobalNormalizedProjection C F) hNorm q ∈ quotientFiniteCarrier families) := by
  apply exists_finite_carrier_of_local_support U K hK hKU (standardGlobalNormalizedProjection C F)
    (globalNormalizedProjection_equivariant (standardChartCenters C) (standardChartBumps C) F) hNorm
  intro u
  obtain ⟨E,hE⟩ := globalNormalizedProjection_local_support (standardChartCenters C) (standardChartBumps C) F
    (by intro j; norm_num [standardChartBumps,regularStandardBump]) (fun j => j.val.property) u.val u.property
  refine ⟨E,?_⟩
  intro v hv
  exact hE v.val (by simpa only [dist_comm] using hv)

end Paper28
