import Paper28.RelativeDeformationHomotopy

/-! The relative finite-carrier deformation on the actual spherical orbit
quotient. Its relative hypothesis is only a finite compact support cover;
polyhedral supports provide such a cover when the current API is connected. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Metric Set
open scoped Topology
variable {G : Type*} [Group G] [DecidableEq G]
local instance (C : Finset (RegularSphere G)) :
    ∀ j : C, Fintype (regularStabilizer (standardChartCenters C j)) := standardChartStabilizers C

structure RelativeCarrierDeformation [metric : MetricSpace (RegularOrbitQuotient G)]
    (K Z : Set (RegularOrbitQuotient G)) (L : NNReal) where
  neighborhood : Set (RegularOrbitQuotient G)
  neighborhood_open : @IsOpen (RegularOrbitQuotient G)
    metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace neighborhood
  contains : K ⊆ neighborhood
  map : neighborhood → RegularOrbitQuotient G
  locally_lipschitz : ∀ q, ∃ V : Set neighborhood,
    V ∈ @nhds neighborhood (TopologicalSpace.induced Subtype.val
      metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) q ∧ LipschitzOnWith L map V
  families : Finset (Finset G)
  coordinates_nonempty : ∀ E ∈ families, (1 : G) ∈ E
  finite_carrier : ∀ q : neighborhood, q.val ∈ K → map q ∈ quotientFiniteCarrier families
  homotopy : DeformationInterval×K → RegularOrbitQuotient G
  homotopy_lipschitz : ∃ B : NNReal, LipschitzWith B homotopy
  homotopy_compact_image : @IsCompact (RegularOrbitQuotient G)
    metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace (Set.range homotopy)
  homotopy_zero : ∀ q : K, homotopy (⟨0,by norm_num⟩,q) = q.val
  homotopy_one : ∀ q : K, homotopy (⟨1,by norm_num⟩,q) = map ⟨q.val,contains q.property⟩
  map_fixed : ∀ q : neighborhood, q.val ∈ Z → map q = q.val
  homotopy_fixed : ∀ t, ∀ q : K, q.val ∈ Z → homotopy (t,q) = q.val

set_option maxHeartbeats 800000 in
theorem relative_deformation_of_finite_support_pieces
    [Countable G] (M : SphericalQuotientMetricInput G)
    (K Z : Set (RegularOrbitQuotient G)) (hK : IsCompact K)
    {A : Type*} [Fintype A]
    (P : A → Set (CoordinateHilbert G)) (hP : ∀ a, IsCompact (P a))
    (hUnit : ∀ a, ∀ u ∈ P a, ‖u‖ = 1) (S : A → Finset G)
    (hS : ∀ a, ∀ u ∈ P a, u ∈ coordinateSupportSubspace (S a))
    (hZ : ∀ z ∈ Z, ∃ u : RegularSphere G, regularQuotientMap u = z ∧ u.val ∈ liftedRelativePieces P)
    (η : ℝ) (hη : 0 < η) :
    letI := M.metric
    Nonempty (RelativeCarrierDeformation K Z ⟨1+η,by linarith⟩) := by
  letI := M.metric
  obtain ⟨C,F,hF,ε,hε,hε1,U,hU,hKU,hData⟩ :=
    exists_relative_deformation_construction K hK P hP hUnit S hS (η/4) (by positivity)
  let hNorm : ∀ u : RegularSphere G, regularQuotientMap u ∈ U →
      ‖standardGlobalNormalizedProjection C F u.val‖ = 1 := fun u hu => (hData u hu).2.2.1
  let hPos : ∀ u : RegularSphere G, regularQuotientMap u ∈ U →
      0 < cutoffDenominator (standardChartCenters C) (standardChartBumps C) u.val :=
    fun u hu => (hData u hu).1
  let hError : ∀ u : RegularSphere G, regularQuotientMap u ∈ U →
      ‖standardGlobalProjection C F u.val-u.val‖ ≤ ε := fun u hu => (hData u hu).2.1
  let f := equivariantSphereDescent U (standardGlobalNormalizedProjection C F) hNorm
  have hEq : ∀ γ u, standardGlobalNormalizedProjection C F (leftRegular γ u) =
      leftRegular γ (standardGlobalNormalizedProjection C F u) :=
    globalNormalizedProjection_equivariant (standardChartCenters C) (standardChartBumps C) F
  have hLip := standardGlobalNormalizedProjection_local_lipschitz M C F U hNorm η hη (by
    intro u hu
    exact ⟨hPos u hu,standardGlobalProjection_ne_zero_of_error C F u ε hε1 (hError u hu),
      (hData u hu).2.2.2.1⟩)
  obtain ⟨families,hFamilies,hCarrier⟩ :=
    standardGlobalNormalizedProjection_finite_carrier C F U K hK hKU hNorm
  let hHNorm := standardGlobalHomotopy_norm C F U ε hε.le hε1 hError
  let H : DeformationInterval×K → RegularOrbitQuotient G := fun p =>
    equivariantSphereDescent U (standardGlobalHomotopy C F p.1.val) (hHNorm p.1)
      ⟨p.2.val,hKU p.2.property⟩
  obtain ⟨B,hHLip⟩ := standardGlobalHomotopy_compact_lipschitz M C F U K hK hKU
    ε hε.le hε1 hPos hError
  have hHEq : ∀ t : DeformationInterval, ∀ γ u,
      standardGlobalHomotopy C F t.val (leftRegular γ u) =
        leftRegular γ (standardGlobalHomotopy C F t.val u) := by
    intro t γ u
    exact globalProjectionHomotopy_equivariant (standardChartCenters C) (standardChartBumps C) F γ t.val u
  have hHEval : ∀ t : DeformationInterval, ∀ q : K, ∀ u : RegularSphere G,
      ∀ hu : regularQuotientMap u = q.val,
        H (t,q) = regularQuotientMap ⟨standardGlobalHomotopy C F t.val u.val,
          hHNorm t u (hu.symm ▸ hKU q.property)⟩ := by
    intro t q u hu
    have huU : regularQuotientMap u ∈ U := hu.symm ▸ hKU q.property
    change equivariantSphereDescent U _ _ _ = _
    exact equivariantSphereDescent_eval_of_eq U _ (hHEq t) (hHNorm t) _ u hu
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : CompactSpace DeformationInterval := isCompact_iff_compactSpace.mp isCompact_Icc
  refine ⟨{
    neighborhood := U
    neighborhood_open := hU
    contains := hKU
    map := f
    locally_lipschitz := hLip
    families := families
    coordinates_nonempty := hFamilies
    finite_carrier := hCarrier
    homotopy := H
    homotopy_lipschitz := ⟨B,hHLip⟩
    homotopy_compact_image := ?_
    homotopy_zero := ?_
    homotopy_one := ?_
    map_fixed := ?_
    homotopy_fixed := ?_ }⟩
  · simpa only [image_univ] using (isCompact_univ.image hHLip.continuous)
  · intro q
    let u := q.val.out
    have hu : regularQuotientMap u = q.val := Quotient.out_eq _
    rw [hHEval ⟨0,by norm_num⟩ q u hu]
    have he := (globalProjectionHomotopy_endpoints (standardChartCenters C) (standardChartBumps C) F u.val u.property).1
    exact (congrArg regularQuotientMap (Subtype.ext he)).trans hu
  · intro q
    let u := q.val.out
    have hu : regularQuotientMap u = q.val := Quotient.out_eq _
    rw [hHEval ⟨1,by norm_num⟩ q u hu]
    dsimp [f]
    rw [equivariantSphereDescent_eval_of_eq U (standardGlobalNormalizedProjection C F)
      hEq hNorm ⟨q.val,hKU q.property⟩ u hu]
    apply congrArg regularQuotientMap
    exact Subtype.ext (globalProjectionHomotopy_endpoints
      (standardChartCenters C) (standardChartBumps C) F u.val u.property).2
  · intro q hq
    obtain ⟨u,hu,hRel⟩ := hZ q.val hq
    have huU : regularQuotientMap u ∈ U := hu.symm ▸ q.property
    have hFixed := ((hData u huU).2.2.2.2.2 hRel).1
    exact (equivariantSphereDescent_eval_of_eq U _ hEq hNorm q u hu).trans
      ((congrArg regularQuotientMap (Subtype.ext hFixed)).trans hu)
  · intro t q hq
    obtain ⟨u,hu,hRel⟩ := hZ q.val hq
    have huU : regularQuotientMap u ∈ U := hu.symm ▸ hKU q.property
    rw [hHEval t q u hu]
    have hFixed := ((hData u huU).2.2.2.2.2 hRel).2 t.val
    exact (congrArg regularQuotientMap (Subtype.ext hFixed)).trans hu

end Paper28
