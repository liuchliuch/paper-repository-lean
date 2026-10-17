import Paper28.SphericalCellPathMetric
import Paper28.FiniteClosedLipschitzGluing
import Paper28.GlobalAngularChordBound
import Paper28.NeighborhoodPushforwardInput
import Paper28.SphericalAtlasGeometry

/-! Native ordinary Lipschitz regularity of the actual spherical
realization. Smooth affine-normalized branches, the exact intrinsic
cell metric and finite closed-cover gluing replace a Lip(h) premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Set Metric
open scoped Topology
universe w
variable {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
  {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  {B : FullSubcomplexBarycentricAtlas K V Idx} {Y : Type w} [metricY : MetricSpace Y]
variable (C : FullSubcomplexSphericalCharts B Y) (M : SphericalCellPathMetricInput C)

theorem atlasSphereLift_lipschitzOn_compact (j : Idx) (N : Set (EuclideanAmbient d))
    (hN : IsCompact N) (hNU : N ⊆ atlasRetractionDomain B) :
    ∃ L : NNReal, LipschitzOnWith L (atlasSphereLift B (C.vertex j) j) (N ∩ atlasCell B j) := by
  let Uj := {x | atlasLiftLinear B (C.vertex j) j x+atlasLiftOffset B (C.vertex j) j ≠ 0}
  have hf : LipschitzNearSet inferInstance inferInstance (atlasSphereLift B (C.vertex j) j) Uj := by
    intro x hx
    exact ((normalizedAffineMap_contDiffAt _ _ x hx 1).hasStrictFDerivAt le_rfl).exists_lipschitzOnWith
  obtain ⟨L,hL⟩ := LipschitzNearSet.compact_restrict (atlasSphereLift B (C.vertex j) j) Uj
    (N ∩ atlasCell B j) hf (fun x hx => atlasSphereLift_raw_nonzero C j x ⟨hNU hx.1,hx.2⟩)
    (hN.inter_right (atlasCell_isClosed j))
  exact ⟨L,LipschitzOnWith.of_dist_le_mul (fun x hx y hy => hL.dist_le_mul ⟨x,hx⟩ ⟨y,hy⟩)⟩

include M

theorem atlasSphericalMap_lipschitzOn_compact_cell (y₀ : Y) (j : Idx) (N : Set (EuclideanAmbient d))
    (hN : IsCompact N) (hNU : N ⊆ atlasRetractionDomain B) :
    ∃ L : NNReal, LipschitzOnWith L (atlasSphericalMap B C.homeomorph y₀) (atlasCell B j ∩ N) := by
  obtain ⟨L,hL⟩ := atlasSphereLift_lipschitzOn_compact C j N hN hNU
  let P : NNReal := ⟨Real.pi/2,by positivity⟩
  refine ⟨P*L,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hxU := hNU hx.2
  have hyU := hNU hy.2
  rw [atlasSphericalMap_chart C y₀ j x hxU hx.1,atlasSphericalMap_chart C y₀ j y hyU hy.1]
  have hc := spherical_cell_distance_le_angle C M j _ _
    (atlasSphereLift_mem_closed_patch C j x ⟨hxU,hx.1⟩) (atlasSphereLift_mem_closed_patch C j y ⟨hyU,hy.1⟩)
  have ha := angular_le_pi_half_chord (atlasSphereLift B (C.vertex j) j x) (atlasSphereLift B (C.vertex j) j y)
    (atlasSphereLift_unit C j x ⟨hxU,hx.1⟩) (atlasSphereLift_unit C j y ⟨hyU,hy.1⟩)
  have hl := hL.dist_le_mul x ⟨hx.2,hx.1⟩ y ⟨hy.2,hy.1⟩
  rw [dist_eq_norm] at hl
  exact hc.trans (ha.trans (by
    simpa only [NNReal.coe_mul,P,mul_assoc] using mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ Real.pi/2)))

theorem atlasSphericalMap_near_lipschitz_intrinsic (y₀ : Y) :
    LipschitzNearSet inferInstance metricY (atlasSphericalMap B C.homeomorph y₀) (atlasRetractionDomain B) := by
  classical
  intro x hx
  obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp (atlasRetractionDomain_isOpen B) x hx
  let N := closedBall x (r/2)
  have hN : IsCompact N := isCompact_closedBall _ _
  have hNU : N ⊆ atlasRetractionDomain B := fun y hy => hrU (by
    change dist y x < r
    have hd : dist y x ≤ r/2 := hy
    linarith)
  choose L hL using fun j => atlasSphericalMap_lipschitzOn_compact_cell C M y₀ j N hN hNU
  let Lmax : NNReal := Finset.univ.sup L
  have hLip : LipschitzOnWith Lmax (atlasSphericalMap B C.homeomorph y₀) N := by
    apply lipschitzOn_finite_closed_cover_convex Finset.univ (atlasCell B) N (convex_closedBall x (r/2))
      _ Lmax (fun j _ => atlasCell_isClosed j)
    · intro j _
      apply LipschitzOnWith.of_dist_le_mul
      intro y hy z hz
      exact ((hL j).dist_le_mul y hy z hz).trans (mul_le_mul_of_nonneg_right
        (show (L j : ℝ) ≤ (Lmax : ℝ) from by
          exact_mod_cast (Finset.le_sup (Finset.mem_univ j) : L j ≤ Lmax)) dist_nonneg)
    · intro y hy
      obtain ⟨j,hj⟩ := mem_iUnion.mp (atlasCells_cover (hNU hy))
      exact mem_iUnion₂.mpr ⟨j,Finset.mem_univ _,hj⟩
  exact ⟨Lmax,N,closedBall_mem_nhds x (by positivity),hLip⟩

theorem spherical_realization_lipschitz (y₀ : Y) : ∃ L : NNReal, LipschitzWith L C.homeomorph := by
  apply exists_lipschitzWith_of_compactSpace
  intro x
  obtain ⟨L,S,hS,hL⟩ := atlasSphericalMap_near_lipschitz_intrinsic C M y₀ x.val
    (atlasRetractionDomain_contains B x.property)
  refine ⟨L,Subtype.val ⁻¹' S,continuous_subtype_val.continuousAt.preimage_mem_nhds hS,
    LipschitzOnWith.of_dist_le_mul ?_⟩
  intro y hy z hz
  rw [← atlasSphericalMap_on_carrier B C.homeomorph y₀ y,← atlasSphericalMap_on_carrier B C.homeomorph y₀ z]
  exact hL.dist_le_mul y.val hy z.val hz

end Paper28
