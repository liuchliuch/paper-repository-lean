import Paper28.NormalizedStraightSphereArc
import Paper28.FiniteCoordinateSphereCells
import Paper28.FiniteClosedLipschitzGluing
import Paper28.GlobalAngularChordBound

/-! Cellwise round distance control gives a native distance bound along
actual normalized straight arcs in a finite coordinate sphere. The finite
closed-cover argument requires no a priori continuity of the target map. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped Classical
variable {G Z : Type*} [Group G] [DecidableEq G] [PseudoMetricSpace Z]

theorem coordinateSphereCellIndices_mono {E F : Finset G} (hEF : E ⊆ F) :
    coordinateSphereCellIndices E ⊆ coordinateSphereCellIndices F := by
  intro p hp
  obtain ⟨hp,hC⟩ := Finset.mem_filter.mp hp
  obtain ⟨hA,hD⟩ := Finset.mem_product.mp hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hC⟩
  · exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hA).trans hEF)
  · apply Finset.mem_powerset.mpr
    intro A hA
    exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp ((Finset.mem_powerset.mp hD) hA)).trans hEF)

theorem coordinate_sphere_cellwise_angular_bound (E : Finset G) (f : RegularSphere G → Z)
    (hCell : ∀ p ∈ coordinateSphereCellIndices E,
      ∀ v ∈ closedSignedBarycentricCell p.1 p.2,
      ∀ w ∈ closedSignedBarycentricCell p.1 p.2, dist (f v) (f w) ≤ angular v.val w.val)
    (u x y : RegularSphere G)
    (hxE : x.val ∈ coordinateSupportSubspace E) (hyE : y.val ∈ coordinateSupportSubspace E)
    (hx : ‖x.val-u.val‖ ≤ 1/2) (hy : ‖y.val-u.val‖ ≤ 1/2) :
    dist (f x) (f y) ≤ 2*Real.pi*‖x.val-y.val‖ := by
  let arc : ℝ → RegularSphere G := normalizedStraightSphereArc u x y hx hy
  have hArc := normalizedStraightSphereArc_lipschitz u x y hx hy
  have hSupport : ∀ t, arc t ∈ regularCoordinateSphere E := by
    intro t
    exact normalizedStraightSphereArc_mem_subspace u x y hx hy _ hxE hyE t
  let L : NNReal := ⟨2*Real.pi*‖x.val-y.val‖,by positivity⟩
  have hBound := finite_closed_cover_dist_bound (coordinateSphereCellIndices E)
    (fun p => arc ⁻¹' closedSignedBarycentricCell p.1 p.2) (fun t => f (arc t)) L 0 1 (by norm_num)
    (fun p hp => (coordinateSphereCellIndices_compact E p hp).isClosed.preimage hArc.continuous)
    (fun p hp => ?_)
    (fun t ht => by
      obtain ⟨p,hp,hpt⟩ := mem_iUnion₂.mp (coordinateSphere_finite_closed_cell_cover E (hSupport t))
      exact mem_iUnion₂.mpr ⟨p,hp,hpt⟩)
  · simpa only [arc,normalizedStraightSphereArc_zero,normalizedStraightSphereArc_one,
      sub_zero,mul_one,L] using hBound
  · apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    have hRound := angular_le_pi_half_chord (arc s).val (arc t).val (arc s).property (arc t).property
    have hChord : ‖(arc s).val-(arc t).val‖ ≤ (4*‖x.val-y.val‖)*dist s t := by
      simpa only [Subtype.dist_eq,dist_eq_norm,NNReal.coe_mul,NNReal.coe_ofNat,coe_nnnorm] using hArc.dist_le_mul s t
    calc
      _ ≤ angular (arc s).val (arc t).val := hCell p hp _ hs.1 _ ht.1
      _ ≤ (Real.pi/2)*‖(arc s).val-(arc t).val‖ := hRound
      _ ≤ (Real.pi/2)*((4*‖x.val-y.val‖)*dist s t) :=
        mul_le_mul_of_nonneg_left hChord (by positivity)
      _ = (L : ℝ)*dist s t := by dsimp [L]; ring

end Paper28
