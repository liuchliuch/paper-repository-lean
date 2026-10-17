import Paper28.OpenNeighborhoodExtension
import Paper28.CompactCurrentHomotopyInput
import Paper28.RelativeCarrierLemma

/-! Apply the actual native relative deformation to actual compact
integral currents. Only generic canonical AK pushforward/locality/local
mass and interval-product laws are used. The current homology, sharp local
mass bound, carrier support and preserved prescribed boundary are derived. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Set
open scoped Topology
variable {G : Type} [Group G] [DecidableEq G] [Countable G]
  [metric : MetricSpace (RegularOrbitQuotient G)]
variable {K R : Set (RegularOrbitQuotient G)} {L : NNReal}
  (F : RelativeCarrierDeformation K R L)

def relativeDeformationExtension := openNeighborhoodExtension F.neighborhood F.map

theorem relativeDeformationExtension_local :
    ∀ x ∈ F.neighborhood, ∃ V : Set (RegularOrbitQuotient G),
      V ∈ @nhds (RegularOrbitQuotient G) metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace x ∧
      LipschitzOnWith L (relativeDeformationExtension F) V := by
  exact openNeighborhoodExtension_local_constant F.neighborhood F.neighborhood_open F.map L F.locally_lipschitz

theorem relativeDeformationExtension_lipschitz :
    LipschitzNearSet metric metric (relativeDeformationExtension F) F.neighborhood := by
  exact openNeighborhoodExtension_near_lipschitz F.neighborhood F.neighborhood_open F.map L F.locally_lipschitz

variable (I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) metric)
  (P : NeighborhoodCurrentPushforwardInput metric metric I I F.neighborhood
    (relativeDeformationExtension F) F.neighborhood_open (relativeDeformationExtension_lipschitz F))
  (Local : LocalCurrentPushforwardCalculusInput I F.neighborhood (relativeDeformationExtension F)
    F.neighborhood_open (relativeDeformationExtension_lipschitz F) P)

include Local in
theorem relative_deformation_current_mass {k : ℕ} (C : I.Current k) (hCK : I.support C ⊆ K) :
    I.mass (P.push k ⟨C,hCK.trans F.contains⟩) ≤ (L : ℝ)^k*I.mass C := by
  exact Local.mass_local_lipschitz_le k _ L (fun x hx => relativeDeformationExtension_local F x
    (F.contains (hCK hx)))

theorem relative_deformation_current_support {k : ℕ} (C : I.Current k) (hCK : I.support C ⊆ K) :
    I.support (P.push k ⟨C,hCK.trans F.contains⟩) ⊆ quotientFiniteCarrier F.families := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := P.support_subset k ⟨C,hCK.trans F.contains⟩ hy
  rw [relativeDeformationExtension,openNeighborhoodExtension_apply F.map x (F.contains (hCK hx))]
  exact F.finite_carrier ⟨x,F.contains (hCK hx)⟩ (hCK hx)

include Local in
theorem relative_deformation_current_cycle
    (H : CompactCurrentHomotopyInput I) {k : ℕ} (C : I.Current (k+1))
    (hCK : I.support C ⊆ K) (hC : I.boundary k C = 0) :
    ∃ E : I.Current (k+1), ∃ W : I.Current (k+2),
      I.boundary k E = 0 ∧ C-E = I.boundary (k+1) W ∧
      I.support E ⊆ quotientFiniteCarrier F.families ∧ I.mass E ≤ (L : ℝ)^(k+1)*I.mass C := by
  let Ck : supportedCurrents I K (k+1) := ⟨C,hCK⟩
  let E := P.push (k+1) ⟨C,hCK.trans F.contains⟩
  let W := -(H.homotopyPush K F.homotopy F.homotopy_lipschitz (k+1) Ck)
  have hz : supportedBoundary I K k Ck = 0 := Subtype.ext hC
  have hb := H.boundary_formula F.neighborhood (relativeDeformationExtension F) F.neighborhood_open
    (relativeDeformationExtension_lipschitz F) P K F.contains F.homotopy F.homotopy_lipschitz
    F.homotopy_zero (fun x => (F.homotopy_one x).trans
      (openNeighborhoodExtension_apply F.map x.val (F.contains x.property)).symm) k Ck
  rw [hz,map_zero,sub_zero] at hb
  refine ⟨E,W,?_,?_,relative_deformation_current_support F I P C hCK,
    relative_deformation_current_mass F I P Local C hCK⟩
  · change I.boundary k (P.push (k+1) ⟨C,hCK.trans F.contains⟩) = 0
    rw [P.boundary_comm]
    have he : supportedBoundary I F.neighborhood k ⟨C,hCK.trans F.contains⟩ = 0 := Subtype.ext hC
    rw [he,map_zero]
  · change C-E = I.boundary (k+1) (-_)
    rw [map_neg,hb]
    change C-E = -(E-C)
    abel

include Local in
theorem relative_deformation_preserves_boundary {k : ℕ} (C : I.Current (k+1))
    (hCK : I.support C ⊆ K) (hRel : I.support (I.boundary k C) ⊆ R) :
    I.boundary k (P.push (k+1) ⟨C,hCK.trans F.contains⟩) = I.boundary k C := by
  rw [P.boundary_comm]
  apply Local.identity_on_support
  intro x hx
  have hxK := hCK (I.support_boundary_subset k C hx)
  rw [relativeDeformationExtension,openNeighborhoodExtension_apply F.map x (F.contains hxK)]
  exact F.map_fixed ⟨x,F.contains hxK⟩ (hRel hx)

end Paper28
