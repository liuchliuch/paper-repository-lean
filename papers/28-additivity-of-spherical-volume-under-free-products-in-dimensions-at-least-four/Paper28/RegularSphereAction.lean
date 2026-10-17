import Paper28.CarrierLocalFiniteness
import Paper28.RegularCompactTranslates
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.Algebra.ProperAction.ProperlyDiscontinuous

/-! The actual regular action on the native unit sphere, its properly
discontinuous compact-transporter property, and its actual orbit quotient.
No abstract quotient/current/volume surrogate is defined here. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G : Type*} [Group G] [DecidableEq G]

instance regularSphereMulAction : MulAction G (RegularSphere G) where
  smul γ u := ⟨leftRegular γ u.val, by rw [(leftRegular γ).norm_map,u.property]⟩
  one_smul u := Subtype.ext (leftRegular_one u.val)
  mul_smul γ δ u := Subtype.ext (leftRegular_mul γ δ u.val)

@[simp] theorem regularSphere_smul_val (γ : G) (u : RegularSphere G) :
    (γ • u).val = leftRegular γ u.val := rfl

instance regularSphereIsIsometricSMul : IsIsometricSMul G (RegularSphere G) where
  isometry_smul γ := Isometry.of_dist_eq (fun u v => (leftRegular γ).isometry.dist_eq u.val v.val)

/-- Native compact-transporter finiteness on the actual regular sphere. -/
theorem regular_compact_transport_finite (K L : Set (CoordinateHilbert G))
    (hK : IsCompact K) (hL : IsCompact L)
    (hKU : ∀ x ∈ K, ‖x‖ = 1) (hLU : ∀ x ∈ L, ‖x‖ = 1) :
    {γ : G | ∃ x ∈ K, leftRegular γ x ∈ L}.Finite := by
  classical
  have hc : L ⊆ ⋃ y : L, ball y.val (1/2 : ℝ) := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y,hy⟩,by simp⟩
  obtain ⟨s,hs⟩ := hL.elim_finite_subcover (fun y : L => ball y.val (1/2 : ℝ))
    (fun _ => isOpen_ball) hc
  let F := s.biUnion (fun y : L =>
    (regular_compact_near_translates_finite y.val (hLU y.val y.property) K hK hKU).toFinset)
  apply F.finite_toSet.subset
  rintro γ ⟨x,hx,hγx⟩
  obtain ⟨y,hy⟩ := Set.mem_iUnion.mp (hs hγx)
  obtain ⟨hys,hxy⟩ := Set.mem_iUnion.mp hy
  apply Finset.mem_biUnion.mpr
  refine ⟨y,hys,?_⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨x,hx,?_⟩
  simpa only [mem_ball,dist_comm] using hxy

instance regularSphereProperlyDiscontinuous : ProperlyDiscontinuousSMul G (RegularSphere G) where
  finite_disjoint_inter_image := by
    intro K L hK hL
    have hf := regular_compact_transport_finite (Subtype.val '' K) (Subtype.val '' L)
      (hK.image continuous_subtype_val) (hL.image continuous_subtype_val)
      (by rintro x ⟨u,_,rfl⟩; exact u.property)
      (by rintro x ⟨u,_,rfl⟩; exact u.property)
    apply hf.subset
    intro γ hγ
    obtain ⟨y,⟨x,hx,hxy⟩,hy⟩ := Set.nonempty_iff_ne_empty.mpr hγ
    refine ⟨x.val,Set.mem_image_of_mem _ hx,?_⟩
    exact ⟨y,hy,congrArg Subtype.val hxy.symm⟩

/-- The source quotient X_G as the actual orbit quotient of the native
regular Hilbert unit sphere (the round metric is handled separately). -/
abbrev RegularOrbitQuotient (G : Type*) [Group G] [DecidableEq G] :=
  Quotient (MulAction.orbitRel G (RegularSphere G))

def regularQuotientMap : RegularSphere G → RegularOrbitQuotient G :=
  Quotient.mk (MulAction.orbitRel G (RegularSphere G))

theorem regularQuotientMap_continuous : Continuous (regularQuotientMap : RegularSphere G → RegularOrbitQuotient G) :=
  continuous_quot_mk

instance regularSphereProperSMul [TopologicalSpace G] [DiscreteTopology G] :
    ProperSMul G (RegularSphere G) :=
  properlyDiscontinuousSMul_iff_properSMul.mp inferInstance

instance regularOrbitQuotientT2 [TopologicalSpace G] [DiscreteTopology G] :
    T2Space (RegularOrbitQuotient G) := t2Space_quotient_mulAction_of_properSMul

end Paper28
