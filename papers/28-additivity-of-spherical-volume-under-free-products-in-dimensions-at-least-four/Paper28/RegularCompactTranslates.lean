import Paper28.RegularStabilizers
import Mathlib.Topology.Compactness.Compact

/-! Finitely many translates of a compact lifted polyhedron can meet a
fixed small sphere chart. This is the relative-support finiteness required
before enlarging the invariant coordinate projections in Lemma 5.1. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G : Type*} [Group G] [DecidableEq G]

theorem regular_compact_near_translates_finite (u : CoordinateHilbert G) (hu : ‖u‖ = 1)
    (K : Set (CoordinateHilbert G)) (hK : IsCompact K) (hUnit : ∀ x ∈ K, ‖x‖ = 1) :
    {γ : G | ∃ x ∈ K, dist u (leftRegular γ x) < (1/2 : ℝ)}.Finite := by
  classical
  have hcover : K ⊆ ⋃ x : K, ball x.val (1/4 : ℝ) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,by simp⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun x : K => ball x.val (1/4 : ℝ))
    (fun _ => isOpen_ball) hcover
  let F := s.biUnion (fun x : K =>
    (regular_near_translates_finite u x.val hu (hUnit x.val x.property)).toFinset)
  apply F.finite_toSet.subset
  rintro γ ⟨x,hx,hγ⟩
  obtain ⟨c,hc⟩ := Set.mem_iUnion.mp (hs hx)
  obtain ⟨hcs,hxc⟩ := Set.mem_iUnion.mp hc
  apply Finset.mem_biUnion.mpr
  refine ⟨c,hcs,?_⟩
  rw [Set.Finite.mem_toFinset]
  change dist u (leftRegular γ c.val) < 1
  have hclose : dist x c.val < (1/4 : ℝ) := hxc
  have hi : dist (leftRegular γ x) (leftRegular γ c.val) = dist x c.val :=
    (leftRegular γ).isometry.dist_eq x c.val
  have ht := dist_triangle u (leftRegular γ x) (leftRegular γ c.val)
  rw [hi] at ht
  linarith

end Paper28
