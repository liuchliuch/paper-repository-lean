import Paper28.L2CoordinateProjections
import Mathlib.Topology.Compactness.Compact

/-! A single actual finite-coordinate projection approximates an entire
compact subset of l2, with arbitrarily small error. This is the finite-net
construction used in Lemma 5.1, proved rather than supplied as an input. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {ι : Type*} [DecidableEq ι]

theorem exists_l2CoordinateProjection_uniform_close (K : Set (CoordinateHilbert ι))
    (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset ι, ∀ u ∈ K, ‖l2CoordinateProjection F u - u‖ < ε := by
  classical
  let ρ := ε / 4
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hcover : K ⊆ ⋃ x : K, ball x.val ρ := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩, by simpa only [mem_ball, dist_self] using hρ⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun x : K => ball x.val ρ) (fun _ => isOpen_ball) hcover
  choose F hF using fun x : K => exists_l2CoordinateProjection_close x.val ρ hρ
  let E := s.biUnion F
  refine ⟨E, ?_⟩
  intro u hu
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp (hs hu)
  obtain ⟨hxs,hux⟩ := Set.mem_iUnion.mp hx
  have hFE : F x ⊆ E := Finset.subset_biUnion_of_mem F hxs
  have hxError : ‖l2CoordinateProjection E x.val - x.val‖ < ρ :=
    (l2CoordinateProjection_error_mono (F x) E hFE x.val).trans_lt (hF x)
  have hd : ‖u-x.val‖ < ρ := by simpa only [mem_ball, dist_eq_norm] using hux
  have he : l2CoordinateProjection E u - u =
      l2CoordinateProjection E (u-x.val) + (l2CoordinateProjection E x.val-x.val) + (x.val-u) := by
    rw [map_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖l2CoordinateProjection E (u-x.val)‖ + ‖l2CoordinateProjection E x.val-x.val‖ + ‖x.val-u‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ ‖u-x.val‖ + ‖l2CoordinateProjection E x.val-x.val‖ + ‖x.val-u‖ :=
      add_le_add_right (add_le_add_right (l2CoordinateProjection_norm_le E (u-x.val)) _) _
    _ < ε := by rw [norm_sub_rev x.val u]; dsimp [ρ] at *; linarith

end Paper28
