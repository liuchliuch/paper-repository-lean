import Paper28.CoordinateSphereAngularGluing
import Paper28.CoordinateSphereBridge

/-! Native local distance control across two coordinate spheres. The
intermediate points lie in their actual intersection, and all three
distance estimates follow from the finite closed cell gluing theorem. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G Z : Type*} [Group G] [DecidableEq G] [PseudoMetricSpace Z]

theorem coordinate_spheres_cellwise_distance_bound (E F : Finset G) (f : RegularSphere G → Z)
    (hE : ∀ p ∈ coordinateSphereCellIndices E,
      ∀ v ∈ closedSignedBarycentricCell p.1 p.2,
      ∀ w ∈ closedSignedBarycentricCell p.1 p.2, dist (f v) (f w) ≤ angular v.val w.val)
    (hF : ∀ p ∈ coordinateSphereCellIndices F,
      ∀ v ∈ closedSignedBarycentricCell p.1 p.2,
      ∀ w ∈ closedSignedBarycentricCell p.1 p.2, dist (f v) (f w) ≤ angular v.val w.val)
    (u v w : RegularSphere G)
    (huE : u.val ∈ coordinateSupportSubspace E) (huF : u.val ∈ coordinateSupportSubspace F)
    (hv : v.val ∈ coordinateSupportSubspace E) (hw : w.val ∈ coordinateSupportSubspace F)
    (hvu : ‖v.val-u.val‖ ≤ 1/4) (hwu : ‖w.val-u.val‖ ≤ 1/4) :
    dist (f v) (f w) ≤ 16*Real.pi*‖v.val-w.val‖ := by
  obtain ⟨p,q,_,_,hp,hq,hpu,hqu,hSum,_⟩ :=
    coordinate_sphere_common_projection_bridge E F u v w huE huF hv hw hvu hwu
  have hpE := coordinateSupportSubspace_mono (E ∩ F) E Finset.inter_subset_left hp
  have hqF := coordinateSupportSubspace_mono (E ∩ F) F Finset.inter_subset_right hq
  have hEF : ∀ a ∈ coordinateSphereCellIndices (E ∩ F),
      ∀ x ∈ closedSignedBarycentricCell a.1 a.2,
      ∀ y ∈ closedSignedBarycentricCell a.1 a.2, dist (f x) (f y) ≤ angular x.val y.val :=
    fun a ha => hE a (coordinateSphereCellIndices_mono Finset.inter_subset_left ha)
  have hVP := coordinate_sphere_cellwise_angular_bound E f hE u v p hv hpE (by linarith) hpu
  have hPQ := coordinate_sphere_cellwise_angular_bound (E ∩ F) f hEF u p q hp hq hpu hqu
  have hQW := coordinate_sphere_cellwise_angular_bound F f hF u q w hqF hw hqu (by linarith)
  calc
    _ ≤ dist (f v) (f p)+dist (f p) (f q)+dist (f q) (f w) := by
      have h₁ := dist_triangle (f v) (f p) (f w)
      have h₂ := dist_triangle (f p) (f q) (f w)
      linarith
    _ ≤ 2*Real.pi*‖v.val-p.val‖+2*Real.pi*‖p.val-q.val‖+2*Real.pi*‖q.val-w.val‖ :=
      add_le_add (add_le_add hVP hPQ) hQW
    _ = (2*Real.pi)*(‖v.val-p.val‖+‖p.val-q.val‖+‖q.val-w.val‖) := by ring
    _ ≤ (2*Real.pi)*(8*‖v.val-w.val‖) := mul_le_mul_of_nonneg_left hSum (by positivity)
    _ = _ := by ring

end Paper28
