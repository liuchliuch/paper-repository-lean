import Paper28.RegularSphereAction

/-! Closed small chart balls have closed images in the actual orbit quotient.
Local finiteness of their translates is derived from the native regular
coefficient estimates, and will give compact chart lifts of compact sets. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G : Type*} [Group G] [DecidableEq G]

/-- Fixed-radius translates of a closed chart ball form a locally finite
family whenever the radius is less than one in the ambient sphere metric. -/
theorem regular_closedBall_translates_locallyFinite (c : RegularSphere G) (r : ℝ) (hr : r < 1) :
    LocallyFinite (fun γ : G => (γ • ·) '' closedBall c r) := by
  intro u
  let ρ := (1-r)/2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  refine ⟨ball u ρ,ball_mem_nhds u hρ,?_⟩
  apply (regular_near_translates_finite u.val c.val u.property c.property).subset
  intro γ hγ
  obtain ⟨x,⟨y,hy,hxy⟩,hx⟩ := hγ
  change dist u.val (leftRegular γ c.val) < 1
  have hux : dist u x < ρ := by simpa only [mem_ball,dist_comm] using hx
  have hyc : dist y c ≤ r := hy
  have he : dist x (γ • c) = dist y c := by
    rw [← hxy]
    exact (isometry_smul (RegularSphere G) γ).dist_eq y c
  have ht := dist_triangle u x (γ • c)
  rw [he] at ht
  change dist u (γ • c) < 1
  dsimp [ρ] at hux
  linarith

/-- A closed subset of a small closed chart ball has a closed image in X_G. -/
theorem regular_quotient_closed_image (c : RegularSphere G) (r : ℝ) (hr : r < 1)
    (S : Set (RegularSphere G)) (hS : IsClosed S) (hSB : S ⊆ closedBall c r) :
    IsClosed ((regularQuotientMap : RegularSphere G → RegularOrbitQuotient G) '' S) := by
  letI : Setoid (RegularSphere G) := MulAction.orbitRel G (RegularSphere G)
  change IsClosed ((Quotient.mk' : RegularSphere G → RegularOrbitQuotient G) '' S)
  rw [isClosed_coinduced,MulAction.quotient_preimage_image_eq_union_mul]
  apply ((regular_closedBall_translates_locallyFinite c r hr).subset
    (fun γ => Set.image_mono hSB)).isClosed_iUnion
  intro γ
  exact (Homeomorph.smul γ).isClosedMap S hS

end Paper28
