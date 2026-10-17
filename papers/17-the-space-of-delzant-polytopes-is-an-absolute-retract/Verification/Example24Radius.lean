import Verification.EuclideanNormalization
import Paper17.Example24Geometry

/-! The actual Euclidean radius and exact `3t` error in Example 2.4. -/
noncomputable section
open scoped BigOperators Pointwise Topology
namespace Paper17.Example24

def prismPoint (p : V 2) (z : ℝ) : V 3 := ![p 0, p 1, z]

def prism (P : Polytope 2) (a : ℝ) : Polytope 3 where
  verts := (P.verts.product {0, a}).image (fun q => prismPoint q.1 q.2)
  nonempty_verts' := by
    obtain ⟨p, hp⟩ := P.nonempty_verts'
    exact ⟨prismPoint p 0, Finset.mem_image.mpr
      ⟨(p, 0), Finset.mem_product.mpr ⟨hp, by simp⟩, rfl⟩⟩

def hexagon : Polytope 2 where
  verts := Tverts
  nonempty_verts' := ⟨vec2 2 (-2), by simp [Tverts]⟩

def exampleS : Polytope 3 := prism hexagon 1

theorem norm_prismPoint_sq (p : V 2) (z : ℝ) :
    ‖P17Contract.euclideanCoordinates 3 (prismPoint p z)‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + z ^ 2 := by
  rw [P17Contract.norm_euclideanCoordinates_sq]
  simp [prismPoint, Fin.sum_univ_succ]
  ring

/-- The whole actual convex prism has radius at most three, not just its
listed vertices. Convexity transports the finite vertex bound. -/
theorem exampleS_norm_le_three : ∀ x ∈ exampleS.carrier,
    ‖P17Contract.euclideanCoordinates 3 x‖ ≤ 3 := by
  classical
  let e := P17Contract.euclideanCoordinates 3
  have hc : Convex ℝ {x : V 3 | e x ∈ Metric.closedBall 0 3} :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 3).linear_preimage e.toLinearMap
  have hv : (exampleS.verts : Set (V 3)) ⊆ {x | e x ∈ Metric.closedBall 0 3} := by
    intro x hx
    obtain ⟨⟨p, z⟩, hpz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hp, hz⟩ := Finset.mem_product.mp hpz
    change p ∈ Tverts at hp
    have hp' : p = vec2 2 (-2) ∨ p = vec2 2 1 ∨ p = vec2 1 2 ∨
        p = vec2 (-1) 2 ∨ p = vec2 (-2) 1 ∨ p = vec2 (-2) (-2) := by
      simpa only [Tverts, Finset.mem_insert, Finset.mem_singleton] using hp
    have hz' : z = 0 ∨ z = 1 := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
    change e (prismPoint p z) ∈ Metric.closedBall 0 3
    rw [Metric.mem_closedBall, dist_zero_right]
    have hh := norm_prismPoint_sq p z
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hz' with rfl | rfl
    all_goals
      simp only [vec2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hh
      norm_num at hh
      dsimp only [e]
      simp only [vec2]
      nlinarith
  intro x hx
  have hh := convexHull_min hv hc hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using hh

/-- The advertised radius is attained at the actual point `(2,-2,1)`. -/
theorem exampleS_radius_attained :
    prismPoint (vec2 2 (-2)) 1 ∈ exampleS.carrier ∧
      ‖P17Contract.euclideanCoordinates 3 (prismPoint (vec2 2 (-2)) 1)‖ = 3 := by
  constructor
  · apply subset_convexHull ℝ _
    apply Finset.mem_image.mpr
    refine ⟨(vec2 2 (-2), 1), Finset.mem_product.mpr ⟨?_, by simp⟩, rfl⟩
    simp [hexagon, Tverts]
  · have hh := norm_prismPoint_sq (vec2 2 (-2)) 1
    norm_num [vec2] at hh
    have hn := norm_nonneg (P17Contract.euclideanCoordinates 3 (prismPoint (vec2 2 (-2)) 1))
    simp only [vec2] at hn ⊢
    nlinarith

/-- The Euclidean support norm of the actual three-dimensional prism is 3. -/
theorem exampleS_support_norm :
    ‖Paper17.EuclideanSupport.sphereSupport
      (P17Contract.euclideanCoordinates 3 '' exampleS.carrier)
      (exampleS.isCompact.image (P17Contract.euclideanCoordinates 3).continuous)‖ = 3 := by
  obtain ⟨hx, hnorm⟩ := exampleS_radius_attained
  apply Paper17.EuclideanSupport.norm_sphereSupport_eq_radius
    (exampleS.isCompact.image (P17Contract.euclideanCoordinates 3).continuous)
    (exampleS.nonempty.image _) (by norm_num : (0 : ℝ) < 3)
    (by rintro x ⟨y, hy, rfl⟩; exact exampleS_norm_le_three y hy)
    ⟨prismPoint (vec2 2 (-2)) 1, hx, rfl⟩ hnorm

/-- The exact source `3t` equality holds for the actual Minkowski perturbation
of every compact convex polytope, in particular the prism `A × [0,1]`. -/
theorem example24_exact_euclidean_error (P : Polytope 3) {t : ℝ} (ht : 0 < t) :
    P17Contract.euclideanHausdorffDist (P.add (exampleS.smul t)).carrier P.carrier = 3 * t := by
  let e := P17Contract.euclideanCoordinates 3
  rw [P17Contract.euclideanHausdorffDist, carrier_add_eq, carrier_smul_eq,
    P17Contract.euclidean_image_add, P17Contract.euclidean_image_smul]
  rw [Paper17.EuclideanSupport.hausdorffDist_add_smul_eq
    (P.isCompact.image e.continuous) (P.nonempty.image e) (P.convex.linear_image e.toLinearMap)
    (exampleS.isCompact.image e.continuous) (exampleS.nonempty.image e)
    (exampleS.convex.linear_image e.toLinearMap) ht.le, exampleS_support_norm, mul_comm]

end Paper17.Example24
