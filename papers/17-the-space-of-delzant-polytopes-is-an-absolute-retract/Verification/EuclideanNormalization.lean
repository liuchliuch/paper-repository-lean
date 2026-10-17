import Verification.SphericalSupport
import Verification.ApproximationControl
import Paper17.EuclideanSupport
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Exact source Euclidean normalization of the support-function embedding. -/
noncomputable section
open scoped Topology BigOperators Pointwise
namespace P17Contract

/-- Coordinates with their actual Euclidean norm. -/
def euclideanCoordinates (n : ℕ) : V n ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm

@[simp] theorem inner_euclideanCoordinates {n : ℕ} (x y : V n) :
    inner ℝ (euclideanCoordinates n x) (euclideanCoordinates n y) = Paper17.dot x y := by
  simp [euclideanCoordinates, EuclideanSpace.equiv, PiLp.inner_apply, Paper17.dot,
    RCLike.inner_apply, mul_comm]

theorem norm_euclideanCoordinates_sq {n : ℕ} (x : V n) :
    ‖euclideanCoordinates n x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_euclideanCoordinates]
  simp only [Paper17.dot, pow_two]

theorem norm_euclideanCoordinates_eq_one_iff {n : ℕ} (x : V n) :
    ‖euclideanCoordinates n x‖ = 1 ↔ ∑ i, x i ^ 2 = 1 := by
  have hn := norm_euclideanCoordinates_sq x
  have hpos := norm_nonneg (euclideanCoordinates n x)
  constructor <;> intro hx <;> nlinarith

/-- The paper's coordinate sphere and the genuine Euclidean metric sphere
are related by the actual coordinate homeomorphism. -/
def euclideanDirectionHomeomorph (n : ℕ) : UnitDirections n ≃ₜ
    Paper17.EuclideanSupport.Directions (EuclideanSpace ℝ (Fin n)) where
  toFun u := ⟨euclideanCoordinates n u.val, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact (norm_euclideanCoordinates_eq_one_iff u.val).mpr u.property⟩
  invFun u := ⟨(euclideanCoordinates n).symm u.val, by
    apply (norm_euclideanCoordinates_eq_one_iff _).mp
    rw [ContinuousLinearEquiv.apply_symm_apply]
    simpa only [Metric.mem_sphere, dist_zero_right] using u.property⟩
  left_inv u := Subtype.ext ((euclideanCoordinates n).symm_apply_apply u.val)
  right_inv u := Subtype.ext ((euclideanCoordinates n).apply_symm_apply u.val)
  continuous_toFun := ((euclideanCoordinates n).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((euclideanCoordinates n).symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- Actual Euclidean Hausdorff distance between coordinate carriers. -/
def euclideanHausdorffDist {n : ℕ} (K L : Set (V n)) : ℝ :=
  Metric.hausdorffDist (euclideanCoordinates n '' K) (euclideanCoordinates n '' L)

theorem euclidean_support_image {n : ℕ} (K : Set (V n)) (u : V n) :
    Paper17.EuclideanSupport.support (euclideanCoordinates n '' K) (euclideanCoordinates n u) =
      Paper17.supportFunction K u := by
  unfold Paper17.EuclideanSupport.support Paper17.supportFunction
  congr 1
  ext b
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, (inner_euclideanCoordinates u y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨euclideanCoordinates n y, ⟨y, hy, rfl⟩, inner_euclideanCoordinates u y⟩

/-- Support of every canonical positive body on the source Euclidean sphere. -/
def bodySphericalSupport {n : ℕ} (K : PosBody n) : PaperSupportSpace n :=
  sphericalRestriction n (bodySupport K)

@[simp] theorem bodySphericalSupport_apply {n : ℕ} (K : PosBody n) (u : UnitDirections n) :
    bodySphericalSupport K u = Paper17.supportFunction K.carrier u.val := by
  change directionL1 u * Paper17.supportFunction K.carrier ((directionL1 u)⁻¹ • u.val) = _
  rw [Paper17.supportFunction_direction_smul K.isCompact K.nonempty u.val
    (inv_nonneg.mpr (directionL1_pos u).le), ← mul_assoc,
    mul_inv_cancel₀ (directionL1_pos u).ne', one_mul]

private theorem norm_precomp_homeomorph {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [CompactSpace A] [CompactSpace B] (e : B ≃ₜ A) (f : C(A, ℝ)) :
    ‖f.comp (⟨e, e.continuous⟩ : C(B, A))‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro b
    exact f.norm_coe_le_norm (e b)
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro a
    obtain ⟨b, rfl⟩ := e.surjective a
    exact (f.comp (⟨e, e.continuous⟩ : C(B, A))).norm_coe_le_norm b

/-- Equation (2.1), with precisely the source Euclidean Hausdorff distance
and its continuous-function norm on the Euclidean unit sphere. -/
theorem euclideanHausdorffDist_eq_norm_sphericalSupport {n : ℕ} (K L : PosBody n) :
    euclideanHausdorffDist K.carrier L.carrier =
      ‖bodySphericalSupport K - bodySphericalSupport L‖ := by
  let e := euclideanCoordinates n
  have hK := K.isCompact.image e.continuous
  have hL := L.isCompact.image e.continuous
  have hneK := K.nonempty.image e
  have hneL := L.nonempty.image e
  have hcK := K.convex.linear_image e.toLinearMap
  have hcL := L.convex.linear_image e.toLinearMap
  rw [euclideanHausdorffDist,
    Paper17.EuclideanSupport.hausdorffDist_eq_norm_support_sub hK hneK hcK hL hneL hcL]
  rw [← norm_precomp_homeomorph (euclideanDirectionHomeomorph n)]
  congr 1
  ext u
  change Paper17.EuclideanSupport.support (e '' K.carrier) (euclideanCoordinates n u.val) -
    Paper17.EuclideanSupport.support (e '' L.carrier) (euclideanCoordinates n u.val) = _
  rw [euclidean_support_image, euclidean_support_image]
  simp only [ContinuousMap.sub_apply, bodySphericalSupport_apply]

/-- The coordinate equivalence respects actual Minkowski carriers. -/
theorem euclidean_image_add {n : ℕ} (K L : Set (V n)) :
    euclideanCoordinates n '' (K + L) =
      euclideanCoordinates n '' K + euclideanCoordinates n '' L := by
  ext z
  constructor
  · rintro ⟨w, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨euclideanCoordinates n x, ⟨x, hx, rfl⟩,
      euclideanCoordinates n y, ⟨y, hy, rfl⟩,
      ((euclideanCoordinates n).map_add x y).symm⟩
  · rintro ⟨w, ⟨x, hx, rfl⟩, v, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x + y, ⟨x, hx, y, hy, rfl⟩, (euclideanCoordinates n).map_add x y⟩

theorem euclidean_image_smul {n : ℕ} (K : Set (V n)) (t : ℝ) :
    euclideanCoordinates n '' (t • K) = t • (euclideanCoordinates n '' K) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hw
    apply Set.mem_smul_set.mpr
    exact ⟨euclideanCoordinates n x, ⟨x, hx, rfl⟩,
      ((euclideanCoordinates n).map_smul t x).symm⟩
  · intro hz
    obtain ⟨w, ⟨x, hx, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hz
    exact ⟨t • x, Set.smul_mem_smul_set hx, (euclideanCoordinates n).map_smul t x⟩

end P17Contract
