import Paper17.SupportBounds
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.ContinuousMap.Compact

/-! The exact support/Hausdorff isometry on the Euclidean unit sphere.
This proof uses the inner-product norm itself, not a coordinate sup norm. -/
noncomputable section
open scoped Topology Pointwise
namespace Paper17.EuclideanSupport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Support in the actual Euclidean inner product. -/
def support (K : Set E) (u : E) : ℝ := sSup ((fun x => inner ℝ u x) '' K)

theorem exists_support_max {K : Set E} (hc : IsCompact K) (hne : K.Nonempty) (u : E) :
    ∃ x ∈ K, support K u = inner ℝ u x := by
  obtain ⟨x, hx, hmax⟩ := hc.exists_isMaxOn hne
    ((continuous_const.inner continuous_id).continuousOn :
      ContinuousOn (fun y : E => inner ℝ u y) K)
  refine ⟨x, hx, le_antisymm ?_ ?_⟩
  · exact csSup_le (hne.image _) (by rintro _ ⟨y, hy, rfl⟩; exact hmax hy)
  · exact le_csSup (hc.bddAbove_image (continuous_const.inner continuous_id).continuousOn)
      ⟨x, hx, rfl⟩

theorem le_support {K : Set E} (hc : IsCompact K) {x : E} (hx : x ∈ K) (u : E) :
    inner ℝ u x ≤ support K u :=
  le_csSup (hc.bddAbove_image (continuous_const.inner continuous_id).continuousOn) ⟨x, hx, rfl⟩

theorem continuous_support {K : Set E} (hc : IsCompact K) : Continuous (support K) := by
  apply hc.continuous_sSup
  exact continuous_inner

@[simp] theorem support_zero {K : Set E} (hc : IsCompact K) (hne : K.Nonempty) :
    support K 0 = 0 := by
  obtain ⟨x, hx, heq⟩ := exists_support_max hc hne 0
  simpa only [inner_zero_left] using heq

theorem support_direction_smul {K : Set E} (hc : IsCompact K) (hne : K.Nonempty)
    (u : E) {t : ℝ} (ht : 0 ≤ t) : support K (t • u) = t * support K u := by
  obtain ⟨x, hx, hmax⟩ := exists_support_max hc hne u
  obtain ⟨y, hy, hymax⟩ := exists_support_max hc hne (t • u)
  apply le_antisymm
  · rw [hymax, real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (le_support hc hy u) ht
  · rw [hmax, ← real_inner_smul_left]
    exact le_support hc hx (t • u)

theorem support_add {K L : Set E} (hK : IsCompact K) (hneK : K.Nonempty)
    (hL : IsCompact L) (hneL : L.Nonempty) (u : E) :
    support (K + L) u = support K u + support L u := by
  obtain ⟨x, hx, hmax⟩ := exists_support_max hK hneK u
  obtain ⟨y, hy, hymax⟩ := exists_support_max hL hneL u
  apply le_antisymm
  · obtain ⟨z, ⟨a, ha, b, hb, rfl⟩, hz⟩ := exists_support_max (hK.add hL) (hneK.add hneL) u
    rw [hz, inner_add_right]
    exact add_le_add (le_support hK ha u) (le_support hL hb u)
  · rw [hmax, hymax, ← inner_add_right]
    exact le_support (hK.add hL) (Set.add_mem_add hx hy) u

/-- The Euclidean ball has support `r * ‖u‖`. -/
theorem support_closedBall (r : ℝ) (hr : 0 ≤ r) (u : E) :
    support (Metric.closedBall (0 : E) r) u = r * ‖u‖ := by
  apply le_antisymm
  · obtain ⟨x, hx, hmax⟩ := exists_support_max (isCompact_closedBall _ _)
      ⟨0, Metric.mem_closedBall_self hr⟩ u
    rw [hmax]
    calc inner ℝ u x ≤ ‖u‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ ‖u‖ * r := mul_le_mul_of_nonneg_left
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx) (norm_nonneg _)
      _ = r * ‖u‖ := mul_comm _ _
  · by_cases hu : u = 0
    · have hz := support_zero (E := E) (K := Metric.closedBall (0 : E) r)
        (isCompact_closedBall _ _) ⟨0, Metric.mem_closedBall_self hr⟩
      simp [hu, hz]
    have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
    let x : E := (r / ‖u‖) • u
    have hx : x ∈ Metric.closedBall (0 : E) r := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hr hun.le), div_mul_cancel₀ _ hun.ne']
    have hpair : inner ℝ u x = r * ‖u‖ := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    rw [← hpair]
    exact le_support (isCompact_closedBall _ _) hx u

/-- Euclidean support inequalities characterize membership in compact convex
sets; Riesz representation identifies the separating functional. -/
theorem subset_of_support {K L : Set E} (hL : IsCompact L) (hne : L.Nonempty)
    (hconv : Convex ℝ L) (h : ∀ u x, x ∈ K → inner ℝ u x ≤ support L u) : K ⊆ L := by
  intro x hx
  by_contra hn
  obtain ⟨f, b, hf, hfx⟩ := geometric_hahn_banach_closed_point hconv hL.isClosed hn
  let u := (InnerProductSpace.toDual ℝ E).symm f
  have hu : ∀ y, inner ℝ u y = f y := fun y => InnerProductSpace.toDual_symm_apply
  have hbound : support L u ≤ b := by
    obtain ⟨y, hy, hm⟩ := exists_support_max hL hne u
    rw [hm, hu]
    exact (hf y hy).le
  have hle := (h u x hx).trans hbound
  rw [hu] at hle
  exact (not_lt_of_ge hle) hfx

/-- A Hausdorff bound controls support in every Euclidean direction. -/
theorem support_sub_le_hausdorff_mul {K L : Set E} (hK : IsCompact K) (hneK : K.Nonempty)
    (hL : IsCompact L) (hneL : L.Nonempty) (u : E) :
    support K u - support L u ≤ Metric.hausdorffDist K L * ‖u‖ := by
  have hfin : EMetric.hausdorffEdist K L ≠ ⊤ :=
    Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded hneK hneL hK.isBounded hL.isBounded
  obtain ⟨x, hx, hmax⟩ := exists_support_max hK hneK u
  obtain ⟨y, hy, hyd⟩ := hL.exists_infDist_eq_dist hneL x
  have hxy : dist x y ≤ Metric.hausdorffDist K L :=
    hyd ▸ Metric.infDist_le_hausdorffDist_of_mem hx hfin
  have hyb := le_support hL hy u
  calc support K u - support L u ≤ inner ℝ u x - inner ℝ u y := by rw [hmax]; linarith
    _ = inner ℝ u (x - y) := (inner_sub_right _ _ _).symm
    _ ≤ ‖u‖ * ‖x - y‖ := real_inner_le_norm _ _
    _ ≤ ‖u‖ * Metric.hausdorffDist K L := mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hxy) (norm_nonneg _)
    _ = Metric.hausdorffDist K L * ‖u‖ := mul_comm _ _

/-- The source Euclidean unit sphere. -/
abbrev Directions (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1

instance directions_compact : CompactSpace (Directions E) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

/-- A continuous support function on the actual Euclidean unit sphere. -/
def sphereSupport (K : Set E) (hc : IsCompact K) : C(Directions E, ℝ) :=
  ⟨fun u => support K u.val, (continuous_support hc).comp continuous_subtype_val⟩

theorem norm_support_sub_le {K L : Set E} (hK : IsCompact K) (hneK : K.Nonempty)
    (hL : IsCompact L) (hneL : L.Nonempty) :
    ‖sphereSupport K hK - sphereSupport L hL‖ ≤ Metric.hausdorffDist K L := by
  apply (ContinuousMap.norm_le _ Metric.hausdorffDist_nonneg).mpr
  intro u
  change |support K u.val - support L u.val| ≤ _
  have hun : ‖u.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  apply abs_le.mpr ⟨?_, ?_⟩
  · have hh := support_sub_le_hausdorff_mul hL hneL hK hneK u.val
    rw [Metric.hausdorffDist_comm, hun, mul_one] at hh
    linarith
  · simpa only [hun, mul_one] using support_sub_le_hausdorff_mul hK hneK hL hneL u.val

/-- Unit-sphere support control scales to all directions. -/
theorem support_sub_le_norm_mul {K L : Set E} (hK : IsCompact K) (hneK : K.Nonempty)
    (hL : IsCompact L) (hneL : L.Nonempty) (u : E) :
    support K u - support L u ≤ ‖sphereSupport K hK - sphereSupport L hL‖ * ‖u‖ := by
  by_cases hu : u = 0
  · simp [hu, support_zero hK hneK, support_zero hL hneL]
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let v : Directions E := ⟨‖u‖⁻¹ • u, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hun), inv_mul_cancel₀ hun.ne']⟩
  have hv := (sphereSupport K hK - sphereSupport L hL).norm_coe_le_norm v
  change |support K (‖u‖⁻¹ • u) - support L (‖u‖⁻¹ • u)| ≤ _ at hv
  rw [support_direction_smul hK hneK u (inv_nonneg.mpr hun.le),
    support_direction_smul hL hneL u (inv_nonneg.mpr hun.le)] at hv
  have hm := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hv) hun.le
  have heq : ‖u‖ * (‖u‖⁻¹ * support K u - ‖u‖⁻¹ * support L u) = support K u - support L u := by
    rw [← mul_sub, ← mul_assoc, mul_inv_cancel₀ hun.ne', one_mul]
  rw [heq] at hm
  simpa only [mul_comm] using hm

/-- Equation (2.1), with the exact Euclidean Hausdorff metric and sphere
supremum norm, for all nonempty compact convex carriers. -/
theorem hausdorffDist_eq_norm_support_sub {K L : Set E}
    (hK : IsCompact K) (hneK : K.Nonempty) (hconvK : Convex ℝ K)
    (hL : IsCompact L) (hneL : L.Nonempty) (hconvL : Convex ℝ L) :
    Metric.hausdorffDist K L = ‖sphereSupport K hK - sphereSupport L hL‖ := by
  apply le_antisymm ?_ (norm_support_sub_le hK hneK hL hneL)
  let r := ‖sphereSupport K hK - sphereSupport L hL‖
  have hr : 0 ≤ r := norm_nonneg _
  have hinc : ∀ A B : Set E, ∀ (hA : IsCompact A) (hneA : A.Nonempty) (hconvA : Convex ℝ A)
      (hB : IsCompact B) (hneB : B.Nonempty) (hconvB : Convex ℝ B),
      ‖sphereSupport A hA - sphereSupport B hB‖ = r →
        A ⊆ B + Metric.closedBall 0 r := by
    intro A B hA hneA hconvA hB hneB hconvB hnorm
    apply subset_of_support (hB.add (isCompact_closedBall _ _))
      (hneB.add ⟨0, Metric.mem_closedBall_self hr⟩) (hconvB.add (convex_closedBall _ _))
    intro u x hx
    rw [support_add hB hneB (isCompact_closedBall _ _) ⟨0, Metric.mem_closedBall_self hr⟩,
      support_closedBall r hr]
    have hh := support_sub_le_norm_mul hA hneA hB hneB u
    rw [hnorm] at hh
    linarith [le_support hA hx u]
  apply Metric.hausdorffDist_le_of_mem_dist hr
  · intro x hx
    obtain ⟨y, hy, z, hz, hxyz⟩ := hinc K L hK hneK hconvK hL hneL hconvL rfl hx
    refine ⟨y, hy, ?_⟩
    rw [← hxyz, dist_eq_norm, add_sub_cancel_left]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  · intro x hx
    obtain ⟨y, hy, z, hz, hxyz⟩ := hinc L K hL hneL hconvL hK hneK hconvK (norm_sub_rev _ _) hx
    refine ⟨y, hy, ?_⟩
    rw [← hxyz, dist_eq_norm, add_sub_cancel_left]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz

/-- Support is linear under nonnegative dilation of the carrier. -/
theorem support_smul {K : Set E} (hK : IsCompact K) (hneK : K.Nonempty)
    {t : ℝ} (ht : 0 ≤ t) (u : E) : support (t • K) u = t * support K u := by
  obtain ⟨x, hx, hmax⟩ := exists_support_max hK hneK u
  apply le_antisymm
  · obtain ⟨y, hy, hymax⟩ := exists_support_max (hK.smul t) hneK.smul_set u
    obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp hy
    rw [hymax, real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (le_support hK hz u) ht
  · rw [hmax, ← real_inner_smul_right]
    exact le_support (hK.smul t) (Set.smul_mem_smul_set hx) u

/-- The norm of a support function is the actual maximum Euclidean radius
when a positive maximum is witnessed by a point of the carrier. -/
theorem norm_sphereSupport_eq_radius {K : Set E} (hK : IsCompact K) (hneK : K.Nonempty)
    {M : ℝ} (hM : 0 < M) (hbound : ∀ x ∈ K, ‖x‖ ≤ M)
    {x : E} (hx : x ∈ K) (hnorm : ‖x‖ = M) :
    ‖sphereSupport K hK‖ = M := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ hM.le).mpr
    intro u
    obtain ⟨y, hy, hmax⟩ := exists_support_max hK hneK u.val
    change |support K u.val| ≤ M
    rw [hmax]
    have hun : ‖u.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using u.property
    calc |inner ℝ u.val y| ≤ ‖u.val‖ * ‖y‖ := abs_real_inner_le_norm _ _
      _ ≤ M := by rw [hun, one_mul]; exact hbound y hy
  · let u : Directions E := ⟨M⁻¹ • x, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hM), hnorm, inv_mul_cancel₀ hM.ne']⟩
    have hpair : inner ℝ u.val x = M := by
      change inner ℝ (M⁻¹ • x) x = M
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm]
      field_simp
    calc M = inner ℝ u.val x := hpair.symm
      _ ≤ support K u.val := le_support hK hx u.val
      _ ≤ |support K u.val| := le_abs_self _
      _ ≤ ‖sphereSupport K hK‖ := (sphereSupport K hK).norm_coe_le_norm u

/-- The exact error of a positive Minkowski perturbation is `t` times the
sphere-support norm of its summand, for the Euclidean Hausdorff metric. -/
theorem hausdorffDist_add_smul_eq {K S : Set E}
    (hK : IsCompact K) (hneK : K.Nonempty) (hcK : Convex ℝ K)
    (hS : IsCompact S) (hneS : S.Nonempty) (hcS : Convex ℝ S)
    {t : ℝ} (ht : 0 ≤ t) :
    Metric.hausdorffDist (K + t • S) K = t * ‖sphereSupport S hS‖ := by
  rw [hausdorffDist_eq_norm_support_sub (hK.add (hS.smul t)) (hneK.add hneS.smul_set)
    (hcK.add (hcS.smul t)) hK hneK hcK]
  have heq : sphereSupport (K + t • S) (hK.add (hS.smul t)) - sphereSupport K hK =
      t • sphereSupport S hS := by
    ext u
    change support (K + t • S) u.val - support K u.val = t * support S u.val
    rw [support_add hK hneK (hS.smul t) hneS.smul_set, support_smul hS hneS ht]
    ring
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

end Paper17.EuclideanSupport
