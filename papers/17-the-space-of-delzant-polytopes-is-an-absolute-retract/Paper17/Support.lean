import Paper17.SupportBounds
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Support-function coordinates

`V n` has the Pi supremum norm. Its dual unit ball is the L1 unit ball.
The isometry below uses this dual ball, so no Euclidean-norm assumption is
silently made about the Pi metric. These are actual continuous functions in
an actual normed space; no additive-group instance is put on sets.
-/
noncomputable section
open scoped Topology BigOperators Pointwise
namespace Paper17

/-- Closed unit ball of the dual norm to the Pi supremum norm. -/
def dualUnitBall (n : ℕ) : Set (V n) := {u | ∑ i, |u i| ≤ 1}

instance dualUnitBall_compact (n : ℕ) : CompactSpace (dualUnitBall n) := by
  apply isCompact_iff_compactSpace.mp
  have hc : IsClosed (dualUnitBall n) := isClosed_le
    (continuous_finset_sum _ fun i _ => (continuous_apply i).abs) continuous_const
  apply (isCompact_closedBall (0 : V n) 1).of_isClosed_subset hc
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  calc ‖u i‖ = |u i| := Real.norm_eq_abs _
    _ ≤ ∑ j, |u j| := Finset.single_le_sum (fun j _ => abs_nonneg (u j)) (Finset.mem_univ i)
    _ ≤ 1 := hu

/-- Ambient real normed space for support functions. -/
abbrev SupportSpace (n : ℕ) := C(dualUnitBall n, ℝ)

theorem continuous_supportFunction {n : ℕ} {K : Set (V n)} (hK : IsCompact K) :
    Continuous (supportFunction K) := by
  change Continuous fun u => sSup ((fun x => dot u x) '' K)
  apply hK.continuous_sSup (f := fun u x : V n => dot u x)
  change Continuous fun p : V n × V n => ∑ i, p.1 i * p.2 i
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)

/-- A body's support function as a point in the normed ambient space. -/
def supportMap {n : ℕ} (K : PosBody n) : SupportSpace n :=
  ⟨fun u => supportFunction K.carrier u,
    (continuous_supportFunction K.isCompact).comp continuous_subtype_val⟩

theorem supportFunction_direction_smul {n : ℕ} {K : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) (u : V n) {t : ℝ} (ht : 0 ≤ t) :
    supportFunction K (t • u) = t * supportFunction K u := by
  obtain ⟨x, hx, hmax⟩ := exists_mem_eq_supportFunction hK hneK u
  apply le_antisymm
  · obtain ⟨y, hy, hymax⟩ := exists_mem_eq_supportFunction hK hneK (t • u)
    rw [hymax, dot_smul_left]
    exact mul_le_mul_of_nonneg_left (supportFunction_ub hK hy) ht
  · rw [hmax, ← dot_smul_left]
    exact supportFunction_ub hK hx

theorem supportFunction_closedBall_zero {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (u : V n) :
    supportFunction (Metric.closedBall (0 : V n) r) u = r * ∑ i, |u i| := by
  let x : V n := fun i => if 0 ≤ u i then r else -r
  have hx : x ∈ Metric.closedBall (0 : V n) r := by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr]
    intro i
    dsimp [x]
    split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg hr]
  have hdot : dot u x = r * ∑ i, |u i| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [x]
    split_ifs with hi
    · rw [abs_of_nonneg hi, mul_comm]
    · rw [abs_of_neg (lt_of_not_ge hi)]
      ring
  apply le_antisymm
  · obtain ⟨y, hy, hmax⟩ := exists_mem_eq_supportFunction (isCompact_closedBall _ _)
      ⟨0, Metric.mem_closedBall_self hr⟩ u
    rw [hmax]
    calc dot u y ≤ |dot u y| := le_abs_self _
      _ ≤ (∑ i, |u i|) * ‖y‖ := abs_dot_le_sum_abs_mul_norm u y
      _ ≤ (∑ i, |u i|) * r := mul_le_mul_of_nonneg_left
        (by simpa [Metric.mem_closedBall] using hy) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      _ = r * ∑ i, |u i| := mul_comm _ _
  · rw [← hdot]
    exact supportFunction_ub (isCompact_closedBall _ _) hx

theorem norm_supportMap_sub_le {n : ℕ} (K L : PosBody n) :
    ‖supportMap K - supportMap L‖ ≤ Metric.hausdorffDist K.carrier L.carrier := by
  apply (ContinuousMap.norm_le _ Metric.hausdorffDist_nonneg).mpr
  intro u
  change |supportFunction K.carrier u - supportFunction L.carrier u| ≤ _
  apply (abs_le.mpr ⟨?_, ?_⟩).trans
    (mul_le_of_le_one_right Metric.hausdorffDist_nonneg u.property)
  · have h := supportFunction_sub_le_of_hausdorffDist' K.isCompact K.nonempty L.isCompact L.nonempty u
    change supportFunction L.carrier u - supportFunction K.carrier u ≤
      Metric.hausdorffDist K.carrier L.carrier * ∑ i, |u.val i| at h
    linarith
  · exact supportFunction_sub_le_of_hausdorffDist K.isCompact K.nonempty L.isCompact L.nonempty u

/-- Control on the dual unit ball controls every direction by homogeneity. -/
theorem supportFunction_sub_le_norm_mul {n : ℕ} (K L : PosBody n) (u : V n) :
    supportFunction K.carrier u - supportFunction L.carrier u ≤
      ‖supportMap K - supportMap L‖ * ∑ i, |u i| := by
  let S : ℝ := ∑ i, |u i|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases hz : S = 0
  · have hu : u = 0 := by
      ext i
      have hi : |u i| ≤ S := Finset.single_le_sum (fun j _ => abs_nonneg (u j)) (Finset.mem_univ i)
      simpa only [hz, abs_nonpos_iff, Pi.zero_apply] using hi
    have hk : supportFunction K.carrier 0 = 0 := by
      obtain ⟨x, hx, hm⟩ := exists_mem_eq_supportFunction K.isCompact K.nonempty 0
      simpa [dot] using hm
    have hl : supportFunction L.carrier 0 = 0 := by
      obtain ⟨x, hx, hm⟩ := exists_mem_eq_supportFunction L.isCompact L.nonempty 0
      simpa [dot] using hm
    simp [hu, hk, hl]
  · have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
    let v : dualUnitBall n := ⟨S⁻¹ • u, by
      change ∑ i, |S⁻¹ * u i| ≤ 1
      simp_rw [abs_mul, abs_of_pos (inv_pos.mpr hSp)]
      rw [← Finset.mul_sum]
      change S⁻¹ * S ≤ 1
      rw [inv_mul_cancel₀ hz]⟩
    have hv := (supportMap K - supportMap L).norm_coe_le_norm v
    change |supportFunction K.carrier (S⁻¹ • u) - supportFunction L.carrier (S⁻¹ • u)| ≤ _ at hv
    rw [supportFunction_direction_smul (K := K.carrier) K.isCompact K.nonempty u (inv_nonneg.mpr hS),
      supportFunction_direction_smul (K := L.carrier) L.isCompact L.nonempty u (inv_nonneg.mpr hS)] at hv
    have hv' := (le_abs_self _).trans hv
    have hmul := mul_le_mul_of_nonneg_left hv' hS
    calc supportFunction K.carrier u - supportFunction L.carrier u
        = S * (S⁻¹ * supportFunction K.carrier u - S⁻¹ * supportFunction L.carrier u) := by
          rw [← mul_sub, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
      _ ≤ S * ‖supportMap K - supportMap L‖ := hmul
      _ = ‖supportMap K - supportMap L‖ * S := mul_comm _ _

/-- The support-function embedding is isometric for the Hausdorff metric. -/
theorem dist_supportMap {n : ℕ} (K L : PosBody n) :
    dist (supportMap K) (supportMap L) = Metric.hausdorffDist K.carrier L.carrier := by
  rw [dist_eq_norm]
  apply le_antisymm (norm_supportMap_sub_le K L)
  let r := ‖supportMap K - supportMap L‖
  have hr : 0 ≤ r := norm_nonneg _
  have hinc : ∀ A B : PosBody n,
      ‖supportMap A - supportMap B‖ = r → A.carrier ⊆ B.carrier + Metric.closedBall 0 r := by
    intro A B hnorm
    apply subset_of_forall_dot_le_supportFunction
      (B.isCompact.add (isCompact_closedBall _ _))
      (B.nonempty.add ⟨0, Metric.mem_closedBall_self hr⟩)
      (B.convex.add (convex_closedBall _ _))
    intro u x hx
    rw [supportFunction_add B.isCompact B.nonempty (isCompact_closedBall _ _)
      ⟨0, Metric.mem_closedBall_self hr⟩, supportFunction_closedBall_zero hr]
    change dot u x ≤ supportFunction B.carrier u + r * ∑ i, |u i|
    have h := supportFunction_sub_le_norm_mul A B u
    rw [hnorm] at h
    have hb : dot u x ≤ supportFunction A.carrier u :=
      supportFunction_ub (K := A.carrier) (u := u) A.isCompact hx
    linarith
  apply Metric.hausdorffDist_le_of_mem_dist hr
  · intro x hx
    obtain ⟨y, hy, z, hz, hxyz⟩ := hinc K L rfl hx
    refine ⟨y, hy, ?_⟩
    rw [← hxyz, dist_eq_norm, add_sub_cancel_left]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  · intro x hx
    obtain ⟨y, hy, z, hz, hxyz⟩ := hinc L K (norm_sub_rev _ _) hx
    refine ⟨y, hy, ?_⟩
    rw [← hxyz, dist_eq_norm, add_sub_cancel_left]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz

/-- Support functions distinguish positive convex bodies. -/
theorem supportMap_injective {n : ℕ} : Function.Injective (@supportMap n) := by
  intro K L h
  apply PosBody.ext
  have hfin := Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded
    K.nonempty L.nonempty K.isCompact.isBounded L.isCompact.isBounded
  apply (K.isClosed.hausdorffDist_zero_iff_eq L.isClosed hfin).mp
  change Metric.hausdorffDist K.carrier L.carrier = 0
  rw [← dist_supportMap, h, dist_self]

instance PosBody.instMetricSpace (n : ℕ) : MetricSpace (PosBody n) :=
  MetricSpace.induced supportMap supportMap_injective inferInstance

@[simp] theorem PosBody.dist_eq_hausdorffDist {n : ℕ} (K L : PosBody n) :
    dist K L = Metric.hausdorffDist K.carrier L.carrier := dist_supportMap K L

theorem isometry_supportMap {n : ℕ} : Isometry (@supportMap n) :=
  isometry_iff_dist_eq.mpr fun _ _ => rfl

end Paper17
