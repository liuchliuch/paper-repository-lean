import Verification.EuclideanMetric
import Paper17.LoopModulus
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! The actual quotient circle, polar directions and open cover for the
quantitative disk filling of Appendix A. -/
noncomputable section
open scoped Topology
namespace P17Contract.QuantitativeDisk

abbrev Angle := AddCircle (1 : ℝ)
abbrev OpenDisk := {z : ℂ // ‖z‖ < 1}
abbrev ClosedDisk := {z : ℂ // ‖z‖ ≤ 1}
abbrev PuncturedPlane := {z : ℂ // 0 < ‖z‖}

def angleCircle : Angle ≃ₜ Circle := AddCircle.homeomorphCircle (T := 1) (by norm_num)

def normalizedCircle (z : PuncturedPlane) : Circle :=
  ⟨‖z.val‖⁻¹ • z.val, by
    change ‖‖z.val‖⁻¹ • z.val - 0‖ = 1
    rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr z.property),
      inv_mul_cancel₀ z.property.ne']⟩

theorem continuous_normalizedCircle : Continuous normalizedCircle := by
  apply Continuous.subtype_mk
  exact ((continuous_norm.comp continuous_subtype_val).inv₀
    (fun z => z.property.ne')).smul continuous_subtype_val

def radialAngle (z : PuncturedPlane) : Angle := angleCircle.symm (normalizedCircle z)

theorem continuous_radialAngle : Continuous radialAngle :=
  angleCircle.symm.continuous.comp continuous_normalizedCircle

/-- A total angular coordinate; its value at the center is only a fallback
for reference values and is never used for boundary control. -/
def totalAngle (z : ℂ) : Angle := if h : 0 < ‖z‖ then radialAngle ⟨z, h⟩ else 0

theorem continuousOn_totalAngle : ContinuousOn totalAngle {z : ℂ | 0 < ‖z‖} := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun z : PuncturedPlane => totalAngle z.val)
  have heq : (fun z : PuncturedPlane => totalAngle z.val) = radialAngle := by
    funext z
    simp only [totalAngle, dif_pos z.property]
  rw [heq]
  exact continuous_radialAngle

theorem continuousAt_totalAngle {z : ℂ} (hz : 0 < ‖z‖) : ContinuousAt totalAngle z :=
  continuousOn_totalAngle.continuousAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)

def polarPoint (θ : Angle) (s : ℝ) : ℂ := (1 - s) • (angleCircle θ : ℂ)

theorem norm_polarPoint (θ : Angle) {s : ℝ} (hs : s ≤ 1) : ‖polarPoint θ s‖ = 1 - s := by
  rw [polarPoint, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs),
    Circle.norm_coe, mul_one]

theorem totalAngle_polarPoint (θ : Angle) {s : ℝ} (hs : s < 1) : totalAngle (polarPoint θ s) = θ := by
  have hr : 0 < 1 - s := sub_pos.mpr hs
  have hn := norm_polarPoint θ hs.le
  have hp : 0 < ‖polarPoint θ s‖ := hn.symm ▸ hr
  rw [totalAngle, dif_pos hp]
  have heq : normalizedCircle ⟨polarPoint θ s, hp⟩ = angleCircle θ := by
    apply Circle.ext
    change ‖polarPoint θ s‖⁻¹ • polarPoint θ s = (angleCircle θ : ℂ)
    rw [hn, polarPoint, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  change angleCircle.symm (normalizedCircle _) = θ
  rw [heq, angleCircle.symm_apply_apply]

@[simp] theorem totalAngle_circle (θ : Angle) : totalAngle (angleCircle θ : ℂ) = θ := by
  have hh := totalAngle_polarPoint θ (by norm_num : (0 : ℝ) < 1)
  simpa only [polarPoint, sub_zero, one_smul] using hh

/-- On real representatives the chart is precisely exp(2πiθ), as in the source. -/
theorem angleCircle_real (θ : ℝ) : angleCircle (θ : Angle) = Circle.exp (2 * Real.pi * θ) := by
  rw [angleCircle, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  congr 1
  ring

def depth (x : OpenDisk) : ℝ := 1 - ‖x.val‖

theorem depth_pos (x : OpenDisk) : 0 < depth x := sub_pos.mpr x.property

theorem continuous_depth : Continuous depth := continuous_const.sub continuous_subtype_val.norm

def puncture : Set OpenDisk := {x | 0 < ‖x.val‖}
abbrev PuncturedDisk := puncture

theorem isOpen_puncture : IsOpen puncture :=
  isOpen_lt continuous_const continuous_subtype_val.norm

def diskAngle (p : PuncturedDisk) : Angle := radialAngle ⟨p.val.val, p.property⟩

theorem continuous_diskAngle : Continuous diskAngle :=
  continuous_radialAngle.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

theorem totalAngle_diskAngle (p : PuncturedDisk) : totalAngle p.val.val = diskAngle p := by
  have hp : 0 < ‖p.val.val‖ := p.property
  rw [totalAngle, dif_pos hp]
  rfl

abbrev CoverIndex := Option (Angle × Set.Ioi (0 : ℝ))

/-- The center patch is disjoint from the controlled outer half-disk. The
other patches control angular distance and depth directly. -/
def cover : CoverIndex → Set OpenDisk
  | none => {x | ‖x.val‖ < 1 / 2}
  | some q => Subtype.val '' {p : PuncturedDisk |
      q.2.val < 2 * depth p.val ∧ dist q.1 (diskAngle p) < depth p.val / 16}

theorem cover_isOpen (i : CoverIndex) : IsOpen (cover i) := by
  cases i with
  | none => exact isOpen_lt continuous_subtype_val.norm continuous_const
  | some q =>
    have hd : Continuous (fun p : PuncturedDisk => depth p.val) :=
      continuous_depth.comp continuous_subtype_val
    have ho : IsOpen {p : PuncturedDisk |
        q.2.val < 2 * depth p.val ∧ dist q.1 (diskAngle p) < depth p.val / 16} :=
      (isOpen_lt continuous_const (continuous_const.mul hd)).inter
        (isOpen_lt (continuous_const.dist continuous_diskAngle) (hd.div_const 16))
    exact isOpen_puncture.isOpenEmbedding_subtypeVal.isOpenMap _ ho

theorem cover_covers : (Set.univ : Set OpenDisk) ⊆ ⋃ i, cover i := by
  intro x hx
  by_cases hp : 0 < ‖x.val‖
  · let p : PuncturedDisk := ⟨x, hp⟩
    let i : CoverIndex := some (diskAngle p, ⟨depth x, depth_pos x⟩)
    apply Set.mem_iUnion.mpr
    refine ⟨i, p, ?_, rfl⟩
    change depth x < 2 * depth x ∧ dist (diskAngle p) (diskAngle p) < depth x / 16
    rw [dist_self]
    exact ⟨by linarith [depth_pos x], div_pos (depth_pos x) (by norm_num)⟩
  · apply Set.mem_iUnion.mpr
    refine ⟨none, ?_⟩
    change ‖x.val‖ < 1 / 2
    linarith [norm_nonneg x.val]

/-- The actual boundary point exp(2πiθ) in the closed unit disk. -/
def boundaryPoint (θ : Angle) : ClosedDisk := ⟨angleCircle θ, (Circle.norm_coe _).le⟩

/-- The actual polar point (1-s)exp(2πiθ) in the closed unit disk. -/
def polarClosed (θ : Angle) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : ClosedDisk :=
  ⟨polarPoint θ s, by rw [norm_polarPoint θ hs1]; linarith⟩

def dyadicDepth (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k
def dyadicCount (k : ℕ) : ℕ := 2 ^ (k + 2)

theorem dyadicDepth_pos (k : ℕ) : 0 < dyadicDepth k := pow_pos (by norm_num) k

theorem dyadicDepth_succ (k : ℕ) : dyadicDepth (k + 1) = dyadicDepth k / 2 := by
  simp only [dyadicDepth, pow_succ]
  ring

theorem dyadicDepth_le_one (k : ℕ) : dyadicDepth k ≤ 1 := by
  induction k with
  | zero => norm_num [dyadicDepth]
  | succ k ih => rw [dyadicDepth_succ]; linarith

theorem dyadicDepth_le_half {k : ℕ} (hk : 1 ≤ k) : dyadicDepth k ≤ 1 / 2 := by
  cases k with
  | zero => omega
  | succ k => rw [dyadicDepth_succ]; linarith [dyadicDepth_le_one k]

theorem reciprocal_dyadicCount (k : ℕ) : 1 / (dyadicCount k : ℝ) = dyadicDepth k / 4 := by
  have hp : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  simp only [dyadicCount, Nat.cast_pow, Nat.cast_ofNat, dyadicDepth, div_pow, one_pow, pow_add]
  norm_num
  field_simp
  <;> ring

/-- The point in a source dyadic annulus, with its actual polar coordinate. -/
def annulusPoint (θ : Angle) (k : ℕ) (s : ℝ) (hk : 1 ≤ k)
    (hlo : dyadicDepth (k + 1) ≤ s) (hhi : s ≤ dyadicDepth k) : ClosedDisk :=
  polarClosed θ s ((dyadicDepth_pos (k + 1)).le.trans hlo)
    (hhi.trans (dyadicDepth_le_one k))

end P17Contract.QuantitativeDisk
