import Verification.QuantitativeDiskGeometry
import Verification.QuantitativeSupport

/-! A continuous interior Delzant filling with a uniform modulus estimate,
constructed by actual compatible nerve labels on the polar open cover. -/
noncomputable section
open scoped Topology
namespace P17Contract.QuantitativeDisk

variable {n : ℕ}

def coverLabel (f : Angle → EuclideanDelzantSpace n) : CoverIndex → EuclideanDelzantSpace n
  | none => f 0
  | some q => f q.1

def coverRadius (n : ℕ) : CoverIndex → ℝ
  | none => 1
  | some q => q.2.val / (8 * (n + 1 : ℝ))

theorem coverRadius_pos (i : CoverIndex) : 0 < coverRadius n i := by
  cases i with
  | none => norm_num [coverRadius]
  | some q => exact div_pos q.2.property (by positivity)

theorem coverRadius_scaled (q : Angle × Set.Ioi (0 : ℝ)) :
    (n : ℝ) * coverRadius n (some q) ≤ q.2.val / 8 := by
  have hd : (0 : ℝ) < 8 * (n + 1 : ℝ) := by positivity
  change (n : ℝ) * (q.2.val / (8 * (n + 1 : ℝ))) ≤ q.2.val / 8
  have heq : (n : ℝ) * (q.2.val / (8 * (n + 1 : ℝ))) =
      ((n : ℝ) * q.2.val) / (8 * (n + 1 : ℝ)) := by ring
  rw [heq]
  apply (div_le_div_iff₀ hd (by norm_num : (0 : ℝ) < 8)).mpr
  have hq : 0 < q.2.val := q.2.property
  nlinarith

/-- The interior map is continuous even at the center and has locally finite
normal fans everywhere. On the outer half-disk it satisfies a bound stronger
than both estimates in (A.1). -/
theorem exists_interior_filling_with_modulus (f : Angle → EuclideanDelzantSpace n)
    (hf : Continuous f) :
    ∃ F : OpenDisk → EuclideanDelzantSpace n, Continuous F ∧
      (∀ x : OpenDisk, 1 / 2 ≤ ‖x.val‖ →
        dist (F x) (f (totalAngle x.val)) ≤ depth x / 4 + Paper17.loopModulus f (depth x / 16)) ∧
      (∀ x, ∃ U ∈ 𝓝 x, ((fun y => normalFan (F y).val.body.carrier) '' U).Finite) := by
  let D : Set OpenDisk := {x | 1 / 2 ≤ ‖x.val‖}
  let R : OpenDisk → EuclideanDelzantSpace n := fun x => f (totalAngle x.val)
  let ε : OpenDisk → ℝ := fun x => depth x / 4 + Paper17.loopModulus f (depth x / 16)
  have hb : ∀ x ∈ D, ∀ i, x ∈ cover i →
      (n : ℝ) * coverRadius n i + dist (coverLabel f i) (R x) ≤ ε x := by
    intro x hx i hxi
    cases i with
    | none =>
      change ‖x.val‖ < 1 / 2 at hxi
      change 1 / 2 ≤ ‖x.val‖ at hx
      linarith
    | some q =>
      obtain ⟨p, ⟨hs, hang⟩, rfl⟩ := hxi
      have hm : dist (f q.1) (f (totalAngle p.val.val)) ≤
          Paper17.loopModulus f (depth p.val / 16) := by
        rw [totalAngle_diskAngle]
        exact Paper17.dist_le_loopModulus hf hang.le
      change (n : ℝ) * coverRadius n (some q) +
        dist (f q.1) (f (totalAngle p.val.val)) ≤
          depth p.val / 4 + Paper17.loopModulus f (depth p.val / 16)
      have hr := coverRadius_scaled (n := n) q
      linarith
  obtain ⟨F, hFc, herr, hfin⟩ := labelled_euclidean_delzant_approximation
    (coverLabel f) (coverRadius n) coverRadius_pos cover cover_isOpen cover_covers D R ε hb
  exact ⟨F, hFc, fun x hx => herr x hx, hfin⟩

/-- The last source estimate follows by monotonicity of the actual loop
modulus. -/
theorem interior_estimate_source (f : Angle → EuclideanDelzantSpace n) (hf : Continuous f)
    (F : OpenDisk → EuclideanDelzantSpace n)
    (hF : ∀ x : OpenDisk, 1 / 2 ≤ ‖x.val‖ →
      dist (F x) (f (totalAngle x.val)) ≤ depth x / 4 + Paper17.loopModulus f (depth x / 16))
    (x : OpenDisk) (hx : 1 / 2 ≤ ‖x.val‖) :
    dist (F x) (f (totalAngle x.val)) ≤ 2 * depth x + Paper17.loopModulus f (depth x / 2) := by
  have hd := depth_pos x
  have hm := Paper17.loopModulus_mono hf (by linarith : (0 : ℝ) ≤ depth x / 16)
    (by linarith : depth x / 16 ≤ depth x / 2)
  linarith [hF x hx]

end P17Contract.QuantitativeDisk
