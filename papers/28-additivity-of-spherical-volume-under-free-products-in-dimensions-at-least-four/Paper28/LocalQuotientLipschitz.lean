import Paper28.EquivariantSphereDescent
import Paper28.SphericalQuotientMetricInput
import Paper28.ChordAngularComparison

/-! Native local Lipschitz descent, using arbitrarily close representatives
in the actual orbit infimum. No minimizing representative or free action is
assumed, so the argument also covers stabilizers. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G : Type*} [Group G] [DecidableEq G] [Countable G]

theorem local_angular_bound_descends (M : SphericalQuotientMetricInput G)
    (U : Set (RegularOrbitQuotient G)) (f : CoordinateHilbert G → CoordinateHilbert G)
    (hEq : ∀ γ u, f (leftRegular γ u) = leftRegular γ (f u))
    (hNorm : ∀ u : RegularSphere G, regularQuotientMap u ∈ U → ‖f u.val‖ = 1)
    (u : RegularSphere G) (hu : regularQuotientMap u ∈ U)
    (L : NNReal) (hL : 0 < (L : ℝ)) (r : ℝ) (hr : 0 < r)
    (hAngle : ∀ v w : RegularSphere G, dist v u < r → dist w u < r →
      regularQuotientMap v ∈ U → regularQuotientMap w ∈ U →
      angular (f v.val) (f w.val) ≤ (L : ℝ)*angular v.val w.val) :
    letI := M.metric
    LipschitzOnWith L (equivariantSphereDescent U f hNorm)
      (ball (⟨regularQuotientMap u,hu⟩ : U) (r/8)) := by
  letI := M.metric
  apply LipschitzOnWith.of_dist_le_mul
  intro q hq p hp
  have hqu : dist q.val (regularQuotientMap u) < r/8 := hq
  have hpu : dist p.val (regularQuotientMap u) < r/8 := hp
  have hqp : dist q.val p.val < r/4 := by
    have h := dist_triangle q.val (regularQuotientMap u) p.val
    rw [dist_comm (regularQuotientMap u) p.val] at h
    linarith
  have hqout : regularQuotientMap q.val.out = q.val := Quotient.out_eq _
  have hpout : regularQuotientMap p.val.out = p.val := Quotient.out_eq _
  obtain ⟨γ,hγ⟩ := spherical_quotient_exists_angle_lt M u q.val.out (r/8) (by positivity)
  let v : RegularSphere G := γ • q.val.out
  have hvq : regularQuotientMap v = q.val := (regularQuotientMap_smul _ _).trans hqout
  have hv : dist v u < r/4 := by
    have hc := chord_le_angular u.val v.val u.property v.property
    rw [hqout,dist_comm (regularQuotientMap u) q.val] at hγ
    change ‖v.val-u.val‖ < r/4
    rw [norm_sub_rev]
    change angular u.val v.val < _ at hγ
    linarith
  apply le_of_forall_pos_le_add
  intro e he
  let ε := min (r/8) (e/(2*(L : ℝ)))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεr : ε ≤ r/8 := min_le_left _ _
  have hεe : (L : ℝ)*ε ≤ e/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(L : ℝ))).mp (min_le_right (r/8) (e/(2*(L : ℝ))))
    dsimp [ε]
    nlinarith
  obtain ⟨δ,hδ⟩ := spherical_quotient_exists_angle_lt M v p.val.out ε hε
  let w : RegularSphere G := δ • p.val.out
  have hwp : regularQuotientMap w = p.val := (regularQuotientMap_smul _ _).trans hpout
  have hδ' : angular v.val w.val < dist q.val p.val+ε := by
    simpa only [hvq,hpout] using hδ
  have hw : dist w u < r := by
    have hc := chord_le_angular v.val w.val v.property w.property
    have ht := dist_triangle w v u
    have heq : dist w v = ‖v.val-w.val‖ := by
      change ‖w.val-v.val‖ = ‖v.val-w.val‖
      exact norm_sub_rev _ _
    rw [heq] at ht
    linarith
  have hvU : regularQuotientMap v ∈ U := hvq.symm ▸ q.property
  have hwU : regularQuotientMap w ∈ U := hwp.symm ▸ p.property
  let vf : RegularSphere G := ⟨f v.val,hNorm v hvU⟩
  let wf : RegularSphere G := ⟨f w.val,hNorm w hwU⟩
  have hOut : dist (equivariantSphereDescent U f hNorm q) (equivariantSphereDescent U f hNorm p) ≤
      (L : ℝ)*angular v.val w.val := by
    rw [equivariantSphereDescent_eval_of_eq U f hEq hNorm q v hvq,
      equivariantSphereDescent_eval_of_eq U f hEq hNorm p w hwp]
    have hd : dist (regularQuotientMap vf) (regularQuotientMap wf) ≤ angular (f v.val) (f w.val) := by
      simpa only [leftRegular_one] using spherical_quotient_dist_le_angle M vf wf 1
    exact hd.trans (hAngle v w (by linarith) hw hvU hwU)
  calc
    _ ≤ (L : ℝ)*angular v.val w.val := hOut
    _ ≤ (L : ℝ)*(dist q.val p.val+ε) := mul_le_mul_of_nonneg_left hδ'.le hL.le
    _ ≤ (L : ℝ)*dist q p+e := by
      change (L : ℝ)*(dist q.val p.val+ε) ≤ (L : ℝ)*dist q.val p.val+e
      nlinarith

end Paper28
