import Paper28.QuotientCloseLifts

/-! Joint Lipschitz descent with a time parameter to the actual spherical
orbit quotient. The domain uses its native product metric. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G T : Type*} [Group G] [DecidableEq G] [Countable G] [MetricSpace T]

theorem local_homotopy_angular_bound_descends (M : SphericalQuotientMetricInput G)
    (U : Set (RegularOrbitQuotient G)) (f : T → CoordinateHilbert G → CoordinateHilbert G)
    (hEq : ∀ t γ u, f t (leftRegular γ u) = leftRegular γ (f t u))
    (hNorm : ∀ t, ∀ u : RegularSphere G, regularQuotientMap u ∈ U → ‖f t u.val‖ = 1)
    (t : T) (u : RegularSphere G) (hu : regularQuotientMap u ∈ U)
    (B : NNReal) (hB : 0 < (B : ℝ)) (r : ℝ) (hr : 0 < r)
    (hAngle : ∀ s z : T, ∀ v w : RegularSphere G,
      dist s t < r → dist z t < r → dist v u < r → dist w u < r →
      regularQuotientMap v ∈ U → regularQuotientMap w ∈ U →
      angular (f s v.val) (f z w.val) ≤ (B : ℝ)*(dist s z+angular v.val w.val)) :
    letI := M.metric
    LipschitzOnWith (2*B)
      (fun p : T×U => equivariantSphereDescent U (f p.1) (hNorm p.1) p.2)
      (ball (t,(⟨regularQuotientMap u,hu⟩ : U)) (r/8)) := by
  letI := M.metric
  apply LipschitzOnWith.of_dist_le_mul
  intro q hq p hp
  have hq' : max (dist q.1 t) (dist q.2.val (regularQuotientMap u)) < r/8 := hq
  have hp' : max (dist p.1 t) (dist p.2.val (regularQuotientMap u)) < r/8 := hp
  have hqt : dist q.1 t < r := by linarith [(max_lt_iff.mp hq').1]
  have hpt : dist p.1 t < r := by linarith [(max_lt_iff.mp hp').1]
  have hqu : dist q.2.val (regularQuotientMap u) < r/8 := (max_lt_iff.mp hq').2
  have hpu : dist p.2.val (regularQuotientMap u) < r/8 := (max_lt_iff.mp hp').2
  apply le_of_forall_pos_le_add
  intro e he
  let ε := min (r/8) (e/(2*(B : ℝ)))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεr : ε ≤ r/8 := min_le_left _ _
  have hεe : (B : ℝ)*ε ≤ e/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(B : ℝ))).mp (min_le_right (r/8) (e/(2*(B : ℝ))))
    dsimp [ε]
    nlinarith
  obtain ⟨v,w,hvq,hwp,hv,hw,hvw⟩ :=
    spherical_quotient_exists_close_lifts M u q.2.val p.2.val r hr ε hε hεr hqu hpu
  have hvU : regularQuotientMap v ∈ U := hvq.symm ▸ q.2.property
  have hwU : regularQuotientMap w ∈ U := hwp.symm ▸ p.2.property
  let vf : RegularSphere G := ⟨f q.1 v.val,hNorm q.1 v hvU⟩
  let wf : RegularSphere G := ⟨f p.1 w.val,hNorm p.1 w hwU⟩
  have hOut : dist (equivariantSphereDescent U (f q.1) (hNorm q.1) q.2)
      (equivariantSphereDescent U (f p.1) (hNorm p.1) p.2) ≤
      (B : ℝ)*(dist q.1 p.1+angular v.val w.val) := by
    rw [equivariantSphereDescent_eval_of_eq U (f q.1) (hEq q.1) (hNorm q.1) q.2 v hvq,
      equivariantSphereDescent_eval_of_eq U (f p.1) (hEq p.1) (hNorm p.1) p.2 w hwp]
    have hd : dist (regularQuotientMap vf) (regularQuotientMap wf) ≤
        angular (f q.1 v.val) (f p.1 w.val) := by
      simpa only [leftRegular_one] using spherical_quotient_dist_le_angle M vf wf 1
    exact hd.trans (hAngle q.1 p.1 v w hqt hpt hv hw hvU hwU)
  have htime : dist q.1 p.1 ≤ dist q p := le_max_left _ _
  have hspace : dist q.2.val p.2.val ≤ dist q p := le_max_right _ _
  calc
    _ ≤ (B : ℝ)*(dist q.1 p.1+angular v.val w.val) := hOut
    _ ≤ (B : ℝ)*(dist q.1 p.1+dist q.2.val p.2.val+ε) :=
      mul_le_mul_of_nonneg_left (by linarith) hB.le
    _ ≤ ((2*B : NNReal) : ℝ)*dist q p+e := by
      simp only [NNReal.coe_mul,NNReal.coe_ofNat]
      nlinarith

end Paper28
