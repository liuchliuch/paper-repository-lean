import Paper28.LocalQuotientLipschitz

/-! Simultaneously choosing nearby actual lifts and representatives which
approach the quotient distance, with no attainment assumption. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G : Type*} [Group G] [DecidableEq G] [Countable G]

theorem spherical_quotient_exists_close_lifts (M : SphericalQuotientMetricInput G)
    (u : RegularSphere G) (q p : RegularOrbitQuotient G) (r : ℝ) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ r/8) :
    letI := M.metric
    dist q (regularQuotientMap u) < r/8 → dist p (regularQuotientMap u) < r/8 →
      ∃ v w : RegularSphere G, regularQuotientMap v = q ∧ regularQuotientMap w = p ∧
        dist v u < r ∧ dist w u < r ∧ angular v.val w.val < dist q p+ε := by
  letI := M.metric
  intro hqu hpu
  have hqp : dist q p < r/4 := by
    have h := dist_triangle q (regularQuotientMap u) p
    rw [dist_comm (regularQuotientMap u) p] at h
    linarith
  have hqout : regularQuotientMap q.out = q := Quotient.out_eq _
  have hpout : regularQuotientMap p.out = p := Quotient.out_eq _
  obtain ⟨γ,hγ⟩ := spherical_quotient_exists_angle_lt M u q.out (r/8) (by positivity)
  let v : RegularSphere G := γ • q.out
  have hvq : regularQuotientMap v = q := (regularQuotientMap_smul _ _).trans hqout
  have hv : dist v u < r/4 := by
    have hc := chord_le_angular u.val v.val u.property v.property
    rw [hqout,dist_comm (regularQuotientMap u) q] at hγ
    change ‖v.val-u.val‖ < r/4
    rw [norm_sub_rev]
    change angular u.val v.val < _ at hγ
    linarith
  obtain ⟨δ,hδ⟩ := spherical_quotient_exists_angle_lt M v p.out ε hε
  let w : RegularSphere G := δ • p.out
  have hwp : regularQuotientMap w = p := (regularQuotientMap_smul _ _).trans hpout
  have hδ' : angular v.val w.val < dist q p+ε := by simpa only [hvq,hpout] using hδ
  have hw : dist w u < r := by
    have hc := chord_le_angular v.val w.val v.property w.property
    have ht := dist_triangle w v u
    have heq : dist w v = ‖v.val-w.val‖ := by
      change ‖w.val-v.val‖ = ‖v.val-w.val‖
      exact norm_sub_rev _ _
    rw [heq] at ht
    linarith
  exact ⟨v,w,hvq,hwp,by linarith,hw,hδ'⟩

end Paper28
