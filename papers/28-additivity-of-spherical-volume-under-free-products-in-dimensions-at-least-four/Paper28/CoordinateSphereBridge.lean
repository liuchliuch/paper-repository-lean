import Paper28.CoordinateIntersectionEstimates
import Paper28.NormalizationGlobalLipschitz
import Paper28.GlobalAngularChordBound
import Paper28.CarrierLocalFiniteness

/-! A native three-arc bridge through the common coordinate sphere near
a common unit center. Its round length is bounded by a fixed multiple of
the actual ambient chord. This supplies the carrier metric comparison. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G : Type*} [Group G] [DecidableEq G]

theorem coordinate_sphere_common_projection_bridge (E F : Finset G) (u v w : RegularSphere G)
    (huE : u.val ∈ coordinateSupportSubspace E) (huF : u.val ∈ coordinateSupportSubspace F)
    (hv : v.val ∈ coordinateSupportSubspace E) (hw : w.val ∈ coordinateSupportSubspace F)
    (hvu : ‖v.val-u.val‖ ≤ 1/4) (hwu : ‖w.val-u.val‖ ≤ 1/4) :
    ∃ p q : RegularSphere G,
      p.val = sphericalNormalize (l2CoordinateProjection (E ∩ F) v.val) ∧
      q.val = sphericalNormalize (l2CoordinateProjection (E ∩ F) w.val) ∧
      p.val ∈ coordinateSupportSubspace (E ∩ F) ∧ q.val ∈ coordinateSupportSubspace (E ∩ F) ∧
      ‖p.val-u.val‖ ≤ 1/2 ∧ ‖q.val-u.val‖ ≤ 1/2 ∧
      ‖v.val-p.val‖+‖p.val-q.val‖+‖q.val-w.val‖ ≤ 8*‖v.val-w.val‖ ∧
      angular v.val p.val+angular p.val q.val+angular q.val w.val ≤ 4*Real.pi*‖v.val-w.val‖ := by
  have huEF : u.val ∈ coordinateSupportSubspace (E ∩ F) := by
    intro g hg
    by_cases hgE : g ∈ E
    · exact huF g (fun hgF => hg (Finset.mem_inter.mpr ⟨hgE,hgF⟩))
    · exact huE g hgE
  have hPv : (1/2 : ℝ) ≤ ‖l2CoordinateProjection (E ∩ F) v.val‖ := by
    have hh := coordinate_projection_norm_lower (E ∩ F) u.val v.val huEF u.property
    linarith
  have hPw : (1/2 : ℝ) ≤ ‖l2CoordinateProjection (E ∩ F) w.val‖ := by
    have hh := coordinate_projection_norm_lower (E ∩ F) u.val w.val huEF u.property
    linarith
  have hPv0 : l2CoordinateProjection (E ∩ F) v.val ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hPv)
  have hPw0 : l2CoordinateProjection (E ∩ F) w.val ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hPw)
  have hu0 : u.val ≠ 0 := norm_pos_iff.mp (by rw [u.property]; norm_num)
  have hv0 : v.val ≠ 0 := norm_pos_iff.mp (by rw [v.property]; norm_num)
  have hw0 : w.val ≠ 0 := norm_pos_iff.mp (by rw [w.property]; norm_num)
  let p : RegularSphere G := ⟨sphericalNormalize (l2CoordinateProjection (E ∩ F) v.val),sphericalNormalize_norm _ hPv0⟩
  let q : RegularSphere G := ⟨sphericalNormalize (l2CoordinateProjection (E ∩ F) w.val),sphericalNormalize_norm _ hPw0⟩
  have hVP : ‖v.val-p.val‖ ≤ 2*‖v.val-w.val‖ := by
    have hh := sphericalNormalize_sub_le v.val (l2CoordinateProjection (E ∩ F) v.val) hv0 hPv0
    rw [sphericalNormalize_fixed v.val v.property,v.property,div_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (coordinate_intersection_projection_error E F v.val w.val hv hw) (by norm_num))
  have hWQ : ‖w.val-q.val‖ ≤ 2*‖v.val-w.val‖ := by
    have hh := sphericalNormalize_sub_le w.val (l2CoordinateProjection (E ∩ F) w.val) hw0 hPw0
    rw [sphericalNormalize_fixed w.val w.property,w.property,div_one] at hh
    have hErr : ‖w.val-l2CoordinateProjection (E ∩ F) w.val‖ ≤ ‖v.val-w.val‖ := by
      simpa only [Finset.inter_comm F E,norm_sub_rev w.val v.val] using
        coordinate_intersection_projection_error F E w.val v.val hw hv
    exact hh.trans (mul_le_mul_of_nonneg_left hErr (by norm_num))
  have hQW : ‖q.val-w.val‖ ≤ 2*‖v.val-w.val‖ := by rw [norm_sub_rev]; exact hWQ
  have hPQ : ‖p.val-q.val‖ ≤ 4*‖v.val-w.val‖ := by
    calc
      _ ≤ (2/(1/2 : ℝ))*‖l2CoordinateProjection (E ∩ F) v.val-l2CoordinateProjection (E ∩ F) w.val‖ :=
        sphericalNormalize_sub_le_of_lower_norm _ _ (1/2) (by norm_num) hPv hPw
      _ = 4*‖l2CoordinateProjection (E ∩ F) v.val-l2CoordinateProjection (E ∩ F) w.val‖ := by norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (coordinate_projection_difference_le (E ∩ F) v.val w.val) (by norm_num)
  have hPU : ‖p.val-u.val‖ ≤ 1/2 := by
    have hh := sphericalNormalize_sub_le u.val (l2CoordinateProjection (E ∩ F) v.val) hu0 hPv0
    rw [sphericalNormalize_fixed u.val u.property,u.property,div_one] at hh
    change ‖u.val-p.val‖ ≤ 2*‖u.val-l2CoordinateProjection (E ∩ F) v.val‖ at hh
    rw [norm_sub_rev u.val p.val,norm_sub_rev u.val (l2CoordinateProjection (E ∩ F) v.val)] at hh
    have hc := coordinate_projection_center_error (E ∩ F) u.val v.val huEF
    linarith
  have hQU : ‖q.val-u.val‖ ≤ 1/2 := by
    have hh := sphericalNormalize_sub_le u.val (l2CoordinateProjection (E ∩ F) w.val) hu0 hPw0
    rw [sphericalNormalize_fixed u.val u.property,u.property,div_one] at hh
    change ‖u.val-q.val‖ ≤ 2*‖u.val-l2CoordinateProjection (E ∩ F) w.val‖ at hh
    rw [norm_sub_rev u.val q.val,norm_sub_rev u.val (l2CoordinateProjection (E ∩ F) w.val)] at hh
    have hc := coordinate_projection_center_error (E ∩ F) u.val w.val huEF
    linarith
  refine ⟨p,q,rfl,rfl,(coordinateSupportSubspace (E ∩ F)).smul_mem _ (l2CoordinateProjection_mem _ _),
    (coordinateSupportSubspace (E ∩ F)).smul_mem _ (l2CoordinateProjection_mem _ _),hPU,hQU,by linarith,?_⟩
  have hA := (angular_le_pi_half_chord v.val p.val v.property p.property).trans
    (mul_le_mul_of_nonneg_left hVP (by positivity : 0 ≤ Real.pi/2))
  have hB := (angular_le_pi_half_chord p.val q.val p.property q.property).trans
    (mul_le_mul_of_nonneg_left hPQ (by positivity : 0 ≤ Real.pi/2))
  have hC := (angular_le_pi_half_chord q.val w.val q.property w.property).trans
    (mul_le_mul_of_nonneg_left hQW (by positivity : 0 ≤ Real.pi/2))
  nlinarith

end Paper28
