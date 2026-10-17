import Paper28.CoordinateCarriers

/-! Actual orthogonal coordinate intersection estimates for the carrier
metric comparison. Projection to E∩F moves a point of S(E) by at most its
distance to a point of S(F), and stays nonzero near a common unit center. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G : Type*} [Group G] [DecidableEq G]

theorem l2CoordinateProjection_fixed_of_supported (F : Finset G) (u : CoordinateHilbert G)
    (hu : u ∈ coordinateSupportSubspace F) : l2CoordinateProjection F u = u := by
  ext g
  rw [l2CoordinateProjection_apply]
  by_cases hg : g ∈ F
  · rw [if_pos hg]
  · rw [if_neg hg,hu g hg]

theorem l2CoordinateProjection_complement_norm_le (F : Finset G) (u : CoordinateHilbert G) :
    ‖u-l2CoordinateProjection F u‖ ≤ ‖u‖ := by
  have hh := lp.norm_sub_norm_compl_sub_single (p := 2) (by norm_num) u F
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hh
  have hs : 0 ≤ ∑ g ∈ F, ‖u g‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change ‖u‖^2-‖u-l2CoordinateProjection F u‖^2 = _ at hh
  nlinarith [norm_nonneg u,norm_nonneg (u-l2CoordinateProjection F u)]

theorem l2CoordinateProjection_inter_of_supported (E F : Finset G) (u : CoordinateHilbert G)
    (hu : u ∈ coordinateSupportSubspace E) :
    l2CoordinateProjection (E ∩ F) u = l2CoordinateProjection F u := by
  ext g
  simp only [l2CoordinateProjection_apply,Finset.mem_inter]
  by_cases hg : g ∈ E
  · simp only [hg,true_and]
  · have hz := hu g hg
    simp only [hg,false_and,if_false,hz,ite_self]

theorem coordinate_intersection_projection_error (E F : Finset G) (v w : CoordinateHilbert G)
    (hv : v ∈ coordinateSupportSubspace E) (hw : w ∈ coordinateSupportSubspace F) :
    ‖v-l2CoordinateProjection (E ∩ F) v‖ ≤ ‖v-w‖ := by
  rw [l2CoordinateProjection_inter_of_supported E F v hv]
  have he : v-l2CoordinateProjection F v = (v-w)-l2CoordinateProjection F (v-w) := by
    rw [map_sub,l2CoordinateProjection_fixed_of_supported F w hw]
    module
  rw [he]
  exact l2CoordinateProjection_complement_norm_le F (v-w)

theorem coordinate_projection_center_error (F : Finset G) (u v : CoordinateHilbert G)
    (hu : u ∈ coordinateSupportSubspace F) :
    ‖l2CoordinateProjection F v-u‖ ≤ ‖v-u‖ := by
  have he : l2CoordinateProjection F v-u = l2CoordinateProjection F (v-u) := by
    rw [map_sub,l2CoordinateProjection_fixed_of_supported F u hu]
  rw [he]
  exact l2CoordinateProjection_norm_le F (v-u)

theorem coordinate_projection_norm_lower (F : Finset G) (u v : CoordinateHilbert G)
    (hu : u ∈ coordinateSupportSubspace F) (hUnit : ‖u‖ = 1) :
    1-‖v-u‖ ≤ ‖l2CoordinateProjection F v‖ := by
  have hc := coordinate_projection_center_error F u v hu
  have hn := norm_sub_norm_le u (l2CoordinateProjection F v)
  rw [hUnit,norm_sub_rev] at hn
  linarith

theorem coordinate_projection_difference_le (F : Finset G) (v w : CoordinateHilbert G) :
    ‖l2CoordinateProjection F v-l2CoordinateProjection F w‖ ≤ ‖v-w‖ := by
  rw [← map_sub]
  exact l2CoordinateProjection_norm_le F (v-w)

end Paper28
