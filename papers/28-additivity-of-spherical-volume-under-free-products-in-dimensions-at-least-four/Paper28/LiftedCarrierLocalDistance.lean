import Paper28.CoordinateCarrierLocalDistance

/-! Local finiteness excludes all nonincident coordinate spheres near a
given point. The native three-sphere estimate therefore controls arbitrary
nearby points of the actual lifted carrier with one fixed constant. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set Metric
variable {G J Z : Type*} [Group G] [DecidableEq G] [Fintype J] [PseudoMetricSpace Z]

theorem coordinate_spheres_nearby_are_incident (F : J → Finset G) (u : RegularSphere G) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/4 ∧ ∀ (v : RegularSphere G) (γ : G) (j : J),
      dist v u < r → v.val ∈ coordinateSupportSubspace ((F j).image (fun x => γ*x)) →
      u.val ∈ coordinateSupportSubspace ((F j).image (fun x => γ*x)) := by
  let spheres : G × J → Set (RegularSphere G) := fun p =>
    regularCoordinateSphere ((F p.2).image (fun x => p.1*x))
  have hLF : LocallyFinite spheres :=
    (coordinateSphere_family_locallyFinite F).subset (fun p v hv => ⟨v.property,hv⟩)
  have he := hLF.eventually_subset
    (fun p => (regularCoordinateSphere_isCompact ((F p.2).image (fun x => p.1*x))).isClosed) u
  obtain ⟨ρ,hρ,hρs⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min ρ (1/4),lt_min hρ (by norm_num),min_le_right _ _,?_⟩
  intro v γ j hv hvs
  exact hρs (lt_of_lt_of_le hv (min_le_left _ _)) (show (γ,j) ∈ {i | v ∈ spheres i} from hvs)

theorem lifted_carrier_cellwise_local_distance_bound (F : J → Finset G)
    (f : RegularSphere G → Z)
    (hCell : ∀ (γ : G) (j : J), ∀ p ∈ coordinateSphereCellIndices ((F j).image (fun x => γ*x)),
      ∀ v ∈ closedSignedBarycentricCell p.1 p.2,
      ∀ w ∈ closedSignedBarycentricCell p.1 p.2, dist (f v) (f w) ≤ angular v.val w.val)
    (u : RegularSphere G) :
    ∃ r : ℝ, 0 < r ∧ ∀ v w : RegularSphere G, dist v u < r → dist w u < r →
      (∃ γ j, v.val ∈ coordinateSupportSubspace ((F j).image (fun x => γ*x))) →
      (∃ γ j, w.val ∈ coordinateSupportSubspace ((F j).image (fun x => γ*x))) →
      dist (f v) (f w) ≤ 16*Real.pi*‖v.val-w.val‖ := by
  obtain ⟨r,hr,hr4,hInc⟩ := coordinate_spheres_nearby_are_incident F u
  refine ⟨r,hr,?_⟩
  rintro v w hv hw ⟨γ,j,hvE⟩ ⟨δ,l,hwF⟩
  exact coordinate_spheres_cellwise_distance_bound _ _ f (hCell γ j) (hCell δ l) u v w
    (hInc v γ j hv hvE) (hInc w δ l hw hwF) hvE hwF
    (le_trans (le_of_lt hv) hr4) (le_trans (le_of_lt hw) hr4)

end Paper28
