import Paper28.RegularStabilizers

/-! Actual finite-isotropy slice balls in the regular Hilbert sphere. The
separation from all nonstabilizing translates is derived from coefficient
decay and a finite minimum, rather than assumed as quotient-chart data. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G : Type*} [Group G] [DecidableEq G]

theorem finset_positive_lower_bound (s : Finset G) (d : G → ℝ)
    (hd : ∀ γ ∈ s, 0 < d γ) : ∃ r : ℝ, 0 < r ∧ ∀ γ ∈ s, r ≤ d γ := by
  revert hd
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨1,by norm_num,by simp⟩
  | @insert γ s hγ ih =>
    intro hd
    obtain ⟨r,hr,hbound⟩ := ih (fun δ hδ => hd δ (Finset.mem_insert_of_mem hδ))
    refine ⟨min r (d γ), lt_min hr (hd γ (Finset.mem_insert_self _ _)), ?_⟩
    intro δ hδ
    rcases Finset.mem_insert.mp hδ with rfl | hδ
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hbound δ hδ)

/-- A positive radius separates the center from every nonstabilizing
translate by at least four times the radius. -/
theorem regular_orbit_separation (u : CoordinateHilbert G) (hu : ‖u‖ = 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ γ ∉ regularStabilizer u, 4*r ≤ dist u (leftRegular γ u) := by
  classical
  let s := (regular_near_translates_finite u u hu hu).toFinset
  let b := s.filter (fun γ => γ ∉ regularStabilizer u)
  have hd : ∀ γ ∈ b, 0 < dist u (leftRegular γ u) := by
    intro γ hγ
    have hn := (Finset.mem_filter.mp hγ).2
    apply dist_pos.mpr
    intro he
    exact hn he.symm
  obtain ⟨ρ,hρ,hbound⟩ := finset_positive_lower_bound b (fun γ => dist u (leftRegular γ u)) hd
  refine ⟨min (1/4) (ρ/4), by positivity, ?_⟩
  intro γ hγ
  by_cases hs : γ ∈ s
  · have hb : γ ∈ b := Finset.mem_filter.mpr ⟨hs,hγ⟩
    have hm := min_le_right (1/4 : ℝ) (ρ/4)
    linarith [hbound γ hb]
  · have hf : ¬ dist u (leftRegular γ u) < 1 := by simpa only [s, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hs
    have hm := min_le_left (1/4 : ℝ) (ρ/4)
    linarith

/-- The small ball and its translates by elements outside the actual
finite stabilizer are disjoint, exactly as required for the quotient charts. -/
theorem regular_slice_ball (u : CoordinateHilbert G) (hu : ‖u‖ = 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ γ ∉ regularStabilizer u,
      Disjoint (ball u r) (leftRegular γ '' ball u r) := by
  obtain ⟨r,hr,hsep⟩ := regular_orbit_separation u hu
  refine ⟨r,hr,?_⟩
  intro γ hγ
  apply Set.disjoint_left.mpr
  intro x hx hxγ
  obtain ⟨y,hy,hxy⟩ := hxγ
  have hx' : dist u x < r := by simpa only [mem_ball, dist_comm] using hx
  have hy' : dist y u < r := hy
  have hi : dist x (leftRegular γ u) = dist y u := by
    rw [← hxy]
    exact (leftRegular γ).isometry.dist_eq y u
  have ht := dist_triangle u x (leftRegular γ u)
  rw [hi] at ht
  have hs := hsep γ hγ
  linarith

end Paper28
