import Paper28.GlobalAngularChordBound
import Paper28.SphericalQuotientMetricInput
import Paper28.RegularSlices

/-! The actual quotient metric is exactly round along a set fixed by the
center's stabilizer, locally at that center. Nonstabilizing translates are
excluded by the natively proved orbit separation and chord-angle bounds. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G : Type*} [Group G] [DecidableEq G] [Countable G]

theorem spherical_quotient_locally_round_on_stabilizer_fixed_set
    (M : SphericalQuotientMetricInput G) (S : Set (RegularSphere G)) (u : RegularSphere G)
    (hFix : ∀ γ ∈ regularStabilizer u.val, ∀ w ∈ S, leftRegular γ w.val = w.val) :
    ∃ r : ℝ, 0 < r ∧ ∀ v ∈ S, ∀ w ∈ S, dist v u < r → dist w u < r →
      @dist (RegularOrbitQuotient G) M.metric.toDist (regularQuotientMap v) (regularQuotientMap w) =
        angular v.val w.val := by
  obtain ⟨ρ,hρ,hSep⟩ := regular_orbit_separation u.val u.property
  let r : ℝ := min (ρ/4) (ρ/(4*Real.pi))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrρ : r ≤ ρ/4 := min_le_left _ _
  have hrπ : Real.pi*r ≤ ρ/4 := by
    have hh : r*(4*Real.pi) ≤ ρ := (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mp (min_le_right _ _)
    nlinarith
  refine ⟨r,hr,?_⟩
  intro v hv w hw hvu hwu
  have hvu' : dist v.val u.val < r := hvu
  have hwu' : dist w.val u.val < r := hwu
  have huv' : dist u.val v.val < r := by simpa only [dist_comm] using hvu'
  have hChord : ‖v.val-w.val‖ ≤ 2*r := by
    have ht : dist v.val w.val ≤ 2*r := by
      have hh := dist_triangle v.val u.val w.val
      rw [dist_comm u.val w.val] at hh
      linarith
    simpa only [dist_eq_norm] using ht
  have hAng : angular v.val w.val ≤ ρ/4 := by
    calc
      _ ≤ (Real.pi/2)*‖v.val-w.val‖ := angular_le_pi_half_chord _ _ v.property w.property
      _ ≤ (Real.pi/2)*(2*r) := mul_le_mul_of_nonneg_left hChord (by positivity)
      _ = Real.pi*r := by ring
      _ ≤ ρ/4 := hrπ
  have hLower : ∀ γ : G, angular v.val w.val ≤ angular v.val (leftRegular γ w.val) := by
    intro γ
    by_cases hγ : γ ∈ regularStabilizer u.val
    · rw [hFix γ hγ w hw]
    · have hSepγ := hSep γ hγ
      have hTri1 := dist_triangle u.val v.val (leftRegular γ u.val)
      have hTri2 := dist_triangle v.val (leftRegular γ w.val) (leftRegular γ u.val)
      have hIso : dist (leftRegular γ w.val) (leftRegular γ u.val) = dist w.val u.val :=
        (leftRegular γ).isometry.dist_eq _ _
      rw [hIso] at hTri2
      have hUnit : ‖leftRegular γ w.val‖ = 1 := (leftRegular γ).norm_map w.val |>.trans w.property
      have hCross : dist v.val (leftRegular γ w.val) ≤ angular v.val (leftRegular γ w.val) := by
        simpa only [dist_eq_norm] using chord_le_angular v.val (leftRegular γ w.val) v.property hUnit
      nlinarith
  apply le_antisymm
  · simpa only [leftRegular_one] using spherical_quotient_dist_le_angle M v w 1
  · rw [spherical_quotient_distance M]
    apply le_csInf (Set.range_nonempty _)
    rintro a ⟨γ,rfl⟩
    exact hLower γ

end Paper28
