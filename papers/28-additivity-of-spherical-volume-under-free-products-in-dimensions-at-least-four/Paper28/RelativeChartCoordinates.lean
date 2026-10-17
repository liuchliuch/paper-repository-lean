import Paper28.CoordinateCarriers
import Paper28.CarrierLocalFiniteness
import Paper28.RegularCompactTranslates

/-! The finite relative coordinate enlargement in one quotient chart.
All translates of every prescribed compact finite-support piece which can
meet the chart are enumerated by proved finite sets; their coordinates are
then included explicitly. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G A : Type*} [Group G] [DecidableEq G] [Fintype A]

theorem leftRegular_mem_coordinateSupport (γ : G) (F : Finset G) (u : CoordinateHilbert G)
    (hu : u ∈ coordinateSupportSubspace F) :
    leftRegular γ u ∈ coordinateSupportSubspace (F.image (fun g => γ*g)) := by
  intro g hg
  change u (γ⁻¹*g) = 0
  apply hu
  intro h
  exact hg (Finset.mem_image.mpr ⟨γ⁻¹*g,h,by simp [mul_assoc]⟩)

def relativeChartCoordinates (c : RegularSphere G) (P : A → Set (CoordinateHilbert G))
    (hP : ∀ a, IsCompact (P a)) (hU : ∀ a, ∀ u ∈ P a, ‖u‖ = 1)
    (F : A → Finset G) : Finset G :=
  Finset.univ.biUnion (fun a =>
    (regular_compact_near_translates_finite c.val c.property (P a) (hP a) (hU a)).toFinset.biUnion
      (fun γ => (F a).image (fun g => γ*g)))

/-- Every translated relative piece meeting the fixed small chart is
supported in the single explicitly constructed finite coordinate set. -/
theorem relative_piece_mem_chart_coordinates (c : RegularSphere G)
    (P : A → Set (CoordinateHilbert G)) (hP : ∀ a, IsCompact (P a))
    (hU : ∀ a, ∀ u ∈ P a, ‖u‖ = 1) (F : A → Finset G)
    (hF : ∀ a, ∀ u ∈ P a, u ∈ coordinateSupportSubspace (F a))
    (a : A) (u : CoordinateHilbert G) (hu : u ∈ P a) (γ : G)
    (hclose : dist c.val (leftRegular γ u) < (1/8 : ℝ)) :
    leftRegular γ u ∈ coordinateSupportSubspace (relativeChartCoordinates c P hP hU F) := by
  have hγ : γ ∈ (regular_compact_near_translates_finite c.val c.property (P a) (hP a) (hU a)).toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨u,hu,by linarith⟩
  have hsubset : (F a).image (fun g => γ*g) ⊆ relativeChartCoordinates c P hP hU F := by
    intro g hg
    exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ a,Finset.mem_biUnion.mpr ⟨γ,hγ,hg⟩⟩
  exact coordinateSupportSubspace_mono _ _ hsubset (leftRegular_mem_coordinateSupport γ (F a) u (hF a u hu))

end Paper28
