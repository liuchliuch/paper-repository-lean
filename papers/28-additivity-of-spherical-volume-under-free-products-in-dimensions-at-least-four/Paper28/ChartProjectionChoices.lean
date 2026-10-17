import Paper28.RegularChartCover
import Paper28.RelativeChartCoordinates

/-! The actual projection choice in every fixed quotient chart: arbitrary
compact-lift precision, finite stabilizer invariance, nonempty coordinates,
and exact fixing of all relative pieces which can enter the chart. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G A : Type*} [Group G] [DecidableEq G] [Fintype A]

theorem exists_chart_relative_coordinates (c : RegularSphere G)
    (K : Set (RegularOrbitQuotient G)) (hK : IsCompact K)
    (P : A → Set (CoordinateHilbert G)) (hP : ∀ a, IsCompact (P a))
    (hU : ∀ a, ∀ u ∈ P a, ‖u‖ = 1) (S : A → Finset G)
    (hS : ∀ a, ∀ u ∈ P a, u ∈ coordinateSupportSubspace (S a))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : Finset G, (1 : G) ∈ F ∧
      (∀ h : regularStabilizer c.val, ∀ g, g ∈ F ↔ h.val*g ∈ F) ∧
      (∀ u : RegularSphere G, regularQuotientMap u ∈ K → dist u c ≤ (1/8 : ℝ) →
        ‖l2CoordinateProjection F u.val-u.val‖ < δ) ∧
      (∀ a, ∀ u ∈ P a, ∀ γ : G, dist c.val (leftRegular γ u) < (1/8 : ℝ) →
        l2CoordinateProjection F (leftRegular γ u) = leftRegular γ u) := by
  letI : Fintype (regularStabilizer c.val) := regularStabilizerFintype c
  let B := relativeChartCoordinates c P hP hU S
  let L := {u : RegularSphere G | u ∈ closedBall c (1/8 : ℝ) ∧ regularQuotientMap u ∈ K}
  have hL : IsCompact (Subtype.val '' L : Set (CoordinateHilbert G)) :=
    (regular_compact_chart_lift c (1/8) (by norm_num) K hK).image continuous_subtype_val
  obtain ⟨F,hBF,hInv,hApprox⟩ := exists_invariant_relative_projection (regularStabilizer c.val)
    (Subtype.val '' L) hL (insert 1 B) δ hδ
  refine ⟨F,hBF (Finset.mem_insert_self _ _),hInv,?_,?_⟩
  · intro u hu hclose
    exact hApprox u.val ⟨u,⟨hclose,hu⟩,rfl⟩
  · intro a u hu γ hclose
    apply l2CoordinateProjection_fixed F B (fun g hg => hBF (Finset.mem_insert_of_mem hg))
    exact relative_piece_mem_chart_coordinates c P hP hU S hS a u hu γ hclose

end Paper28
