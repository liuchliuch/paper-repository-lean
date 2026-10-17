import Paper28.CoordinateCarriers
import Paper28.FiniteTranslates
import Mathlib.Topology.LocallyFinite

/-! Native local finiteness of the lifted coordinate-sphere carrier in (12).
A nonzero coordinate persists on a small ball and restricts all relevant
translates to the explicit finite overlap set. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G J : Type*} [Group G] [DecidableEq G] [Fintype J]

abbrev RegularSphere (G : Type*) := {u : CoordinateHilbert G // ‖u‖ = 1}

theorem unit_has_nonzero_coordinate (u : RegularSphere G) : ∃ g : G, u.val g ≠ 0 := by
  by_contra h
  have hz : u.val = 0 := by
    ext g
    simpa using not_exists.mp h g
  have hu := u.property
  rw [hz,norm_zero] at hu
  norm_num at hu

theorem near_nonzero_coordinate (u v : CoordinateHilbert G) (g : G) (hu : u g ≠ 0)
    (hclose : dist u v < |u g|/2) : v g ≠ 0 := by
  intro hv
  have hc := lp.norm_apply_le_norm (p := 2) (by norm_num) (u-v) g
  change ‖u g-v g‖ ≤ ‖u-v‖ at hc
  rw [hv,sub_zero,Real.norm_eq_abs] at hc
  rw [dist_eq_norm] at hclose
  have hp : 0 < |u g| := abs_pos.mpr hu
  linarith

/-- A nearby coordinate sphere is indexed by a translation in the exact
finite overlap set determined by the persistent coordinate. -/
theorem near_coordinateSphere_translation (u v : CoordinateHilbert G) (g γ : G)
    (F : Finset G) (hu : u g ≠ 0) (hclose : dist u v < |u g|/2)
    (hv : v ∈ coordinateSphere (F.image (fun x => γ*x))) :
    γ ∈ overlapTranslations {g} F := by
  have hn := near_nonzero_coordinate u v g hu hclose
  have hg : g ∈ F.image (fun x => γ*x) := by
    by_contra h
    exact hn (hv.2 g h)
  obtain ⟨x,hx,hγx⟩ := Finset.mem_image.mp hg
  exact (mem_overlapTranslations {g} F γ).mpr ⟨g,by simp,x,hx,hγx.symm⟩

/-- The actual lifted family of all translates of finitely many coordinate
spheres is locally finite on the native regular unit sphere. -/
theorem coordinateSphere_family_locallyFinite (F : J → Finset G) :
    LocallyFinite (fun p : G×J =>
      {u : RegularSphere G | u.val ∈ coordinateSphere ((F p.2).image (fun x => p.1*x))}) := by
  classical
  intro u
  obtain ⟨g,hg⟩ := unit_has_nonzero_coordinate u
  let ρ := |u.val g|/2
  have hρ : 0 < ρ := by dsimp [ρ]; exact div_pos (abs_pos.mpr hg) (by norm_num)
  let B := Finset.univ.biUnion (fun j : J => overlapTranslations {g} (F j))
  refine ⟨ball u ρ, ball_mem_nhds u hρ, ?_⟩
  apply (B ×ˢ Finset.univ).finite_toSet.subset
  rintro ⟨γ,j⟩ ⟨v,hv,hclose⟩
  have hc : dist u.val v.val < |u.val g|/2 := by
    simpa only [mem_ball, dist_comm] using hclose
  have hb := near_coordinateSphere_translation u.val v.val g γ (F j) hg hc hv
  exact Finset.mem_product.mpr ⟨Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,hb⟩,Finset.mem_univ j⟩

end Paper28
