import K44K35Free.Pruning
import K44K35Free.ProjectivePairing
import K44K35Free.GeometrySections
import K44K35Free.Construction

/-! The concrete span calculations behind local block pruning. -/

noncomputable section
namespace K44K35Free.Geometry

open Submodule

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A linear equation holds on a finite set precisely when it holds on its
linear span. This is the passage from three cap points to their projective plane. -/
theorem linear_zero_on_point_span_iff (α : F) (c : Quartic F)
    (X : Finset (Param F)) (Q : Plane F)
    (hspan : Submodule.span F (point α c '' (↑X : Set (Param F))) = Q.val)
    (f : V F →ₗ[F] F) :
    (∀ p ∈ X, f (point α c p) = 0) ↔ ∀ v ∈ Q.val, f v = 0 := by
  constructor
  · intro h
    have hle : Submodule.span F (point α c '' (↑X : Set (Param F))) ≤ LinearMap.ker f := by
      apply Submodule.span_le.mpr
      rintro v ⟨p, hp, rfl⟩
      exact h p hp
    rw [hspan] at hle
    exact hle
  · intro h p hp
    apply h
    rw [← hspan]
    exact Submodule.subset_span ⟨p, hp, rfl⟩

/-- The right common-neighbor equation is the actual dual plane section. -/
theorem incidence_right_triple_iff (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) (X : Finset (Param F)) (Q : Plane F)
    (hspan : Submodule.span F (point α c '' (↑X : Set (Param F))) = Q.val)
    (y : Param F) :
    (∀ x ∈ X, Incidence α c T x y) ↔ y ∈ planeSection α c (rightDual T Q) := by
  classical
  rw [mem_section, rightDual_apply, mem_mapPlane, mem_polar]
  simpa only [Incidence, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
    LinearMap.flip_apply, dotForm_apply] using
    linear_zero_on_point_span_iff α c X Q hspan (dotForm.flip (T (point α c y)))

/-- The left common-neighbor equation is the actual dual plane section. -/
theorem incidence_left_triple_iff (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) (X : Finset (Param F)) (Q : Plane F)
    (hspan : Submodule.span F (point α c '' (↑X : Set (Param F))) = Q.val)
    (y : Param F) :
    (∀ x ∈ X, Incidence α c T y x) ↔ y ∈ planeSection α c (leftDual T Q) := by
  classical
  rw [mem_section, leftDual_apply, mem_polar]
  have hlinear := linear_zero_on_point_span_iff α c X Q hspan
    ((dotForm.flip (point α c y)).comp T.toLinearMap)
  constructor
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := hv
    have hQ : ∀ w ∈ Q.val, dotProduct (T w) (point α c y) = 0 := by
      apply hlinear.mp
      intro x hx
      simpa [Incidence, dotProduct_comm] using h x hx
    exact hQ w hw
  · intro h x hx
    have hQ : ∀ w ∈ Q.val, dotProduct (T w) (point α c y) = 0 := by
      intro w hw
      apply h
      exact ⟨w, hw, rfl⟩
    have hh := hlinear.mpr hQ x hx
    simpa [Incidence, dotProduct_comm] using hh

theorem right_neighbors_eq_dual_section (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) (initial : Finset (Param F × Param F))
    (hinitial : ∀ p r, (p, r) ∈ initial ↔ Incidence α c T p r)
    (X : Finset (Param F)) (Q : Plane F)
    (hspan : Submodule.span F (point α c '' (↑X : Set (Param F))) = Q.val) :
    Pruning.rightNeighbors initial X = planeSection α c (rightDual T Q) := by
  classical
  ext y
  rw [Pruning.mem_rightNeighbors, ← incidence_right_triple_iff α c T X Q hspan]
  simp only [hinitial]

theorem left_neighbors_eq_dual_section (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) (initial : Finset (Param F × Param F))
    (hinitial : ∀ p r, (p, r) ∈ initial ↔ Incidence α c T p r)
    (X : Finset (Param F)) (Q : Plane F)
    (hspan : Submodule.span F (point α c '' (↑X : Set (Param F))) = Q.val) :
    Pruning.leftNeighbors initial X = planeSection α c (leftDual T Q) := by
  classical
  ext y
  rw [Pruning.mem_leftNeighbors, ← incidence_left_triple_iff α c T X Q hspan]
  simp only [hinitial]

/-- Lemma 8 for the actual quartic cap and the actual projective pairing. -/
theorem lemma8_controlled_intersections (α : F) (c : Quartic F)
    (hα : K44K35Free.IsNonsquare α) (T : V F ≃ₗ[F] V F)
    {Q C E : Plane F} (hdesignated : Q = leftDual T C)
    (hQ : ¬ Exceptional α c Q) (hC : ¬ Exceptional α c C)
    (hE : Exceptional α c E) :
    ((planeSection α c Q) ∩ (planeSection α c (leftDual T E))).card ≤ 2 ∧
      ((planeSection α c C) ∩ (planeSection α c (rightDual T E))).card ≤ 2 := by
  classical
  exact Pruning.lemma8_of_plane_sections (planeSection α c) (Exceptional α c)
    (leftDual T) (rightDual T) (fun _ => (leftDual T).symm_apply_apply _)
    (fun _ => (leftDual T).apply_symm_apply _)
    (plane_unique_of_card_three α c hα) hdesignated hQ hC hE

end K44K35Free.Geometry

namespace K44K35Free.Construction

open Geometry Pruning Finset

variable {F : Type*} [Field F] [Fintype F]

local instance pruningGeometryLocalInstance1 : DecidableEq F := Classical.decEq F

theorem actual_requirements_card_le_two (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (T : V F ≃ₗ[F] V F)
    (D : Plane F × Plane F) (hD : D ∈ designatedPairs α c T)
    (i : BlockIndex α c) (y : Param F) :
    (requirements (copyEdges α c D) (actualBlocks α c T i) y).card ≤ 2 := by
  classical
  obtain ⟨hQ, hC, hdesignated⟩ := (mem_designatedPairs α c T D).mp hD
  rcases i with ⟨b, E⟩
  obtain ⟨hleft, hright⟩ := lemma8_controlled_intersections α c hα T
    hdesignated hQ.1 hC.1 E.property
  cases b
  · apply (requirements_product_card_le (planeSection α c D.1)
      (planeSection α c D.2) (actualBlocks α c T (false, E)) y).trans
    simpa [actualBlocks, sectionBlock, Block.controlled] using hright
  · apply (requirements_product_card_le (planeSection α c D.1)
      (planeSection α c D.2) (actualBlocks α c T (true, E)) y).trans
    simpa [actualBlocks, sectionBlock, Block.controlled] using hleft

theorem actualBlocks_controlled_card_le_four (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (T : V F ≃ₗ[F] V F)
    (i : BlockIndex α c) (hi : ¬ actualMutual α c T i) :
    (actualBlocks α c T i).controlled.card ≤ 4 := by
  classical
  exact sectionBlock_controlled_card_le_four (planeSection α c) (Exceptional α c)
    (leftDual T) (rightDual T) (nonexceptional_section_card_le_four α c hα) i hi

/-- Proposition 9, for every actual local-pruning outcome. The cap and section
theorems, rather than an assumed common-neighborhood condition, provide all
geometric inputs. -/
theorem proposition9 (α : F) (c : Quartic F) (hα : IsNonsquare α)
    (T : V F ≃ₗ[F] V F) (L : ℕ) (R : Choices α c)
    (hR : ValidChoices α c T R) : IsK35Free (finalGraph α c T L R) := by
  classical
  letI : Fintype (BlockIndex α c) := Fintype.ofFinite _
  apply proposition9_of_plane_sections (planeSection α c) (Exceptional α c)
    (leftDual T) (rightDual T) (fun _ => (leftDual T).apply_symm_apply _)
    (fun _ => (leftDual T).symm_apply_apply _)
    (nonexceptional_section_card_le_four α c hα)
    (initialEdges α c T) (preliminary α c T L)
    (PreliminaryAlteration.preliminaryEdges_subset _ _ _ _) ?_ ?_ R ?_ ?_
  · intro X hX
    obtain ⟨Q, hXQ, hspan⟩ := exists_plane_of_card_three α c hα X hX
    exact ⟨Q, hXQ, left_neighbors_eq_dual_section α c T (initialEdges α c T)
      (mem_initialEdges α c T) X Q hspan⟩
  · intro X hX
    obtain ⟨Q, hXQ, hspan⟩ := exists_plane_of_card_three α c hα X hX
    exact ⟨Q, hXQ, right_neighbors_eq_dual_section α c T (initialEdges α c T)
      (mem_initialEdges α c T) X Q hspan⟩
  · intro i hi
    apply Finset.disjoint_left.mpr
    intro e he hb
    exact PreliminaryAlteration.preliminaryEdges_no_mutual
      (initialEdges α c T) (fun i => (actualBlocks α c T i).edges)
      (actualMutual α c T) L he hi hb
  · intro i hi ha y hy
    exact (hR i hi ha y hy).2

end K44K35Free.Construction
