import Paper17.HalfspaceNormalCone

/-!
# Finite vertex realization of generic bounded halfspace intersections

Vertices are actual solutions of square constraint systems. An extreme point
has at least `n` active constraints. When at most `n` constraints can be active,
the active square matrix is nonsingular and the point is one of finitely many
candidates. Krein-Milman then gives the actual finite convex-hull presentation.
-/
noncomputable section
open scoped BigOperators
namespace Paper17
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- At each feasible point at most `n` supporting hyperplanes are active. -/
def GeneralPositionHeights (a : ι → V n) (h : ι → ℝ) : Prop :=
  ∀ x ∈ finiteHalfspaces a h, (activeConstraints a h x).card ≤ n

/-- The actual solution of a candidate square system of supporting equations. -/
def constraintVertex (a : ι → V n) (h : ι → ℝ) (s : Finset ι) : V n :=
  if hs : s.card = n then
    (constraintMatrix a s hs)⁻¹.mulVec (fun i => h (cellEnumeration s hs i).val)
  else 0

theorem constraintVertex_solves (a : ι → V n) (h : ι → ℝ)
    (s : Finset ι) (hs : s.card = n) (hdet : (constraintMatrix a s hs).det ≠ 0) :
    ∀ i ∈ s, dot (a i) (constraintVertex a h s) = h i := by
  let M := constraintMatrix a s hs
  let e := cellEnumeration s hs
  have heq : M.mulVec (constraintVertex a h s) = fun i => h (e i).val := by
    rw [constraintVertex, dif_pos hs]
    change M.mulVec (M⁻¹.mulVec _) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  intro i hi
  obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
  have heval := congrFun heq j
  have hji : (e j).val = i := congrArg Subtype.val hj
  change dot (a (e j).val) (constraintVertex a h s) = h (e j).val at heval
  simpa only [hji] using heval

/-- The active constraints of a feasible nonsingular candidate are exactly
the prescribed constraint set under generic heights. -/
theorem activeConstraints_constraintVertex (a : ι → V n) (h : ι → ℝ)
    (hgen : GeneralPositionHeights a h) (s : Finset ι) (hs : s.card = n)
    (hdet : (constraintMatrix a s hs).det ≠ 0)
    (hfeas : constraintVertex a h s ∈ finiteHalfspaces a h) :
    activeConstraints a h (constraintVertex a h s) = s := by
  have hsub : s ⊆ activeConstraints a h (constraintVertex a h s) := by
    intro i hi
    exact (mem_activeConstraints a h _ i).mpr (constraintVertex_solves a h s hs hdet i hi)
  exact (Finset.eq_of_subset_of_card_le hsub ((hgen _ hfeas).trans_eq hs.symm)).symm

/-- Every extreme point is the unique solution of its actual active system. -/
theorem extreme_eq_constraintVertex (a : ι → V n) (h : ι → ℝ)
    {x : V n} (hx : x ∈ (finiteHalfspaces a h).extremePoints ℝ)
    (hs : (activeConstraints a h x).card = n) :
    x = constraintVertex a h (activeConstraints a h x) := by
  let s := activeConstraints a h x
  let M := constraintMatrix a s hs
  let e := cellEnumeration s hs
  have hd := extreme_constraintMatrix_det_ne_zero a h hx hs
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hd))
  apply hinj
  funext i
  change dot (a (e i).val) x = dot (a (e i).val) (constraintVertex a h s)
  rw [(mem_activeConstraints a h x (e i).val).mp (e i).property,
    constraintVertex_solves a h s hs hd (e i).val (e i).property]

/-- Valid candidate systems: full size, genuinely nonsingular, with feasible
actual solution. -/
def AdmissibleConstraintSet (a : ι → V n) (h : ι → ℝ) (s : Finset ι) : Prop :=
  ∃ hs : s.card = n, (constraintMatrix a s hs).det ≠ 0 ∧ constraintVertex a h s ∈ finiteHalfspaces a h

/-- All valid systems and their actual feasible vertices form a finite set. -/
def constraintVertices (a : ι → V n) (h : ι → ℝ) : Finset (V n) := by
  classical
  exact ((Finset.univ : Finset ι).powerset.filter (AdmissibleConstraintSet a h)).image
    (constraintVertex a h)

theorem constraintVertices_subset (a : ι → V n) (h : ι → ℝ) :
    (constraintVertices a h : Set (V n)) ⊆ finiteHalfspaces a h := by
  classical
  intro x hx
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hdet, hfeas⟩ := (Finset.mem_filter.mp hs).2
  exact hfeas

theorem extremePoints_subset_constraintVertices (a : ι → V n) (h : ι → ℝ)
    (hgen : GeneralPositionHeights a h) :
    (finiteHalfspaces a h).extremePoints ℝ ⊆ (constraintVertices a h : Set (V n)) := by
  classical
  intro x hx
  have hs : (activeConstraints a h x).card = n :=
    le_antisymm (hgen x hx.1) (extreme_active_card_ge a h hx)
  have hd := extreme_constraintMatrix_det_ne_zero a h hx hs
  have heq := extreme_eq_constraintVertex a h hx hs
  apply Finset.mem_image.mpr
  refine ⟨activeConstraints a h x, Finset.mem_filter.mpr ⟨?_, ?_⟩, heq.symm⟩
  · exact Finset.mem_powerset.mpr (Finset.subset_univ _)
  · exact ⟨hs, hd, heq ▸ hx.1⟩

/-- Actual polytopal realization of a compact finite halfspace intersection
in general position. -/
theorem finiteHalfspaces_eq_convexHull_constraintVertices (a : ι → V n) (h : ι → ℝ)
    (hgen : GeneralPositionHeights a h) (hcompact : IsCompact (finiteHalfspaces a h)) :
    finiteHalfspaces a h = convexHull ℝ (constraintVertices a h : Set (V n)) := by
  have hclosed : IsClosed (convexHull ℝ (constraintVertices a h : Set (V n))) :=
    (constraintVertices a h).finite_toSet.isCompact_convexHull.isClosed
  apply Set.Subset.antisymm
  · rw [← closure_convexHull_extremePoints hcompact (finiteHalfspaces_convex a h)]
    exact closure_minimal (convexHull_mono (extremePoints_subset_constraintVertices a h hgen)) hclosed
  · exact convexHull_min (constraintVertices_subset a h) (finiteHalfspaces_convex a h)

/-- The realization is a genuine nonempty finite-vertex polytope when the
halfspace intersection is nonempty. -/
def halfspacePolytope (a : ι → V n) (h : ι → ℝ)
    (hgen : GeneralPositionHeights a h) (hcompact : IsCompact (finiteHalfspaces a h))
    (hne : (finiteHalfspaces a h).Nonempty) : Polytope n where
  verts := constraintVertices a h
  nonempty_verts' := by
    have hh : (convexHull ℝ (constraintVertices a h : Set (V n))).Nonempty :=
      (finiteHalfspaces_eq_convexHull_constraintVertices a h hgen hcompact) ▸ hne
    exact (convexHull_nonempty_iff.mp hh)

@[simp] theorem halfspacePolytope_carrier (a : ι → V n) (h : ι → ℝ)
    (hgen : GeneralPositionHeights a h) (hcompact : IsCompact (finiteHalfspaces a h))
    (hne : (finiteHalfspaces a h).Nonempty) :
    (halfspacePolytope a h hgen hcompact hne).carrier = finiteHalfspaces a h :=
  (finiteHalfspaces_eq_convexHull_constraintVertices a h hgen hcompact).symm

end
end Paper17
