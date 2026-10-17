import Paper17.GeneralHalfspaceVertices
import Paper17.Approximation

/-! Rational solutions and finite rational vertex presentations of compact
rational halfspace intersections, without genericity assumptions. -/
noncomputable section
open scoped BigOperators
namespace Paper17

/-- Real realization of a rational vector. -/
def ratVector {n : ℕ} (q : Fin n → ℚ) : V n := fun j => (q j : ℝ)

@[simp] theorem ratVector_isRatPoint {n : ℕ} (q : Fin n → ℚ) : IsRatPoint (ratVector q) :=
  fun j => ⟨q j, rfl⟩

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- A nonsingular real supporting system with rational entries has a rational
solution, obtained by solving the actual square system over `ℚ`. -/
theorem constraintVertex_isRatPoint (a : ι → Fin n → ℚ) (h : ι → ℚ)
    (s : Finset ι) (hs : s.card = n)
    (hd : (constraintMatrix (fun i => ratVector (a i)) s hs).det ≠ 0) :
    IsRatPoint (constraintVertex (fun i => ratVector (a i)) (fun i => (h i : ℝ)) s) := by
  let e := cellEnumeration s hs
  let M : Matrix (Fin n) (Fin n) ℚ := fun i => a (e i).val
  let b : Fin n → ℚ := fun i => h (e i).val
  let q : Fin n → ℚ := M⁻¹.mulVec b
  have hcast : M.map (fun q : ℚ => (q : ℝ)) =
      constraintMatrix (fun i => ratVector (a i)) s hs := rfl
  have hMd : M.det ≠ 0 := by
    intro hz
    apply hd
    rw [← hcast, ← Rat.cast_det, hz, Rat.cast_zero]
  have hsol : M.mulVec q = b := by
    dsimp only [q]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hMd),
      Matrix.one_mulVec]
  have hrsol : (constraintMatrix (fun i => ratVector (a i)) s hs).mulVec (ratVector q) =
      fun i => (h (e i).val : ℝ) := by
    funext i
    have hh := congrArg (fun t : ℚ => (t : ℝ)) (congrFun hsol i)
    simpa only [Matrix.mulVec, dotProduct, ratVector, Rat.cast_sum, Rat.cast_mul, M, b,
      constraintMatrix, e] using hh
  have hreal : ratVector q =
      constraintVertex (fun i => ratVector (a i)) (fun i => (h i : ℝ)) s := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
    rw [hrsol]
    funext i
    exact (constraintVertex_solves (fun i => ratVector (a i)) (fun i => (h i : ℝ))
      s hs hd (e i).val (e i).property).symm
  exact hreal ▸ ratVector_isRatPoint q

/-- Rational finite H-data has a finite rational vertex realization whenever
its actual intersection is compact. -/
theorem rationalHalfspaces_finite_vertices (a : ι → Fin n → ℚ) (h : ι → ℚ)
    (hc : IsCompact (finiteHalfspaces (fun i => ratVector (a i)) (fun i => (h i : ℝ)))) :
    ∃ s : Finset (V n),
      finiteHalfspaces (fun i => ratVector (a i)) (fun i => (h i : ℝ)) =
        convexHull ℝ (s : Set (V n)) ∧ ∀ x ∈ s, IsRatPoint x := by
  classical
  refine ⟨constraintVertices (fun i => ratVector (a i)) (fun i => (h i : ℝ)),
    finiteHalfspaces_eq_convexHull_constraintVertices_general _ _ hc, ?_⟩
  intro x hx
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hc, hd, _⟩ := (Finset.mem_filter.mp hs).2
  exact constraintVertex_isRatPoint a h s hc hd

end
end Paper17
