import Paper17.Basic
import Paper17.Polytope
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Data.Real.Sqrt

/-!
# Example 2.4: Minkowski sums need not be Delzant

Let `A = conv{(0,0),(1,0),(0,1)}` and `B' = conv{(0,0),(-1,0),(0,1)}`.
Both are Delzant polygons.  The primitive outward rays of the normal fan of
`A+B'`, in counterclockwise order, are

`(1,0), (1,1), (-1,1), (-1,0), (0,-1)`.

The adjacent pair `(1,1), (-1,1)` has determinant `2`, so `A+B'` is not
Delzant.  Inserting the ray `(0,1)` yields a smooth fan realized by the hexagon

`T = conv{(2,-2),(2,1),(1,2),(-1,2),(-2,1),(-2,-2)}`,

with all consecutive determinants equal to `1`.
-/

noncomputable section

open scoped BigOperators

namespace Paper17

namespace Example24

/-- A planar vector from two reals. -/
def vec2 (a b : ℝ) : V 2 := ![a, b]

/-- Determinant of two planar vectors `u, v` as `u₁ v₂ - u₂ v₁`. -/
def det2 (u v : V 2) : ℝ := u 0 * v 1 - u 1 * v 0

theorem det2_vec2 (a b c d : ℝ) : det2 (vec2 a b) (vec2 c d) = a * d - b * c := by
  unfold det2 vec2
  simp

/-- The primitive outward rays of `N(A+B')` in counterclockwise order. -/
def raysSum : Fin 5 → V 2
  | 0 => vec2 1 0
  | 1 => vec2 1 1
  | 2 => vec2 (-1) 1
  | 3 => vec2 (-1) 0
  | 4 => vec2 0 (-1)

/-- The smooth hexagon rays in counterclockwise order. -/
def raysT : Fin 6 → V 2
  | 0 => vec2 1 0
  | 1 => vec2 1 1
  | 2 => vec2 0 1
  | 3 => vec2 (-1) 1
  | 4 => vec2 (-1) 0
  | 5 => vec2 0 (-1)

/-- The adjacent pair `(1,1), (-1,1)` of `raysSum` has determinant `2`. -/
theorem det_pair_eq_two : det2 (raysSum 1) (raysSum 2) = 2 := by
  unfold raysSum
  rw [det2_vec2]
  norm_num

/-- Not all consecutive determinants of `raysSum` are `1`, so the fan of
`A+B'` is not smooth. -/
theorem not_all_dets_one :
    ¬ ∀ i : Fin 5, det2 (raysSum i) (raysSum ((i + 1) % 5)) = 1 := by
  intro h
  have h1 : det2 (raysSum 1) (raysSum ((1 + 1) % 5)) = 1 := h 1
  have : ((1 : Fin 5) + 1) % 5 = 2 := by decide
  rw [this] at h1
  have hdet : det2 (raysSum 1) (raysSum 2) = 2 := det_pair_eq_two
  linarith

/-- All consecutive determinants of `raysT` equal `1` (smooth fan). -/
theorem raysT_dets_eq_one : ∀ i : Fin 6, det2 (raysT i) (raysT ((i + 1) % 6)) = 1 := by
  intro i
  fin_cases i
  · show det2 (vec2 1 0) (vec2 1 1) = 1; rw [det2_vec2]; norm_num
  · show det2 (vec2 1 1) (vec2 0 1) = 1; rw [det2_vec2]; norm_num
  · show det2 (vec2 0 1) (vec2 (-1) 1) = 1; rw [det2_vec2]; norm_num
  · show det2 (vec2 (-1) 1) (vec2 (-1) 0) = 1; rw [det2_vec2]; norm_num
  · show det2 (vec2 (-1) 0) (vec2 0 (-1)) = 1; rw [det2_vec2]; norm_num
  · show det2 (vec2 0 (-1)) (vec2 1 0) = 1; rw [det2_vec2]; norm_num

/-- The triangles `A` and `B'`. -/
def Averts : Finset (V 2) := {vec2 0 0, vec2 1 0, vec2 0 1}
def Bverts : Finset (V 2) := {vec2 0 0, vec2 (-1) 0, vec2 0 1}

/-- The hexagon vertex set of `T`. -/
def Tverts : Finset (V 2) :=
  {vec2 2 (-2), vec2 2 1, vec2 1 2, vec2 (-1) 2, vec2 (-2) 1, vec2 (-2) (-2)}

/-- The planar vertex radius is `√8`, attained at `(2,-2)`. -/
theorem max_norm_T : sSup (Set.image (fun x : V 2 => Real.sqrt (x 0 ^ 2 + x 1 ^ 2)) (Tverts : Set (V 2))) = Real.sqrt 8 := by
  classical
  let f : V 2 → ℝ := fun x => Real.sqrt (x 0 ^ 2 + x 1 ^ 2)
  have hne : (f '' (Tverts : Set (V 2))).Nonempty := by
    exact ⟨f (vec2 2 (-2)), ⟨vec2 2 (-2), by simp [Tverts], rfl⟩⟩
  apply le_antisymm
  · apply csSup_le hne
    rintro b ⟨x, hx, rfl⟩
    apply Real.sqrt_le_sqrt
    simp only [Tverts, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [vec2]
  · have hmem : Real.sqrt 8 ∈ f '' (Tverts : Set (V 2)) := by
      refine ⟨vec2 2 (-2), by simp [Tverts], ?_⟩
      norm_num [f, vec2]
    exact le_csSup (Tverts.finite_toSet.image f).bddAbove hmem

end Example24

end Paper17
