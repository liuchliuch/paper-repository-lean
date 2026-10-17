import Paper34.Model
import Paper34.ChebyshevCounterexample
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Coverage and nonemptiness of the actual Chebyshev grid

These results concern the `closedCell` and `cube` from `Paper34.Model`.
The closed-cell convention includes shared boundaries, in particular the two
endpoints of the full interval. No choice of a sample is used in the covering.
-/

open Set

namespace Paper34

noncomputable section

/-- Adjacent closed unit intervals cover `[0,m]`, including the right endpoint.
This finite argument avoids a separate floor-function endpoint convention. -/
lemma exists_unit_subinterval : ∀ (m : ℕ), 0 < m → ∀ (u : ℝ),
    0 ≤ u → u ≤ m → ∃ j : Fin m, (j : ℝ) ≤ u ∧ u ≤ (j : ℝ) + 1 := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
    intro hm u hu0 hum
    by_cases hm0 : m = 0
    · subst m
      exact ⟨⟨0, by omega⟩, by simpa using hu0, by simpa using hum⟩
    · by_cases hu : u ≤ (m : ℝ)
      · obtain ⟨j, hj0, hj1⟩ := ih (by omega) u hu0 hu
        exact ⟨⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, hj0, hj1⟩
      · refine ⟨⟨m, Nat.lt_succ_self m⟩, (lt_of_not_ge hu).le, ?_⟩
        simpa using hum

/-- The `m` adjacent angular cells cover the whole interval `[0,π]`. -/
lemma exists_angular_cell (m : ℕ) (hm : 0 < m) (theta : ℝ)
    (htheta0 : 0 ≤ theta) (hthetaPi : theta ≤ Real.pi) :
    ∃ j : Fin m, (j : ℕ) * Real.pi / m ≤ theta ∧
      theta ≤ ((j : ℕ) + (1 : ℝ)) * Real.pi / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hu0 : (0 : ℝ) ≤ theta * m / Real.pi := by positivity
  have hum : theta * m / Real.pi ≤ m := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith [mul_le_mul_of_nonneg_right hthetaPi (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  obtain ⟨j, hj0, hj1⟩ := exists_unit_subinterval m hm (theta * m / Real.pi) hu0 hum
  refine ⟨j, ?_, ?_⟩
  · apply (div_le_iff₀ hm').2
    exact (le_div_iff₀ Real.pi_pos).mp hj0
  · apply (le_div_iff₀ hm').2
    exact (div_le_iff₀ Real.pi_pos).mp hj1

/-- Every point of `[-1,1]` belongs to an actual one-dimensional Chebyshev cell.
The endpoints are handled by the closed angular covering. -/
lemma exists_chebyshev_cell (m : ℕ) (hm : 0 < m) (x : ℝ)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    ∃ j : Fin m, x ∈ ChebyshevCounterexample.cell m j := by
  obtain ⟨j, hj0, hj1⟩ := exists_angular_cell m hm (Real.arccos x)
    (Real.arccos_nonneg x) (Real.arccos_le_pi x)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : (j : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
  have hleft : (0 : ℝ) ≤ (j : ℕ) * Real.pi / m := by positivity
  have hright : ((j : ℕ) + (1 : ℝ)) * Real.pi / m ≤ Real.pi := by
    apply (div_le_iff₀ hm').2
    nlinarith [mul_le_mul_of_nonneg_right hj Real.pi_pos.le]
  refine ⟨j, ?_, ?_⟩
  · simpa only [Real.cos_arccos hx.1 hx.2] using
      Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg x) hright hj1
  · simpa only [Real.cos_arccos hx.1 hx.2] using
      Real.cos_le_cos_of_nonneg_of_le_pi hleft (Real.arccos_le_pi x) hj0

/-- Every actual product cell contains the product of its Chebyshev midpoints. -/
theorem closedCell_nonempty {n m : ℕ} (hm : 0 < m) (j : CellIndex n m) :
    (closedCell j).Nonempty := by
  refine ⟨fun k => ChebyshevCounterexample.node m (j k), ?_, ?_⟩
  · intro k
    exact (ChebyshevCounterexample.node_mem_cell m (by omega) (j k)).1
  · intro k
    exact (ChebyshevCounterexample.node_mem_cell m (by omega) (j k)).2

/-- The actual closed product-Chebyshev cells cover the entire source cube. -/
theorem cube_covered_by_closedCells {n m : ℕ} (hm : 0 < m) (x : Point n)
    (hx : x ∈ cube n) : ∃ j : CellIndex n m, x ∈ closedCell j := by
  classical
  have hcoordinate : ∀ k : Fin n, ∃ j : Fin m,
      x k ∈ ChebyshevCounterexample.cell m j := by
    intro k
    exact exists_chebyshev_cell m hm (x k) ⟨hx.1 k, hx.2 k⟩
  choose j hj using hcoordinate
  refine ⟨j, ?_, ?_⟩
  · intro k
    exact (hj k).1
  · intro k
    exact (hj k).2

/-- Set-valued form of the coverage theorem. Together with the source-model
subset lemma, this identifies the union of all closed cells with the cube. -/
theorem iUnion_closedCell_eq_cube {n m : ℕ} (hm : 0 < m) :
    (⋃ j : CellIndex n m, closedCell j) = cube n := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact closedCell_subset_cube j hj
  · intro hx
    obtain ⟨j, hj⟩ := cube_covered_by_closedCells hm x hx
    exact mem_iUnion.mpr ⟨j, hj⟩

end

end Paper34
