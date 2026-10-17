import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The six-observation counterexample to cellwise-majority LAD

This is the example in P34, S4.p5.  There is one variable, degree bound two,
and two Chebyshev cells.  Each cell contains three observations, of which
exactly one is corrupted.  The two uncorrupted locations coincide at the
midpoint of their cell.  We retain actual `Polynomial ℝ` evaluations in the
data and in the weighted least-absolute-deviations objective.

Cell zero is the right cell and cell one is the left cell, as prescribed by
the paper's decreasing-cosine indexing.  No location is on their common
boundary, so the choice of boundary convention is immaterial here.
-/

namespace Paper34.LADCounterexample

noncomputable section

open Polynomial
open scoped BigOperators

abbrev Cell := Fin 2
abbrev Observation := Fin 3

/-- The actual Chebyshev intervals for `m = 2`, with zero-based indexing. -/
def chebyshevCell (j : Cell) : Set ℝ :=
  Set.Icc (Real.cos (((j : ℕ) + (1 : ℝ)) * Real.pi / 2))
    (Real.cos ((j : ℕ) * Real.pi / 2))

/-- Two inliers at each of `±1/2`, and an outlier at each of `±1`. -/
def location (j : Cell) (i : Observation) : ℝ :=
  if j = 0 then (if i = 2 then 1 else 1 / 2)
  else (if i = 2 then -1 else -(1 / 2))

def corrupted (i : Observation) : Prop := i = 2

instance : DecidablePred corrupted := fun _ => inferInstanceAs (Decidable (_ = _))

/-- The signal is the zero polynomial and the noise bound is zero. -/
def truth : ℝ[X] := 0

def sigma : ℝ := 0

/-- The genuine quadratic direction used for the corrupt labels. -/
def quadratic (K : ℝ) : ℝ[X] := C K * (X ^ 2 - C (1 / 4))

/-- Inliers have exact zero labels; corrupt labels are evaluations of `quadratic K`. -/
def label (K : ℝ) (j : Cell) (i : Observation) : ℝ :=
  if corrupted i then (quadratic K).eval (location j i) else 0

def badIndices : Finset Observation := Finset.univ.filter corrupted

def goodIndices : Finset Observation := Finset.univ.filter (fun i => ¬ corrupted i)

/-- Equation (2.6) with `n = 1`, `m = 2`, and `N_C = 3` in each cell. -/
def weightedLAD (K : ℝ) (r : ℝ[X]) : ℝ :=
  (1 / (2 : ℝ) ^ 1) * ∑ j : Cell,
    (1 / (Fintype.card Observation : ℝ)) *
      ∑ i : Observation, |r.eval (location j i) - label K j i|

@[simp] theorem quadratic_eval (K x : ℝ) :
    (quadratic K).eval x = K * (x ^ 2 - 1 / 4) := by
  simp [quadratic]

theorem quadratic_natDegree (K : ℝ) (hK : K ≠ 0) :
    (quadratic K).natDegree = 2 := by
  rw [quadratic, Polynomial.natDegree_C_mul hK, Polynomial.natDegree_X_pow_sub_C]

theorem quadratic_natDegree_le (K : ℝ) : (quadratic K).natDegree ≤ 2 := by
  exact (Polynomial.natDegree_C_mul_le K _).trans
    (by rw [Polynomial.natDegree_X_pow_sub_C])

theorem quadratic_ne_zero (K : ℝ) (hK : K ≠ 0) : quadratic K ≠ 0 := by
  intro hzero
  have hdeg := quadratic_natDegree K hK
  rw [hzero, Polynomial.natDegree_zero] at hdeg
  norm_num at hdeg

@[simp] theorem truth_natDegree_le : truth.natDegree ≤ 2 := by
  norm_num [truth]

theorem right_cell : chebyshevCell 0 = Set.Icc (0 : ℝ) 1 := by
  norm_num [chebyshevCell, Real.cos_pi_div_two]

theorem left_cell : chebyshevCell 1 = Set.Icc (-1 : ℝ) 0 := by
  have hangle : (2 : ℝ) * Real.pi / 2 = Real.pi := by ring
  norm_num [chebyshevCell, hangle, Real.cos_pi_div_two]

theorem location_mem_cell (j : Cell) (i : Observation) :
    location j i ∈ chebyshevCell j := by
  fin_cases j <;> fin_cases i <;>
    norm_num [right_cell, left_cell, location, Fin.ext_iff]

theorem location_ne_common_boundary (j : Cell) (i : Observation) :
    location j i ≠ 0 := by
  fin_cases j <;> fin_cases i <;> norm_num [location, Fin.ext_iff]

/-- A sample belongs to exactly its designated actual Chebyshev cell. -/
theorem location_mem_cell_iff (j k : Cell) (i : Observation) :
    location j i ∈ chebyshevCell k ↔ j = k := by
  fin_cases j <;> fin_cases k <;> fin_cases i <;>
    norm_num [right_cell, left_cell, location, Fin.ext_iff]

/-- The actual six indexed observations in a specified cell. -/
def cellSamples (j : Cell) : Finset (Cell × Observation) :=
  Finset.univ.filter (fun s => s.1 = j)

def badCellSamples (j : Cell) : Finset (Cell × Observation) :=
  (cellSamples j).filter (fun s => corrupted s.2)

def goodCellSamples (j : Cell) : Finset (Cell × Observation) :=
  (cellSamples j).filter (fun s => ¬ corrupted s.2)

theorem cellSamples_mem_iff (j : Cell) (s : Cell × Observation) :
    s ∈ cellSamples j ↔ location s.1 s.2 ∈ chebyshevCell j := by
  simp [cellSamples, location_mem_cell_iff]

@[simp] theorem cellSamples_card (j : Cell) : (cellSamples j).card = 3 := by
  fin_cases j <;> decide

@[simp] theorem badCellSamples_card (j : Cell) : (badCellSamples j).card = 1 := by
  fin_cases j <;> decide

@[simp] theorem goodCellSamples_card (j : Cell) : (goodCellSamples j).card = 2 := by
  fin_cases j <;> decide

theorem per_cell_outlier_fraction (j : Cell) :
    ((badCellSamples j).card : ℝ) / ((cellSamples j).card : ℝ) = 1 / 3 := by
  norm_num

theorem per_cell_strict_majority (j : Cell) :
    (badCellSamples j).card < (goodCellSamples j).card := by
  norm_num

@[simp] theorem observations_per_cell : Fintype.card Observation = 3 := by decide

@[simp] theorem number_of_cells : Fintype.card Cell = 2 := by decide

theorem total_observations : Fintype.card (Cell × Observation) = 6 := by decide

@[simp] theorem bad_count : badIndices.card = 1 := by
  decide

@[simp] theorem good_count : goodIndices.card = 2 := by
  decide

/-- In every cell the outlier fraction is exactly one third. -/
theorem outlier_fraction :
    (badIndices.card : ℝ) / (Fintype.card Observation : ℝ) = 1 / 3 := by
  norm_num

theorem strict_inlier_majority : badIndices.card < goodIndices.card := by
  norm_num [bad_count, good_count]

/-- The samples satisfy the zero-noise inlier condition at the true polynomial. -/
theorem inliers_exact (K : ℝ) (j : Cell) (i : Observation) (hi : ¬ corrupted i) :
    |truth.eval (location j i) - label K j i| ≤ sigma := by
  simp [truth, label, hi, sigma]

/-- Every observation, including the four exact inliers, is fitted by the quadratic. -/
theorem quadratic_fits (K : ℝ) (j : Cell) (i : Observation) :
    (quadratic K).eval (location j i) = label K j i := by
  fin_cases j <;> fin_cases i <;>
    norm_num [label, corrupted, location, quadratic_eval, Fin.ext_iff]

theorem weightedLAD_nonneg (K : ℝ) (r : ℝ[X]) : 0 ≤ weightedLAD K r := by
  unfold weightedLAD
  positivity

theorem weightedLAD_quadratic (K : ℝ) : weightedLAD K (quadratic K) = 0 := by
  simp only [weightedLAD, quadratic_fits, sub_self, abs_zero,
    Finset.sum_const_zero, mul_zero]

theorem truth_residual (K : ℝ) (hK : 0 < K) (j : Cell) (i : Observation) :
    |truth.eval (location j i) - label K j i| =
      if corrupted i then 3 * K / 4 else 0 := by
  fin_cases j <;> fin_cases i <;>
    norm_num [truth, label, corrupted, location, quadratic_eval, Fin.ext_iff,
      abs_mul, abs_of_pos hK] <;> ring

/-- The exact value of the paper's weighted objective at the true polynomial. -/
theorem weightedLAD_truth (K : ℝ) (hK : 0 < K) : weightedLAD K truth = K / 4 := by
  unfold weightedLAD
  simp_rw [truth_residual K hK]
  norm_num [Fin.sum_univ_two, Fin.sum_univ_three, corrupted, Fin.ext_iff]
  <;> ring

/-- Thus this wrong polynomial is an actual global weighted-LAD minimizer. -/
theorem quadratic_minimizes (K : ℝ) :
    ∀ r : ℝ[X], weightedLAD K (quadratic K) ≤ weightedLAD K r := by
  intro r
  rw [weightedLAD_quadratic]
  exact weightedLAD_nonneg K r

theorem truth_not_minimizer (K : ℝ) (hK : 0 < K) :
    ¬ ∀ r : ℝ[X], r.natDegree ≤ 2 → weightedLAD K truth ≤ weightedLAD K r := by
  intro h
  have hbad := h (quadratic K) (quadratic_natDegree_le K)
  rw [weightedLAD_truth K hK, weightedLAD_quadratic] at hbad
  exact (not_le_of_gt (by positivity : (0 : ℝ) < K / 4)) hbad

/-- S4.p5, including the actual cell geometry, observed labels, degree bound,
per-cell corruption fraction, exact-inlier condition, and both LAD values. -/
theorem six_observation_counterexample (K : ℝ) (hK : 0 < K) :
    Fintype.card (Cell × Observation) = 6 ∧
    (∀ j i, location j i ∈ chebyshevCell j) ∧
    (∀ j, (cellSamples j).card = 3 ∧ (badCellSamples j).card = 1 ∧
      (goodCellSamples j).card = 2 ∧
      ((badCellSamples j).card : ℝ) / ((cellSamples j).card : ℝ) = 1 / 3) ∧
    (badIndices.card : ℝ) / (Fintype.card Observation : ℝ) = 1 / 3 ∧
    badIndices.card < goodIndices.card ∧
    (∀ j i, ¬ corrupted i → |truth.eval (location j i) - label K j i| ≤ sigma) ∧
    (quadratic K).natDegree = 2 ∧
    quadratic K ≠ truth ∧
    weightedLAD K (quadratic K) = 0 ∧
    weightedLAD K truth = K / 4 ∧
    0 < weightedLAD K truth := by
  refine ⟨total_observations, location_mem_cell, ?_, outlier_fraction,
    strict_inlier_majority, inliers_exact K, quadratic_natDegree K hK.ne', ?_,
    weightedLAD_quadratic K, weightedLAD_truth K hK, ?_⟩
  · intro j
    exact ⟨cellSamples_card j, badCellSamples_card j, goodCellSamples_card j,
      per_cell_outlier_fraction j⟩
  · exact quadratic_ne_zero K hK.ne'
  · rw [weightedLAD_truth K hK]
    positivity

end

end Paper34.LADCounterexample
