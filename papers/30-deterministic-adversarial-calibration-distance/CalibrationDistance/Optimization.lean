import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace CalibrationDistance

/-- The exact finite-horizon guarantee (6.9), with subtraction in the reals. -/
def gridObjective (T m : ℕ) : ℝ := (T : ℝ) / (2 * (m : ℝ)) + ((m : ℝ) - 1) / 2

/-- The explicit integer optimizer in equation (2.9). -/
def optimalGrid (T : ℕ) : ℕ :=
  Nat.ceil ((Real.sqrt (4 * (T : ℝ) + 1) - 1) / 2)

def optimalValue (T : ℕ) : ℝ := gridObjective T (optimalGrid T)
def ceilSqrtGrid (T : ℕ) : ℕ := Nat.ceil (Real.sqrt (T : ℝ))
def gridRoundingError (T : ℕ) : ℝ := (ceilSqrtGrid T : ℝ) - Real.sqrt (T : ℝ)

private theorem optimizer_root_properties (T : ℕ) (hT : 1 ≤ T) :
    let r := (Real.sqrt (4 * (T : ℝ) + 1) - 1) / 2
    0 < r ∧ r * (r + 1) = (T : ℝ) := by
  dsimp
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hs := Real.sq_sqrt (show 0 ≤ 4 * (T : ℝ) + 1 by positivity)
  have hs0 := Real.sqrt_nonneg (4 * (T : ℝ) + 1)
  constructor <;> nlinarith

/-- The integer in (2.9) is the first positive integer with m(m+1) ≥ T. -/
theorem optimalGrid_threshold (T : ℕ) (hT : 1 ≤ T) :
    1 ≤ optimalGrid T ∧
      ((optimalGrid T : ℝ) - 1) * (optimalGrid T : ℝ) < (T : ℝ) ∧
      (T : ℝ) ≤ (optimalGrid T : ℝ) * ((optimalGrid T : ℝ) + 1) := by
  let r := (Real.sqrt (4 * (T : ℝ) + 1) - 1) / 2
  have hr := optimizer_root_properties T hT
  change 0 < r ∧ r * (r + 1) = (T : ℝ) at hr
  have hm : 1 ≤ optimalGrid T := Nat.one_le_ceil_iff.mpr hr.1
  have hmr : r ≤ (optimalGrid T : ℝ) := Nat.le_ceil r
  have hmr' : (optimalGrid T : ℝ) < r + 1 := Nat.ceil_lt_add_one (le_of_lt hr.1)
  have hm' : (1 : ℝ) ≤ optimalGrid T := by exact_mod_cast hm
  refine ⟨hm, ?_, ?_⟩ <;> nlinarith

/-- Exact adjacent-grid difference used in Corollary 6.4. -/
theorem gridObjective_successor_difference (T m : ℕ) (hm : 1 ≤ m) :
    gridObjective T (m + 1) - gridObjective T m =
      ((m : ℝ) * ((m : ℝ) + 1) - T) / (2 * (m : ℝ) * ((m : ℝ) + 1)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  simp only [gridObjective, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

private theorem gridObjective_difference (T m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    gridObjective T n - gridObjective T m =
      ((n : ℝ) - m) * ((m : ℝ) * n - T) / (2 * (m : ℝ) * n) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  simp only [gridObjective]
  field_simp
  <;> ring

/-- The exact formula (2.9) minimizes (6.9) over every positive integer grid. -/
theorem optimalGrid_minimizes (T n : ℕ) (hT : 1 ≤ T) (hn : 1 ≤ n) :
    gridObjective T (optimalGrid T) ≤ gridObjective T n := by
  obtain ⟨hm, hlo, hhi⟩ := optimalGrid_threshold T hT
  have hm' : (0 : ℝ) < optimalGrid T := by exact_mod_cast (show 0 < optimalGrid T by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd := gridObjective_difference T (optimalGrid T) n hm hn
  have hnum : 0 ≤ ((n : ℝ) - optimalGrid T) * ((optimalGrid T : ℝ) * n - T) := by
    rcases le_total n (optimalGrid T) with hle | hle
    · by_cases heq : n = optimalGrid T
      · simp [heq]
      have hlt : (n : ℝ) ≤ (optimalGrid T : ℝ) - 1 := by
        have : n + 1 ≤ optimalGrid T := by omega
        have hcast : (n : ℝ) + 1 ≤ (optimalGrid T : ℝ) := by exact_mod_cast this
        linarith
      have hnonpos : (optimalGrid T : ℝ) * n - T ≤ 0 := by nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos (by nlinarith) hnonpos
    · by_cases heq : n = optimalGrid T
      · simp [heq]
      have hlt : (optimalGrid T : ℝ) + 1 ≤ n := by
        have : optimalGrid T + 1 ≤ n := by omega
        exact_mod_cast this
      exact mul_nonneg (by nlinarith) (by nlinarith)
  have hdiff : 0 ≤ gridObjective T n - gridObjective T (optimalGrid T) := by
    rw [hd]
    exact div_nonneg hnum (by positivity)
  linarith

theorem optimalValue_le_gridObjective (T n : ℕ) (hT : 1 ≤ T) (hn : 1 ≤ n) :
    optimalValue T ≤ gridObjective T n := optimalGrid_minimizes T n hT hn

/-- Ceil-sqrt rounding has precisely the error interval stated in Corollary 6.4. -/
theorem gridRoundingError_bounds (T : ℕ) :
    0 ≤ gridRoundingError T ∧ gridRoundingError T < 1 := by
  have hlo := Nat.le_ceil (Real.sqrt (T : ℝ))
  have hhi := Nat.ceil_lt_add_one (Real.sqrt_nonneg (T : ℝ))
  change 0 ≤ (Nat.ceil (Real.sqrt (T : ℝ)) : ℝ) - Real.sqrt (T : ℝ) ∧
    (Nat.ceil (Real.sqrt (T : ℝ)) : ℝ) - Real.sqrt (T : ℝ) < 1
  constructor <;> linarith

theorem ceilSqrtGrid_pos (T : ℕ) (hT : 1 ≤ T) : 1 ≤ ceilSqrtGrid T := by
  apply Nat.one_le_ceil_iff.mpr
  apply Real.sqrt_pos.2
  exact_mod_cast (show 0 < T by omega)

/-- The equality in (6.10), including the exact quadratic rounding correction. -/
theorem ceilSqrtGrid_objective_identity (T : ℕ) (hT : 1 ≤ T) :
    gridObjective T (ceilSqrtGrid T) = Real.sqrt (T : ℝ) - 1 / 2 +
      gridRoundingError T ^ 2 / (2 * (ceilSqrtGrid T : ℝ)) := by
  have hm : (0 : ℝ) < ceilSqrtGrid T := by
    exact_mod_cast (show 0 < ceilSqrtGrid T from lt_of_lt_of_le Nat.zero_lt_one (ceilSqrtGrid_pos T hT))
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ T by positivity)
  unfold gridObjective gridRoundingError
  field_simp
  nlinarith

/-- The strict leading-constant bound in (6.10), valid also at T = 1. -/
theorem ceilSqrtGrid_objective_lt_sqrt (T : ℕ) (hT : 1 ≤ T) :
    gridObjective T (ceilSqrtGrid T) < Real.sqrt (T : ℝ) := by
  obtain ⟨hd0, hd1⟩ := gridRoundingError_bounds T
  have hm : (1 : ℝ) ≤ ceilSqrtGrid T := by exact_mod_cast ceilSqrtGrid_pos T hT
  have hd2 : gridRoundingError T ^ 2 < (ceilSqrtGrid T : ℝ) := by
    nlinarith
  rw [ceilSqrtGrid_objective_identity T hT]
  have : gridRoundingError T ^ 2 / (2 * (ceilSqrtGrid T : ℝ)) < (1 : ℝ) / 2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (ceilSqrtGrid T : ℝ))).2
    nlinarith
  linarith

/-- The advertised optimized finite-horizon guarantee is strictly below sqrt T. -/
theorem optimalValue_lt_sqrt (T : ℕ) (hT : 1 ≤ T) :
    optimalValue T < Real.sqrt (T : ℝ) :=
  lt_of_le_of_lt (optimalValue_le_gridObjective T (ceilSqrtGrid T) hT (ceilSqrtGrid_pos T hT))
    (ceilSqrtGrid_objective_lt_sqrt T hT)


/-- A natural-number characterization of the exact optimizer, without a minimizer premise. -/
theorem optimalGrid_le_iff (T n : ℕ) (hT : 1 ≤ T) :
    optimalGrid T ≤ n ↔ T ≤ n * (n + 1) := by
  let r := (Real.sqrt (4 * (T : ℝ) + 1) - 1) / 2
  have hr := optimizer_root_properties T hT
  change 0 < r ∧ r * (r + 1) = (T : ℝ) at hr
  change Nat.ceil r ≤ n ↔ _
  rw [Nat.ceil_le]
  have hn : (0 : ℝ) ≤ n := by positivity
  constructor
  · intro h
    have : (T : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by nlinarith
    exact_mod_cast this
  · intro h
    have h' : (T : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast h
    nlinarith

/-- There is a second minimizing grid exactly at a triangular-number boundary. -/
theorem optimalGrid_successor_tie (T : ℕ) (hT : 1 ≤ T)
    (htie : (T : ℝ) = (optimalGrid T : ℝ) * ((optimalGrid T : ℝ) + 1)) :
    gridObjective T (optimalGrid T + 1) = optimalValue T := by
  have hd := gridObjective_successor_difference T (optimalGrid T) (optimalGrid_threshold T hT).1
  rw [← htie, sub_self, zero_div] at hd
  exact sub_eq_zero.mp hd

/-- Away from the triangular boundary, the integer optimizer is unique. -/
theorem optimalGrid_unique (T n : ℕ) (hT : 1 ≤ T) (hn : 1 ≤ n)
    (hstrict : (T : ℝ) < (optimalGrid T : ℝ) * ((optimalGrid T : ℝ) + 1))
    (heq : gridObjective T n = optimalValue T) : n = optimalGrid T := by
  obtain ⟨hm, hlo, hhi⟩ := optimalGrid_threshold T hT
  have hm' : (0 : ℝ) < optimalGrid T := by exact_mod_cast (show 0 < optimalGrid T by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd := gridObjective_difference T (optimalGrid T) n hm hn
  change gridObjective T n = gridObjective T (optimalGrid T) at heq
  rw [heq, sub_self] at hd
  have hz : ((n : ℝ) - optimalGrid T) * ((optimalGrid T : ℝ) * n - T) = 0 :=
    (div_eq_zero_iff.mp hd.symm).resolve_right (by positivity)
  rcases mul_eq_zero.mp hz with hz | hz
  · exact_mod_cast sub_eq_zero.mp hz
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hcast : (n : ℝ) + 1 ≤ optimalGrid T := by exact_mod_cast (show n + 1 ≤ optimalGrid T by omega)
      nlinarith
    · have hcast : (optimalGrid T : ℝ) + 1 ≤ n := by exact_mod_cast (show optimalGrid T + 1 ≤ n by omega)
      nlinarith

/-- The optimized grid has the square-root size used in the implementation bound. -/
theorem optimalGrid_sqrt_bounds (T : ℕ) (hT : 1 ≤ T) :
    Real.sqrt (T : ℝ) / 2 ≤ (optimalGrid T : ℝ) ∧
      (optimalGrid T : ℝ) < Real.sqrt (T : ℝ) + 1 := by
  obtain ⟨hm, hlo, hhi⟩ := optimalGrid_threshold T hT
  have hm' : (1 : ℝ) ≤ optimalGrid T := by exact_mod_cast hm
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ T by positivity)
  have hs0 := Real.sqrt_nonneg (T : ℝ)
  constructor <;> nlinarith

end CalibrationDistance
