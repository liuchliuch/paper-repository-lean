import CalibrationDistance.LowerFinal
import CalibrationDistance.LowerTape
import CalibrationDistance.BehavioralUpper
import CalibrationDistance.Anytime

/-! The principal theorems, retaining the source strategy classes, quantifier
orders, exact constants and genuine calibrated-distance loss. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CalibrationDistance
open Protocol

/-- Theorem 5.1. The deterministic Borel adversary has only the past public
history in its domain; the current private forecast is unavailable to it. -/
theorem randomized_simultaneous_lower (T : ℕ) (hT : 2 ≤ T)
    (K : BehavioralForecaster) :
    ∃ A : Adversary, Real.sqrt (T : ℝ) / 4320 ≤ expectedCalDist K A T := by
  have ha : 1 ≤ lowerExponent (T : ℝ) := lowerExponent_pos (by exact_mod_cast hT)
  obtain ⟨A, hA⟩ := exists_deterministic_adversary_ge_auxiliary K (lowerExponent T) ha T
  exact ⟨A, (randomized_auxiliary_lower K T hT).trans hA⟩

/-- Theorem 5.2. A single string is selected after the deterministic rule and
before play, using its real trajectory loss under the auxiliary law. -/
theorem deterministic_oblivious_lower (T : ℕ) (hT : 2 ≤ T)
    (F : DeterministicForecaster T) :
    ∃ y : Fin T → Bool, Real.sqrt (T : ℝ) / 1200 ≤ deterministicLoss F y := by
  have ha : 1 ≤ lowerExponent (T : ℝ) := lowerExponent_pos (by exact_mod_cast hT)
  exact exists_string_of_integral_calDist_le F
    (meanRevertingAdversary (deterministicBehavioral F) (lowerExponent T) ha)
    (deterministic_auxiliary_lower F hT)

theorem randomized_minimax_lower (T : ℕ) (hT : 2 ≤ T) :
    Real.sqrt (T : ℝ) / 4320 ≤ randAdaptiveMinimax T :=
  le_randAdaptiveMinimax_of_forall_exists T (randomized_simultaneous_lower T hT)

theorem deterministic_minimax_lower (T : ℕ) (hT : 2 ≤ T) :
    Real.sqrt (T : ℝ) / 1200 ≤ deterministicMinimax T :=
  le_deterministicMinimax_of_forall_exists (deterministic_oblivious_lower T hT)

/-- Theorem 2.1, equations (2.7)--(2.9), with both actual minimax values and
an explicit integer optimizer of the shared pathwise upper bound. -/
theorem square_root_minimax_rate (T : ℕ) (hT : 2 ≤ T) :
    (Real.sqrt (T : ℝ) / 4320 ≤ randAdaptiveMinimax T ∧
      randAdaptiveMinimax T ≤ optimalValue T ∧ optimalValue T < Real.sqrt (T : ℝ)) ∧
    (Real.sqrt (T : ℝ) / 1200 ≤ deterministicMinimax T ∧
      deterministicMinimax T ≤ optimalValue T ∧ optimalValue T < Real.sqrt (T : ℝ)) ∧
    (∀ m : ℕ, 1 ≤ m →
      gridObjective T (Nat.ceil ((Real.sqrt (4*(T : ℝ)+1)-1)/2)) ≤ gridObjective T m) := by
  have hT1 : 1 ≤ T := by omega
  exact ⟨⟨randomized_minimax_lower T hT, randAdaptiveMinimax_le_optimalValue T hT1,
      optimalValue_lt_sqrt T hT1⟩,
    ⟨deterministic_minimax_lower T hT, deterministicMinimax_le_optimalValue T hT1,
      optimalValue_lt_sqrt T hT1⟩,
    fun m hm => optimalGrid_minimizes T m hT1 hm⟩

/-- The single-round boundary assertion in Theorem 2.1. -/
theorem minimax_one : randAdaptiveMinimax 1 = (1 / 2 : ℝ) ∧
    deterministicMinimax 1 = (1 / 2 : ℝ) :=
  ⟨randAdaptiveMinimax_one, deterministicMinimax_one⟩

/-- Explicit normalized rates, stronger than the stated asymptotic exponent. -/
theorem normalized_minimax_bounds (T : ℕ) (hT : 2 ≤ T) :
    (1 / (4320 * Real.sqrt (T : ℝ)) ≤ randAdaptiveMinimax T / T ∧
      randAdaptiveMinimax T / T < 1 / Real.sqrt (T : ℝ)) ∧
    (1 / (1200 * Real.sqrt (T : ℝ)) ≤ deterministicMinimax T / T ∧
      deterministicMinimax T / T < 1 / Real.sqrt (T : ℝ)) := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hsp : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTp
  have hs : Real.sqrt (T : ℝ)^2 = T := Real.sq_sqrt hTp.le
  have hr := randomized_minimax_lower T hT
  have hd := deterministic_minimax_lower T hT
  have hru := randAdaptiveMinimax_lt_sqrt T (by omega)
  have hdu := deterministicMinimax_lt_sqrt T (by omega)
  have hnorm (v c : ℝ) (hc : 0 < c) (hl : Real.sqrt (T : ℝ) / c ≤ v)
      (hu : v < Real.sqrt (T : ℝ)) :
      1 / (c * Real.sqrt (T : ℝ)) ≤ v / T ∧ v / T < 1 / Real.sqrt (T : ℝ) := by
    constructor
    · apply (div_le_div_iff₀ (mul_pos hc hsp) hTp).mpr
      have := (div_le_iff₀ hc).mp hl
      nlinarith
    · apply (div_lt_div_iff₀ hTp hsp).mpr
      nlinarith
  exact ⟨hnorm _ _ (by norm_num) hr hru, hnorm _ _ (by norm_num) hd hdu⟩

end CalibrationDistance
