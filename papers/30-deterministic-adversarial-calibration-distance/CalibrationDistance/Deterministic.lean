import CalibrationDistance.Core
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Fintype.Pi

/-! The deterministic nonanticipating protocol of §2.2. All forecasts are
functions only of the previous outcomes. The minimax value is defined from
actual calibrated-distance losses, rather than from assumed rate bounds. -/

open scoped BigOperators
open Set

namespace CalibrationDistance

noncomputable section

abbrev ProbabilityForecast := Set.Icc (0 : ℝ) 1

/-- A horizon-T deterministic strategy has precisely the public outcome prefix
available before its current prediction. -/
abbrev DeterministicForecaster (T : ℕ) :=
  (t : Fin T) → (Fin t.val → Bool) → ProbabilityForecast

def halfForecaster (T : ℕ) : DeterministicForecaster T :=
  fun _ _ => ⟨1 / 2, by constructor <;> norm_num⟩

def realOutcomes {T : ℕ} (y : Fin T → Bool) : Fin T → ℝ :=
  fun t => if y t then 1 else 0

def deterministicPath {T : ℕ} (F : DeterministicForecaster T)
    (y : Fin T → Bool) : Fin T → ℝ :=
  fun t => (F t (fun s => y ⟨s.val, lt_trans s.isLt t.isLt⟩)).val

def deterministicLoss {T : ℕ} (F : DeterministicForecaster T)
    (y : Fin T → Bool) : ℝ :=
  calDist (deterministicPath F y) (realOutcomes y)

noncomputable def deterministicWorst {T : ℕ} (F : DeterministicForecaster T) : ℝ :=
  sSup (Set.range (deterministicLoss F))

noncomputable def deterministicMinimax (T : ℕ) : ℝ :=
  sInf (Set.range (@deterministicWorst T))

theorem realOutcomes_valid {T : ℕ} (y : Fin T → Bool) : Valid (realOutcomes y) := by
  intro t
  simp only [realOutcomes]
  split <;> norm_num

theorem deterministicPath_valid {T : ℕ} (F : DeterministicForecaster T)
    (y : Fin T → Bool) : Valid (deterministicPath F y) := by
  intro t
  exact (F t _).property

theorem deterministicLoss_le_worst {T : ℕ} (F : DeterministicForecaster T)
    (y : Fin T → Bool) : deterministicLoss F y ≤ deterministicWorst F := by
  exact le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self y)

theorem worst_le_of_all_losses_le {T : ℕ} (F : DeterministicForecaster T) {C : ℝ}
    (h : ∀ y, deterministicLoss F y ≤ C) : deterministicWorst F ≤ C := by
  exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨y, rfl⟩; exact h y)

theorem deterministicMinimax_le_of_uniform_bound {T : ℕ}
    (F : DeterministicForecaster T) {C : ℝ}
    (h : ∀ y, deterministicLoss F y ≤ C) : deterministicMinimax T ≤ C := by
  apply le_trans (csInf_le ?_ (Set.mem_range_self F)) (worst_le_of_all_losses_le F h)
  refine ⟨0, ?_⟩
  rintro _ ⟨G, rfl⟩
  have := deterministicLoss_le_worst G (fun _ => false)
  have hn : 0 ≤ deterministicLoss G (fun _ => false) := by
    exact calDist_nonneg (realOutcomes_valid _)
  linarith

/-- The lower bound for each deterministic strategy transfers to the genuine
infimum/supremum minimax value, without changing quantifier order. -/
theorem le_deterministicMinimax_of_forall_exists {T : ℕ} {C : ℝ}
    (h : ∀ F : DeterministicForecaster T, ∃ y, C ≤ deterministicLoss F y) :
    C ≤ deterministicMinimax T := by
  unfold deterministicMinimax
  apply le_csInf (show (Set.range (@deterministicWorst T)).Nonempty from
    ⟨_, halfForecaster T, rfl⟩)
  rintro _ ⟨F, rfl⟩
  obtain ⟨y, hy⟩ := h F
  exact hy.trans (deterministicLoss_le_worst F y)

/-- On a single round the calibration comparator is forced to equal the
outcome, exactly as in the final paragraph of §5.2. -/
theorem calDist_one (p y : Fin 1 → ℝ) (hy : Valid y) :
    calDist p y = |p 0 - y 0| := by
  apply le_antisymm
  · simpa [l1Dist] using calDist_le_of_calibrated (p := p) (self_calibrated hy)
  · apply le_csInf (calibratedCosts_nonempty hy)
    rintro _ ⟨r, hr, rfl⟩
    have hz := hr.2 (r 0)
    have he : r 0 = y 0 := by
      have : y 0 - r 0 = 0 := by simpa using hz
      linarith
    simp [l1Dist, he]

lemma deterministic_one_prediction_independent (F : DeterministicForecaster 1)
    (y z : Fin 1 → Bool) : deterministicPath F y 0 = deterministicPath F z 0 := by
  unfold deterministicPath
  congr 2
  funext s
  exact Fin.elim0 s

/-- For every single-round deterministic forecast one of the two fixed strings
has calibration distance at least one half. -/
theorem deterministic_one_round_lower (F : DeterministicForecaster 1) :
    ∃ y, (1 / 2 : ℝ) ≤ deterministicLoss F y := by
  let y0 : Fin 1 → Bool := fun _ => false
  let y1 : Fin 1 → Bool := fun _ => true
  let p := deterministicPath F y0 0
  have hp := deterministicPath_valid F y0 0
  have h0 : deterministicLoss F y0 = p := by
    rw [deterministicLoss, calDist_one _ _ (realOutcomes_valid _)]
    simp [realOutcomes, y0, abs_of_nonneg hp.1, p]
  have h1 : deterministicLoss F y1 = 1 - p := by
    rw [deterministicLoss, calDist_one _ _ (realOutcomes_valid _)]
    rw [deterministic_one_prediction_independent F y1 y0]
    simp [realOutcomes, y1, p, abs_of_nonpos (sub_nonpos.mpr hp.2)]
  by_cases h : (1 / 2 : ℝ) ≤ p
  · exact ⟨y0, by simpa [h0] using h⟩
  · exact ⟨y1, by rw [h1]; linarith⟩

theorem halfForecaster_one_loss (y : Fin 1 → Bool) :
    deterministicLoss (halfForecaster 1) y = (1 / 2 : ℝ) := by
  rw [deterministicLoss, calDist_one _ _ (realOutcomes_valid _)]
  simp only [deterministicPath, halfForecaster, realOutcomes]
  cases y 0 <;> norm_num

/-- The deterministic-oblivious part of Theorem 2.1 at T=1. -/
theorem deterministicMinimax_one : deterministicMinimax 1 = (1 / 2 : ℝ) := by
  apply le_antisymm
  · exact deterministicMinimax_le_of_uniform_bound (halfForecaster 1)
      (fun y => (halfForecaster_one_loss y).le)
  · exact le_deterministicMinimax_of_forall_exists deterministic_one_round_lower

/-- A two-point random tape that outputs its own bit as the forecast. -/
def quantifierExampleLoss (w y : Bool) : ℝ :=
  calDist (fun _ : Fin 1 => if w then 1 else 0)
    (fun _ => if y then 1 else 0)

lemma quantifierExampleLoss_eq (w y : Bool) :
    quantifierExampleLoss w y = if w = y then 0 else 1 := by
  unfold quantifierExampleLoss
  rw [calDist_one]
  · cases w <;> cases y <;> norm_num
  · intro t
    cases y <;> norm_num

/-- Remark 2.3: even for actual one-round calibration losses, supremum over
outcomes and expectation over a private random tape cannot be exchanged.
The displayed averages are expectation under the uniform two-point tape. -/
theorem quantifier_order_strict_example :
    max ((quantifierExampleLoss false false + quantifierExampleLoss true false) / 2)
        ((quantifierExampleLoss false true + quantifierExampleLoss true true) / 2) =
      (1 / 2 : ℝ) ∧
    (max (quantifierExampleLoss false false) (quantifierExampleLoss false true) +
      max (quantifierExampleLoss true false) (quantifierExampleLoss true true)) / 2 = 1 := by
  norm_num [quantifierExampleLoss_eq]

end
end CalibrationDistance
