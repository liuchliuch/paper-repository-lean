import CalibrationDistance.Core
import CalibrationDistance.Deterministic

/-! The paper's own finite-horizon ECE calculation in §3. This is proved directly
for the genuine unbinned ECE, including its deterministic-strategy realization. -/

open scoped BigOperators

namespace CalibrationDistance

noncomputable section

def oppositeOutcome (z : ℝ) : ℝ := if z < 1 / 2 then 1 else 0

def oppositeOutcomes {α : Type*} (p : α → ℝ) : α → ℝ :=
  fun t => oppositeOutcome (p t)

theorem oppositeOutcomes_valid {α : Type*} (p : α → ℝ) : Valid (oppositeOutcomes p) := by
  intro t
  unfold oppositeOutcomes oppositeOutcome
  split <;> norm_num

/-- Equal forecasts receive equal opposite outcomes, so a value bucket has
constant-sign residuals and absolute values commute with its sum exactly. -/
theorem oppositeOutcomes_ece_eq {α : Type*} [Fintype α] (p : α → ℝ) :
    ece p (oppositeOutcomes p) = ∑ t, |oppositeOutcomes p t - p t| := by
  classical
  unfold ece
  rw [← sum_grouped p]
  apply Finset.sum_congr rfl
  intro z hz
  have hres : binResidual p (oppositeOutcomes p) z =
      (bucket p z).card * (oppositeOutcome z - z) := by
    unfold binResidual
    calc
      (∑ t ∈ bucket p z, (oppositeOutcomes p t - p t)) =
          ∑ _t ∈ bucket p z, (oppositeOutcome z - z) := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht' : p t = z := (Finset.mem_filter.mp ht).2
        simp only [oppositeOutcomes, ht']
      _ = (bucket p z).card * (oppositeOutcome z - z) := by simp; ring
  have hcost : (∑ t ∈ bucket p z, |oppositeOutcomes p t - p t|) =
      (bucket p z).card * |oppositeOutcome z - z| := by
    calc
      (∑ t ∈ bucket p z, |oppositeOutcomes p t - p t|) =
          ∑ _t ∈ bucket p z, |oppositeOutcome z - z| := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht' : p t = z := (Finset.mem_filter.mp ht).2
        simp only [oppositeOutcomes, ht']
      _ = (bucket p z).card * |oppositeOutcome z - z| := by simp
  rw [hres, hcost, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ (bucket p z).card by exact Nat.cast_nonneg _)]

theorem oppositeOutcome_distance {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    (1 / 2 : ℝ) ≤ |oppositeOutcome z - z| := by
  unfold oppositeOutcome
  split_ifs with h
  · rw [abs_of_nonneg (by linarith [hz.2] : 0 ≤ 1 - z)]
    linarith
  · rw [zero_sub, abs_neg, abs_of_nonneg hz.1]
    linarith

/-- The displayed §3 identity and finite-horizon lower bound, in the stronger
form of an arbitrary finite index set. -/
theorem oakes_finite_calculation {α : Type*} [Fintype α] {p : α → ℝ} (hp : Valid p) :
    ece p (oppositeOutcomes p) = (∑ t, |oppositeOutcomes p t - p t|) ∧
      (Fintype.card α : ℝ) / 2 ≤ ece p (oppositeOutcomes p) := by
  refine ⟨oppositeOutcomes_ece_eq p, ?_⟩
  rw [oppositeOutcomes_ece_eq]
  calc
    (Fintype.card α : ℝ) / 2 = ∑ _t : α, (1 / 2 : ℝ) := by simp; ring
    _ ≤ ∑ t, |oppositeOutcomes p t - p t| :=
      Finset.sum_le_sum fun t ht => oppositeOutcome_distance (hp t)

/-- The outcome at n uses the strategy and earlier outcomes only. Its recursive
calls are all indexed by the strictly shorter supplied prefix. -/
def oakesStream {T : ℕ} (F : DeterministicForecaster T) (n : ℕ) : Bool :=
  if hn : n < T then
    if (F ⟨n, hn⟩ (fun t => oakesStream F t.val) : ℝ) < 1 / 2 then true else false
  else false
termination_by n
decreasing_by all_goals exact t.isLt

def oakesString {T : ℕ} (F : DeterministicForecaster T) : Fin T → Bool :=
  fun t => oakesStream F t.val

theorem oakesString_follows {T : ℕ} (F : DeterministicForecaster T) (t : Fin T) :
    oakesString F t =
      if deterministicPath F (oakesString F) t < 1 / 2 then true else false := by
  change oakesStream F t.val =
    if (F t (fun s => oakesStream F s.val) : ℝ) < 1 / 2 then true else false
  rw [oakesStream]
  simp only [dif_pos t.isLt]

theorem oakesString_realOutcomes {T : ℕ} (F : DeterministicForecaster T) :
    realOutcomes (oakesString F) = oppositeOutcomes (deterministicPath F (oakesString F)) := by
  funext t
  by_cases hp : deterministicPath F (oakesString F) t < 1 / 2
  · simp [realOutcomes, oppositeOutcomes, oppositeOutcome, oakesString_follows, hp]
  · simp [realOutcomes, oppositeOutcomes, oppositeOutcome, oakesString_follows, hp]

/-- Every deterministic nonanticipating forecaster admits one fixed outcome
string whose genuine ECE is at least half the horizon. -/
theorem deterministic_exists_ece_ge_half {T : ℕ} (F : DeterministicForecaster T) :
    ∃ y : Fin T → Bool,
      ece (deterministicPath F y) (realOutcomes y) =
        (∑ t, |realOutcomes y t - deterministicPath F y t|) ∧
      (T : ℝ) / 2 ≤ ece (deterministicPath F y) (realOutcomes y) := by
  refine ⟨oakesString F, ?_⟩
  rw [oakesString_realOutcomes]
  simpa only [Fintype.card_fin] using oakes_finite_calculation (deterministicPath_valid F (oakesString F))

end

end CalibrationDistance
