import Paper26.MultiscaleRefinement
import Paper26.CollectiveSubmatrixRoutine

/-!
# Scalar collective multiscale copy accounting

There is no execution, learner, stage certificate or probabilistic assumption
in this file.  The actual source mass allowances and accuracy schedule imply
one global integer copy allowance for every stage and every active dimension.
The final ceiling is absorbed with its exact dimension/rank exponents and the
collective logarithm `log(L/delta)`, with no extra rank or dimension logarithm.
-/
noncomputable section

namespace Paper26.MultiscaleCollectiveCost
open MultiscaleRefinement

/-- The exact constant in the proved Proposition 5.5 copy estimate. -/
abbrev routineConstant : ℝ := CollectiveSubmatrixRoutine.universalConstant

/-- Rank/dimension scale for one collective stage, before its common log. -/
def scale (r d L : ℕ) (e : ℝ) : ℝ :=
  Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) * L / e

theorem stageCount_pos {d L : ℕ} {e : ℝ} (he : 0 < e) (hed : e < d)
    (hL : L = dyadicStages d e) : 0 < L := by
  rw [hL]
  exact dyadicStages_pos d he hed

theorem scale_ge_one {r d L : ℕ} {e : ℝ} (hr : 1 ≤ r) (hrd : r ≤ d)
    (hL : 0 < L) (he : 0 < e) (hed : e < d) : 1 ≤ scale r d L e := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hr.trans hrd
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hsr : 1 ≤ Real.sqrt (r : ℝ) := Real.one_le_sqrt.mpr hrR
  have hsd : 1 ≤ Real.sqrt (d : ℝ) := Real.one_le_sqrt.mpr hdR
  have hroots : 1 ≤ Real.sqrt (r : ℝ) * Real.sqrt (d : ℝ) := by
    simpa only [one_mul] using mul_le_mul hsr hsd (by norm_num) (Real.sqrt_nonneg _)
  have hratio : 1 ≤ (d : ℝ) * L / e := by
    apply (le_div_iff₀ he).mpr
    have hm := mul_le_mul_of_nonneg_left hLR (show (0 : ℝ) ≤ d by positivity)
    nlinarith
  calc
    1 ≤ (Real.sqrt (r : ℝ) * Real.sqrt (d : ℝ)) * ((d : ℝ) * L / e) := by
      simpa only [one_mul] using mul_le_mul hroots hratio (by norm_num) (by positivity)
    _ = scale r d L e := by unfold scale; ring

/-- Pure scalar stage bound.  Stage zero is treated directly with W=1 and
eta=e/(16L); later stages use the source's proved mass allowance inequality. -/
theorem stage_mass_cost_le {r d L k : ℕ} {e : ℝ}
    (hr : 1 ≤ r) (hrd : r ≤ d) (hkd : k ≤ d)
    (he : 0 < e) (hed : e < d) (hL : L = dyadicStages d e) (j : Fin L) :
    (k : ℝ) * massAllowance r e L j / stageAccuracy e L j ≤ 32 * scale r d L e := by
  have hLp := stageCount_pos he hed hL
  letI : NeZero L := ⟨hLp.ne'⟩
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hLp
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrdR : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hkdR : (k : ℝ) ≤ d := by exact_mod_cast hkd
  have hη : 0 < stageAccuracy e L j := by
    unfold stageAccuracy
    exact div_pos (mul_pos he (dyadicLower_pos L j)) (by positivity)
  have hW := massAllowance_nonneg r e L j
  have hs := scale_ge_one hr hrd hLp he hed
  by_cases hj : j.val = 0
  · have hm : massAllowance r e L j = 1 := by simp [massAllowance, hj]
    have ha : stageAccuracy e L j = e / (16 * (L : ℝ)) := by
      simp only [stageAccuracy, dyadicLower, hj]
      norm_num
      ring
    have hsr : 1 ≤ Real.sqrt (r : ℝ) := Real.one_le_sqrt.mpr hrR
    have hsd : 1 ≤ Real.sqrt (d : ℝ) :=
      Real.one_le_sqrt.mpr (by exact_mod_cast hr.trans hrd)
    have hroots : 1 ≤ Real.sqrt (r : ℝ) * Real.sqrt (d : ℝ) := by
      simpa only [one_mul] using mul_le_mul hsr hsd (by norm_num) (Real.sqrt_nonneg _)
    have heq : (k : ℝ) * 1 / (e / (16 * (L : ℝ))) = 16 * k * L / e := by
      field_simp
    rw [hm, ha, heq]
    calc
      16 * (k : ℝ) * L / e ≤ 16 * (d : ℝ) * L / e := by gcongr
      _ ≤ 16 * (Real.sqrt (r : ℝ) * Real.sqrt (d : ℝ) * ((d : ℝ) * L / e)) := by
        have hh := mul_le_mul_of_nonneg_right hroots
          (show 0 ≤ (d : ℝ) * L / e by positivity)
        convert mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 16) using 1
        ring
      _ = 16 * scale r d L e := by unfold scale; ring
      _ ≤ 32 * scale r d L e := by nlinarith
  · have hf : e / (2 * (d : ℝ)) ≤ dyadicLower L j := by
      have hl : e / (2 * (d : ℝ)) < dyadicLower L (lastStage L) := by
        rw [dyadicLower_last, hL]
        exact (dyadicStages_window d he hed).2
      exact hl.le.trans (dyadicLower_floor L j)
    have hc := stageCost_le hrR hrdR hLR he hf (rfl : stageAccuracy e L j = _)
      (massAllowance_le hr e L j)
    have hterm : (r : ℝ) * ((k : ℝ) * massAllowance r e L j / stageAccuracy e L j) ≤
        stageCost r d (massAllowance r e L j) (stageAccuracy e L j) := by
      unfold stageCost
      calc
        _ ≤ (r : ℝ) * ((d : ℝ) * massAllowance r e L j / stageAccuracy e L j) := by gcongr
        _ ≤ _ := by
          have hnonneg : 0 ≤ (d : ℝ) * Real.sqrt ((r : ℝ) / stageAccuracy e L j) := by positivity
          have heq : (r : ℝ) * ((d : ℝ) * massAllowance r e L j / stageAccuracy e L j) =
              (r : ℝ) * d * massAllowance r e L j / stageAccuracy e L j := by ring
          rw [heq]
          exact le_add_of_nonneg_right hnonneg
    have hh : (r : ℝ) * ((k : ℝ) * massAllowance r e L j / stageAccuracy e L j) ≤
        (r : ℝ) * (32 * scale r d L e) := by
      apply hterm.trans
      calc
        _ ≤ _ := hc
        _ = _ := by unfold scale; ring
    exact (mul_le_mul_iff_right₀ (by linarith : (0 : ℝ) < r)).mp hh

/-- Common collective confidence allocation; no dimension occurs in its log. -/
def stageFailure (L : ℕ) (δ : ℝ) : ℝ := δ / (L : ℝ)

theorem stageFailure_range {L : ℕ} (hL : 0 < L) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    0 < stageFailure L δ ∧ stageFailure L δ < 1 / 2 := by
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  constructor
  · exact div_pos hδ hLp
  · apply (div_lt_iff₀ hLp).mpr
    nlinarith

theorem confidence_log_eq {L : ℕ} (_hL : 0 < L) (δ : ℝ) :
    Real.log (1 / stageFailure L δ) = Real.log ((L : ℝ) / δ) := by
  congr 1
  unfold stageFailure
  rw [one_div, inv_div]

theorem confidence_log_ge_half {L : ℕ} (hL : 0 < L) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) : 1 / 2 ≤ Real.log ((L : ℝ) / δ) := by
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have htwo : (2 : ℝ) ≤ (L : ℝ) / δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hh
  exact hh.trans (Real.log_le_log (by norm_num) htwo)

theorem routineConstant_ge_one : 1 ≤ routineConstant := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hi : 0 ≤ 1 / Real.log 2 := by positivity
  unfold routineConstant CollectiveSubmatrixRoutine.universalConstant
  nlinarith

def globalBudget (r d L : ℕ) (e δ : ℝ) : ℝ :=
  32 * routineConstant * scale r d L e * Real.log ((L : ℝ) / δ)

/-- One integer allowance, independent of the stage and its active dimension. -/
def globalN (r d L : ℕ) (e δ : ℝ) : ℕ := Nat.ceil (globalBudget r d L e δ)

theorem globalBudget_ge_one {r d L : ℕ} {e δ : ℝ}
    (hr : 1 ≤ r) (hrd : r ≤ d) (he : 0 < e) (hed : e < d)
    (hL : L = dyadicStages d e) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    1 ≤ globalBudget r d L e δ := by
  have hLp := stageCount_pos he hed hL
  have hs := scale_ge_one hr hrd hLp he hed
  have hl := confidence_log_ge_half hLp hδ hδhalf
  have hc : 1 ≤ routineConstant * scale r d L e := by
    simpa only [one_mul] using mul_le_mul routineConstant_ge_one hs (by norm_num)
      CollectiveSubmatrixRoutine.universalConstant_pos.le
  have hm := mul_le_mul hc hl (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith)
  unfold globalBudget
  nlinarith

theorem globalN_pos {r d L : ℕ} {e δ : ℝ}
    (hr : 1 ≤ r) (hrd : r ≤ d) (he : 0 < e) (hed : e < d)
    (hL : L = dyadicStages d e) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    0 < globalN r d L e δ := by
  apply Nat.ceil_pos.mpr
  have h := globalBudget_ge_one hr hrd he hed hL hδ hδhalf
  linarith

/-- Every stage's Proposition 5.5 real copy expression is bounded by the
same integer.  This is only scalar transitivity, with no learner input. -/
theorem stage_routine_cost_le_globalN {r d L k : ℕ} {e δ : ℝ}
    (hr : 1 ≤ r) (hrd : r ≤ d) (hkd : k ≤ d)
    (he : 0 < e) (hed : e < d) (hL : L = dyadicStages d e)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (j : Fin L) :
    routineConstant * ((k : ℝ) * massAllowance r e L j / stageAccuracy e L j) *
      Real.log (1 / stageFailure L δ) ≤ (globalN r d L e δ : ℝ) := by
  have hLp := stageCount_pos he hed hL
  have hl : 0 ≤ Real.log ((L : ℝ) / δ) := by
    have h := confidence_log_ge_half hLp hδ hδhalf
    linarith
  rw [confidence_log_eq hLp]
  apply le_trans _ (Nat.le_ceil (globalBudget r d L e δ))
  unfold globalBudget
  have hc := mul_le_mul_of_nonneg_left (stage_mass_cost_le hr hrd hkd he hed hL j)
    CollectiveSubmatrixRoutine.universalConstant_pos.le
  have hm := mul_le_mul_of_nonneg_right hc hl
  nlinarith

/-- The literal zero/nonzero integer-cost conclusion of Proposition 5.5
therefore fits the common allowance.  The premise is only its preceding
scalar cost estimate, not a global budget, learner or stage-data assertion. -/
theorem allocated_copies_le_globalN {r d L k n : ℕ} {e δ : ℝ}
    (hr : 1 ≤ r) (hrd : r ≤ d) (hkd : k ≤ d)
    (he : 0 < e) (hed : e < d) (hL : L = dyadicStages d e)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (j : Fin L)
    (hcopies : if massAllowance r e L j ^ 2 ≤ stageAccuracy e L j then n = 0 else
      (n : ℝ) ≤ routineConstant *
        ((k : ℝ) * massAllowance r e L j / stageAccuracy e L j) *
          Real.log (1 / stageFailure L δ)) :
    n ≤ globalN r d L e δ := by
  split_ifs at hcopies with hz
  · rw [hcopies]
    exact Nat.zero_le _
  · have h := hcopies.trans (stage_routine_cost_le_globalN hr hrd hkd he hed hL hδ hδhalf j)
    exact_mod_cast h

/-- Explicit universal constant after absorbing the single final ceiling. -/
def universalConstant : ℝ := 64 * routineConstant

theorem universalConstant_pos : 0 < universalConstant := by
  unfold universalConstant
  exact mul_pos (by norm_num) CollectiveSubmatrixRoutine.universalConstant_pos

/-- Total allowance for L stages with the sharp collective rank/dimension
exponents and only `log(L/delta)`.  Every integer rounding is included. -/
theorem total_copies_le {r d L : ℕ} {e δ : ℝ}
    (hr : 1 ≤ r) (hrd : r ≤ d) (he : 0 < e) (hed : e < d)
    (hL : L = dyadicStages d e) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ((globalN r d L e δ * L : ℕ) : ℝ) ≤
      universalConstant * (Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) * (L : ℝ)^2 / e) *
        Real.log ((L : ℝ) / δ) := by
  have hx := globalBudget_ge_one hr hrd he hed hL hδ hδhalf
  have hn := (Nat.ceil_lt_add_one (show 0 ≤ globalBudget r d L e δ by linarith)).le
  have hN : (globalN r d L e δ : ℝ) ≤ 2 * globalBudget r d L e δ := by
    change (Nat.ceil (globalBudget r d L e δ) : ℝ) ≤ _
    linarith
  rw [Nat.cast_mul]
  calc
    _ ≤ (2 * globalBudget r d L e δ) * L :=
      mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg L)
    _ = _ := by unfold globalBudget universalConstant scale; ring

end Paper26.MultiscaleCollectiveCost
