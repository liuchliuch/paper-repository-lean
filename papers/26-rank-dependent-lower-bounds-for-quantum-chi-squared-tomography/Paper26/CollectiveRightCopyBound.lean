import Paper26.CollectiveRightUpper

/-! Exact integer copy accounting for Equation (11). The two ceilings are
absorbed into one explicit universal constant times d²/ε² log(1/δ). -/
noncomputable section
open scoped ENNReal
open MeasureTheory

namespace Paper26.CollectiveRightCopyBound
open QuantumModel CollectiveModel FrobeniusLearning
variable {d : ℕ} [NeZero d]

def baseCopies (d : ℕ) (ε : ℝ) : ℕ := ⌈9216 * (d : ℝ) ^ 2 / ε ^ 2⌉₊
def batches (δ : ℝ) : ℕ := ⌈8 * Real.log (1 / δ)⌉₊
def universalConstant : ℝ := 9217 * (8 + 1 / Real.log 2)

theorem universalConstant_pos : 0 < universalConstant := by
  unfold universalConstant
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem baseCopies_pos {ε : ℝ} (hε : 0 < ε) : 0 < baseCopies d ε := by
  apply Nat.ceil_pos.2
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 (NeZero.pos d)
  positivity

theorem batches_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : 0 < batches δ := by
  apply Nat.ceil_pos.2
  have hinv : (1 : ℝ) < 1 / δ := (lt_div_iff₀ hδ).2 (by simpa using hδ1)
  exact mul_pos (by norm_num) (Real.log_pos hinv)

/-- Integer rounding costs only a universal factor on the source's full
range `d≥1`, `ε≤1`, `δ<1/2`. -/
theorem total_copies_bound {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ((baseCopies d ε * batches δ : ℕ) : ℝ) ≤
      universalConstant * ((d : ℝ) ^ 2 / ε ^ 2) * Real.log (1 / δ) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have htwo : (2 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).2 (by linarith)
  have hlog : Real.log 2 ≤ Real.log (1 / δ) := Real.log_le_log (by norm_num) htwo
  have hlog0 : 0 ≤ Real.log (1 / δ) := hlog2.le.trans hlog
  have hscale : (1 : ℝ) ≤ (d : ℝ) ^ 2 / ε ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).2
    nlinarith
  have hn : (baseCopies d ε : ℝ) ≤ 9217 * ((d : ℝ) ^ 2 / ε ^ 2) := by
    have h := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 9216 * (d : ℝ) ^ 2 / ε ^ 2 by positivity)).le
    change (baseCopies d ε : ℝ) ≤ 9216 * (d : ℝ) ^ 2 / ε ^ 2 + 1 at h
    calc
      _ ≤ 9216 * (d : ℝ) ^ 2 / ε ^ 2 + 1 := h
      _ = 9216 * ((d : ℝ) ^ 2 / ε ^ 2) + 1 := by ring
      _ ≤ _ := by linarith
  have hl : (batches δ : ℝ) ≤ (8 + 1 / Real.log 2) * Real.log (1 / δ) := by
    have h := (Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hlog0)).le
    change (batches δ : ℝ) ≤ 8 * Real.log (1 / δ) + 1 at h
    have hr : 1 ≤ Real.log (1 / δ) / Real.log 2 := (le_div_iff₀ hlog2).2 (by simpa using hlog)
    apply h.trans
    simp only [div_eq_mul_inv] at hr ⊢
    nlinarith
  rw [Nat.cast_mul]
  calc
    _ ≤ (9217 * ((d : ℝ) ^ 2 / ε ^ 2)) *
        ((8 + 1 / Real.log 2) * Real.log (1 / δ)) :=
      mul_le_mul hn hl (Nat.cast_nonneg _) (by positivity)
    _ = _ := by unfold universalConstant; ring

/-- A concrete actual learner attains Equation (11), with an explicit
universal constant and the consumed-copy count including all batches. -/
theorem equation_11 (O : OWFrobeniusInput (Fin d))
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ (N : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω),
      (N : ℝ) ≤ universalConstant * ((d : ℝ) ^ 2 / ε ^ 2) * Real.log (1 / δ) ∧
      (letI := mΩ
       ∃ A : Learner (Fin d) Ω N,
         A.LearnsRank chiR d (ENNReal.ofReal ε) (1 - ENNReal.ofReal δ)) := by
  let n := baseCopies d ε
  let l := batches δ
  have hn : 0 < n := baseCopies_pos hε
  have hl : 0 < l := batches_pos hδ (by linarith)
  letI : NeZero l := ⟨hl.ne'⟩
  let D := chooseExperiment O n hn
  letI := D.outcomeMeasurable
  refine ⟨n * l, Fin l → D.Outcome, inferInstance, total_copies_bound hε hε1 hδ hδhalf, ?_⟩
  refine ⟨CollectiveRightUpper.learner (l := l) D.learner ε hε hε1, ?_⟩
  apply CollectiveRightUpper.chosen_learns O n hn hε hε1 hδ
  · exact Nat.le_ceil _
  · exact Nat.le_ceil _

end Paper26.CollectiveRightCopyBound
