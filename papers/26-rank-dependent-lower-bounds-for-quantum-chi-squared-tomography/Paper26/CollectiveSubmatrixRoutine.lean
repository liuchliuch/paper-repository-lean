import Paper26.ContinuousSubmatrixLearning
import Paper26.MatrixAmplification

/-! Proposition 5.5: one prechosen physical continuous-outcome collective
experiment, including all rejected copies, independent-batch amplification,
the zero-copy branch and an explicit integer sample bound. -/
noncomputable section
open scoped BigOperators ENNReal ComplexOrder
open MeasureTheory

namespace Paper26.CollectiveSubmatrixRoutine
open QuantumModel ContinuousPOVM CollectiveModel CollectiveFiltering
open ContinuousSubmatrixLearning CollectiveSubmatrix ShellAccounting
variable {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype β] [DecidableEq β]
local instance matrixMeasurableSpace (m k : Type*) : MeasurableSpace (Matrix m k ℂ) :=
  inferInstanceAs (MeasurableSpace (m → k → ℂ))
local instance labelMeasurableSpace (N : ℕ) : MeasurableSpace (Finset (Fin N)) := ⊤

def baseCopies (W η : ℝ) : ℕ := ⌈360*(Fintype.card α : ℝ)*W/η⌉₊
def batches (b : ℝ) : ℕ := ⌈8*Real.log (1/b)⌉₊
def universalConstant : ℝ := 361*(8+1/Real.log 2)

theorem universalConstant_pos : 0 < universalConstant := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold universalConstant
  positivity

theorem baseCopies_pos {W η : ℝ} (hW : 0 < W) (hη : 0 < η) :
    0 < baseCopies (α := α) W η := by
  apply Nat.ceil_pos.mpr
  have hk : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  positivity

theorem batches_pos {b : ℝ} (hb : 0 < b) (hb1 : b < 1) : 0 < batches b := by
  apply Nat.ceil_pos.mpr
  have hinv : (1 : ℝ) < 1/b := (lt_div_iff₀ hb).mpr (by simpa using hb1)
  exact mul_pos (by norm_num) (Real.log_pos hinv)

theorem total_copies_bound {W η b : ℝ} (hW : 0 ≤ W) (hW1 : W ≤ 1)
    (hη : 0 < η) (hnontrivial : η < W^2) (hb : 0 < b) (hbhalf : b < 1/2) :
    ((baseCopies (α := α) W η * batches b : ℕ) : ℝ) ≤
      universalConstant*((Fintype.card α : ℝ)*W/η)*Real.log (1/b) := by
  have hk : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
  have hscale : 1 ≤ (Fintype.card α : ℝ)*W/η := by
    apply (le_div_iff₀ hη).mpr
    have hkw := mul_le_mul_of_nonneg_right hk hW
    nlinarith [mul_nonneg hW (sub_nonneg.mpr hW1)]
  have hn : (baseCopies (α := α) W η : ℝ) ≤ 361*((Fintype.card α : ℝ)*W/η) := by
    have h := (Nat.ceil_lt_add_one (show 0 ≤ 360*(Fintype.card α : ℝ)*W/η by positivity)).le
    change (baseCopies (α := α) W η : ℝ) ≤ 360*(Fintype.card α : ℝ)*W/η+1 at h
    calc
      _ ≤ _ := h
      _ = 360*((Fintype.card α : ℝ)*W/η)+1 := by ring
      _ ≤ _ := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have htwo : (2 : ℝ) ≤ 1/b := (le_div_iff₀ hb).mpr (by linarith)
  have hlog : Real.log 2 ≤ Real.log (1/b) := Real.log_le_log (by norm_num) htwo
  have hlog0 : 0 ≤ Real.log (1/b) := hlog2.le.trans hlog
  have hl : (batches b : ℝ) ≤ (8+1/Real.log 2)*Real.log (1/b) := by
    have h := (Nat.ceil_lt_add_one (show 0 ≤ 8*Real.log (1/b) by positivity)).le
    change (batches b : ℝ) ≤ 8*Real.log (1/b)+1 at h
    have ht : 1 ≤ Real.log (1/b)/Real.log 2 := (le_div_iff₀ hlog2).mpr (by simpa using hlog)
    apply h.trans
    simp only [div_eq_mul_inv] at ht ⊢
    nlinarith
  rw [Nat.cast_mul]
  calc
    _ ≤ (361*((Fintype.card α : ℝ)*W/η))*((8+1/Real.log 2)*Real.log (1/b)) :=
      mul_le_mul hn hl (Nat.cast_nonneg _) (by positivity)
    _ = _ := by unfold universalConstant; ring

theorem amplified_risk (O : FrobeniusLearning.OWFrobeniusInput α)
    {W η b : ℝ} (hW : 0 < W) (hη : 0 < η) (hb : 0 < b) (hb1 : b < 1) :
    let n := baseCopies (α := α) W η
    let l := batches b
    let D := chooseFamily O n
    let u := Real.sqrt η/3
    letI : NeZero l := ⟨(batches_pos hb hb1).ne'⟩
    ∀ ρ : Density (α ⊕ β), headMass ρ ≤ W →
      ENNReal.ofReal (1-b) ≤
        (MatrixAmplification.batchMeasurement (D.measurement (β := β)) ρ l).outcomeMeasure
          (TensorCopies.density ρ (n*l))
          {y | frobeniusSq (MatrixAmplification.selected D.output u y-headBlock ρ.matrix) ≤ η} := by
  dsimp only
  let n := baseCopies (α := α) W η
  let l := batches b
  let D := chooseFamily O n
  let u := Real.sqrt η/3
  letI : NeZero l := ⟨(batches_pos hb hb1).ne'⟩
  intro ρ hρ
  have hn : 0 < n := baseCopies_pos hW hη
  have hu : 0 < u := div_pos (Real.sqrt_pos.mpr hη) (by norm_num)
  have hm : (∫⁻ z, ENNReal.ofReal (frobeniusSq (D.output z-headBlock ρ.matrix))
      ∂(D.measurement (β := β)).outcomeMeasure (TensorCopies.density ρ n)) ≤ ENNReal.ofReal (u^2/4) := by
    apply (D.expected_error_all hn ρ).trans
    apply ENNReal.ofReal_le_ofReal
    have hk : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
    have hcost : 360*(Fintype.card α : ℝ)*W/η ≤ (n : ℝ) := Nat.le_ceil _
    have hc := (div_le_iff₀ hη).mp hcost
    have hs : u^2/4 = η/36 := by dsimp [u]; rw [div_pow, Real.sq_sqrt hη.le]; ring
    rw [hs]
    apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr
    have hw : 0 ≤ headMass ρ := headMass_nonneg ρ
    have he := mul_le_mul_of_nonneg_left hρ (show 0 ≤ 2*(4*(Fintype.card α : ℝ)+1) by positivity)
    have hmW := mul_le_mul_of_nonneg_right hk hW.le
    nlinarith
  have hl : 8*Real.log (1/b) ≤ (l : ℝ) := Nat.le_ceil _
  have hf := MatrixAmplification.amplified_failure (D.measurement (β := β)) ρ ρ
    D.output D.measurable_output (headBlock ρ.matrix) hu hb hl hm
  have ht : (3*u)^2 = η := by dsimp [u]; field_simp; exact Real.sq_sqrt hη.le
  rw [ht] at hf
  exact OneCopySubmatrix.success_lower_from_failure _ _ η b hb.le hf

/-- The zero-copy experiment is still a genuine POVM on the empty tensor
power, with a single observed outcome and the identity effect. -/
def zeroMeasurement : DominatedPOVM (Fin 0 → (α ⊕ β)) PUnit where
  reference := Measure.dirac PUnit.unit
  reference_finite := inferInstance
  effect _ := 1
  entry_measurable _ _ := measurable_const
  positive_ae := ae_of_all _ fun _ => Matrix.PosSemidef.one
  entry_integrable _ _ := integrable_const _
  total _ _ := by simp

/-- Complete uniform Proposition 5.5. The measurement and estimator are
chosen once before all states of allowed block mass. Outcome spaces are
arbitrary measurable continuous spaces supplied by the actual OW experiment. -/
theorem proposition_5_5 (O : FrobeniusLearning.OWFrobeniusInput α)
    {W η b : ℝ} (hW : 0 ≤ W) (hW1 : W ≤ 1) (hη : 0 < η)
    (hb : 0 < b) (hbhalf : b < 1/2) :
    ∃ (N : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω),
      letI := mΩ
      ∃ (M : DominatedPOVM (Fin N → (α ⊕ β)) Ω) (T : Ω → Matrix α α ℂ),
        Measurable T ∧ (∀ y, (T y).PosSemidef) ∧
        (∀ ρ : Density (α ⊕ β), headMass ρ ≤ W →
          MeasurableSet {y | frobeniusSq (T y-headBlock ρ.matrix) ≤ η} ∧
          ENNReal.ofReal (1-b) ≤ M.outcomeMeasure (TensorCopies.density ρ N)
            {y | frobeniusSq (T y-headBlock ρ.matrix) ≤ η}) ∧
        (if W^2 ≤ η then N=0 else (N : ℝ) ≤
          universalConstant*((Fintype.card α : ℝ)*W/η)*Real.log (1/b)) := by
  by_cases hz : W^2 ≤ η
  · refine ⟨0, PUnit, inferInstance, zeroMeasurement, (fun _ => 0), measurable_const,
      (fun _ => Matrix.PosSemidef.zero), ?_, by simp only [hz, ↓reduceIte]⟩
    intro ρ hρ
    have he := zero_estimate_suffices (headBlock ρ.matrix) (headBlock_posSemidef ρ)
      (headMass ρ) W η rfl (headMass_nonneg ρ) hρ hz |>.2
    have hu : {y : PUnit | frobeniusSq (0-headBlock ρ.matrix) ≤ η} = Set.univ := by
      ext y
      simpa only [Set.mem_setOf_eq, Set.mem_univ, iff_true] using he
    rw [hu]
    exact ⟨MeasurableSet.univ, by
      rw [measure_univ]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show 1-b ≤ 1 by linarith)⟩
  · have hnon : η < W^2 := lt_of_not_ge hz
    have hWp : 0 < W := lt_of_le_of_ne hW (by intro h; rw [← h] at hnon; nlinarith)
    let n := baseCopies (α := α) W η
    let l := batches b
    letI : NeZero l := ⟨(batches_pos hb (by linarith)).ne'⟩
    let D := chooseFamily O n
    let u := Real.sqrt η/3
    let σ₀ := AdaptiveCollectiveEmbedding.uniformState (α ⊕ β)
    refine ⟨n*l, Fin l → (Finset (Fin n) × (∀ S, D.Outcome S)), inferInstance,
      MatrixAmplification.batchMeasurement (D.measurement (β := β)) σ₀ l,
      MatrixAmplification.selected D.output u,
      MatrixAmplification.measurable_selected _ D.measurable_output _,
      (fun y => MatrixAmplification.selected_property _ _ _ D.output_posSemidef y), ?_, ?_⟩
    · intro ρ hρ
      refine ⟨measurableSet_le (MatrixAmplification.measurable_error _
        (MatrixAmplification.measurable_selected _ D.measurable_output _) _) measurable_const, ?_⟩
      have hs := amplified_risk (β := β) O hWp hη hb (by linarith) ρ hρ
      exact hs
    · simp only [hz, ↓reduceIte]
      exact total_copies_bound hW hW1 hη hnon hb hbhalf

end Paper26.CollectiveSubmatrixRoutine
