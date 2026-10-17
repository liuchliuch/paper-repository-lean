import Paper26.FrobeniusAmplification
import Paper26.OneCopySubmatrix

/-! Actual quantum independent-batch amplification for subnormalized matrix
outputs. Selection uses the genuine Frobenius metric and retains an original
output, so every pointwise PSD or rank constraint is preserved. -/
noncomputable section
open scoped BigOperators ENNReal ComplexOrder
open MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

namespace Paper26.MatrixAmplification
open QuantumModel ContinuousPOVM CollectiveModel ProductCollectiveMeasurement MetricAmplification
variable {δ κ Ω : Type*} [Fintype δ] [DecidableEq δ] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {n l : ℕ}
local instance matrixMeasurableSpace (m k : Type*) : MeasurableSpace (Matrix m k ℂ) :=
  inferInstanceAs (MeasurableSpace (m → k → ℂ))
local instance matrixBorelSpace (m k : Type*) [Fintype m] [Fintype k] :
    BorelSpace (Matrix m k ℂ) := inferInstanceAs (BorelSpace (m → k → ℂ))

def reindex (A : Matrix κ κ ℂ) : Matrix (Fin (Fintype.card κ)) (Fin (Fintype.card κ)) ℂ :=
  A.submatrix (Fintype.equivFin κ).symm (Fintype.equivFin κ).symm

def coordinates (A : Matrix κ κ ℂ) : FrobeniusAmplification.Coordinates (Fintype.card κ) :=
  MatrixCoordinates.coordinates _ _ (reindex A)

theorem reindex_frobenius (A : Matrix κ κ ℂ) :
    ShellAccounting.frobeniusSq (reindex A) = ShellAccounting.frobeniusSq A := by
  unfold ShellAccounting.frobeniusSq reindex
  simp only [Matrix.submatrix_apply]
  rw [← (Fintype.equivFin κ).symm.sum_comp (fun i => ∑ j : κ, ‖A i j‖^2)]
  apply Finset.sum_congr rfl
  intro i _
  exact (Fintype.equivFin κ).symm.sum_comp (fun j => ‖A ((Fintype.equivFin κ).symm i) j‖^2)

theorem distance_sq (A B : Matrix κ κ ℂ) :
    dist (coordinates A) (coordinates B)^2 = ShellAccounting.frobeniusSq (A-B) := by
  rw [dist_eq_norm]
  unfold coordinates
  rw [← map_sub, ← MatrixCoordinates.frobeniusSq_eq_norm_sq]
  exact reindex_frobenius (A-B)

theorem measurable_coordinates : Measurable (coordinates (κ := κ)) := by
  apply (MatrixCoordinates.coordinates _ _).continuous.measurable.comp
  change Measurable (fun A : Matrix κ κ ℂ => fun i : Fin (Fintype.card κ) =>
    fun j : Fin (Fintype.card κ) => A ((Fintype.equivFin κ).symm i) ((Fintype.equivFin κ).symm j))
  exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

theorem measurable_error (T : Ω → Matrix κ κ ℂ) (hT : Measurable T) (R : Matrix κ κ ℂ) :
    Measurable (fun y => ShellAccounting.frobeniusSq (T y-R)) := by
  have hm := ((measurable_coordinates.comp hT).dist
    (measurable_const (a := coordinates R))).pow_const 2
  simpa only [Function.comp_apply, distance_sq] using hm

def dummyLearner (M : DominatedPOVM (Fin n → δ) Ω) (σ₀ : Density δ) : Learner δ Ω n :=
  ⟨M, ⟨fun _ => σ₀, measurable_const⟩⟩

def batchMeasurement (M : DominatedPOVM (Fin n → δ) Ω) (σ₀ : Density δ) (l : ℕ) :
    DominatedPOVM (Fin (n*l) → δ) (Fin l → Ω) := batchedMeasurement (dummyLearner M σ₀) l

theorem batch_outcomeMeasure (M : DominatedPOVM (Fin n → δ) Ω) (σ₀ : Density δ)
    (l : ℕ) (ρ : Density δ) :
    (batchMeasurement M σ₀ l).outcomeMeasure (TensorCopies.density ρ (n*l)) =
      Measure.pi (fun _ : Fin l => M.outcomeMeasure (TensorCopies.density ρ n)) :=
  batched_outcomeMeasure (dummyLearner M σ₀) l ρ

def batchCoordinates (T : Ω → Matrix κ κ ℂ) (y : Fin l → Ω) :
    Fin l → FrobeniusAmplification.Coordinates (Fintype.card κ) := fun j => coordinates (T (y j))

def selectedIndex [NeZero l] (T : Ω → Matrix κ κ ℂ) (u : ℝ) (y : Fin l → Ω) : Fin l :=
  MetricAmplification.selectedIndex (batchCoordinates T y) u

theorem measurable_selectedIndex [NeZero l] (T : Ω → Matrix κ κ ℂ) (hT : Measurable T) (u : ℝ) :
    Measurable (selectedIndex (l := l) T u) := by
  apply (FrobeniusAmplification.measurable_selectedIndex u).comp
  exact measurable_pi_lambda _ fun j => measurable_coordinates.comp (hT.comp (measurable_pi_apply j))

def selected [NeZero l] (T : Ω → Matrix κ κ ℂ) (u : ℝ) (y : Fin l → Ω) : Matrix κ κ ℂ :=
  T (y (selectedIndex T u y))

theorem measurable_selected [NeZero l] (T : Ω → Matrix κ κ ℂ) (hT : Measurable T) (u : ℝ) :
    Measurable (selected (l := l) T u) :=
  hT.comp (ProductCollectiveMeasurement.measurable_selected l _ (measurable_selectedIndex T hT u))

theorem selected_property [NeZero l] (T : Ω → Matrix κ κ ℂ) (u : ℝ)
    (P : Matrix κ κ ℂ → Prop) (hP : ∀ y, P (T y)) (y : Fin l → Ω) :
    P (selected T u y) := hP _

theorem selected_distance [NeZero l] (T : Ω → Matrix κ κ ℂ) (u : ℝ)
    (y : Fin l → Ω) (R : Matrix κ κ ℂ) :
    dist (MetricAmplification.select (batchCoordinates T y) u) (coordinates R)^2 =
      ShellAccounting.frobeniusSq (selected T u y-R) := distance_sq _ _

theorem one_batch_failure (ν : Measure Ω) [IsProbabilityMeasure ν]
    (T : Ω → Matrix κ κ ℂ) (hT : Measurable T) (R : Matrix κ κ ℂ)
    {u : ℝ} (hu : 0 < u)
    (hm : (∫⁻ y, ENNReal.ofReal (ShellAccounting.frobeniusSq (T y-R)) ∂ν) ≤ ENNReal.ofReal (u^2/4)) :
    ν {y | u^2 < ShellAccounting.frobeniusSq (T y-R)} ≤ (1 : ℝ≥0∞)/4 := by
  have hpos := sq_pos_of_pos hu
  have hp : ENNReal.ofReal (u^2) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
  calc
    _ ≤ ν {y | ENNReal.ofReal (u^2) ≤ ENNReal.ofReal (ShellAccounting.frobeniusSq (T y-R))} :=
      measure_mono (fun y hy => ENNReal.ofReal_le_ofReal hy.le)
    _ ≤ (∫⁻ y, ENNReal.ofReal (ShellAccounting.frobeniusSq (T y-R)) ∂ν)/ENNReal.ofReal (u^2) :=
      meas_ge_le_lintegral_div (measurable_error T hT R).ennreal_ofReal.aemeasurable
        hp ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (u^2/4)/ENNReal.ofReal (u^2) := by gcongr
    _ = (1 : ℝ≥0∞)/4 := by
      rw [← ENNReal.ofReal_div_of_pos hpos]
      have he : u^2/4/u^2 = (1/4 : ℝ) := by field_simp
      rw [he, ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num

/-- The actual amplified full-copy quantum outcome law, with no IID or
concentration conclusion assumed. Infinite raw errors are handled by ENNReal. -/
theorem amplified_failure [NeZero l] (M : DominatedPOVM (Fin n → δ) Ω) (σ₀ ρ : Density δ)
    (T : Ω → Matrix κ κ ℂ) (hT : Measurable T) (R : Matrix κ κ ℂ)
    {u β : ℝ} (hu : 0 < u) (hβ : 0 < β) (hl : 8*Real.log (1/β) ≤ (l : ℝ))
    (hm : (∫⁻ y, ENNReal.ofReal (ShellAccounting.frobeniusSq (T y-R))
      ∂M.outcomeMeasure (TensorCopies.density ρ n)) ≤ ENNReal.ofReal (u^2/4)) :
    (batchMeasurement M σ₀ l).outcomeMeasure (TensorCopies.density ρ (n*l))
      {y | (3*u)^2 < ShellAccounting.frobeniusSq (selected T u y-R)} ≤ ENNReal.ofReal β := by
  let ν := Measure.pi (fun _ : Fin l => M.outcomeMeasure (TensorCopies.density ρ n))
  let X : Fin l → (Fin l → Ω) → FrobeniusAmplification.Coordinates (Fintype.card κ) :=
    fun j y => coordinates (T (y j))
  have hX (j : Fin l) : Measurable (X j) := measurable_coordinates.comp (hT.comp (measurable_pi_apply j))
  have hind : iIndepFun X ν := iIndepFun_pi (fun _ => (measurable_coordinates.comp hT).aemeasurable)
  have hsingle := one_batch_failure _ T hT R hu hm
  have hbatch (j : Fin l) : ν.real {y | u < dist (X j y) (coordinates R)} ≤ 1/4 := by
    let S : Set Ω := {y | u < dist (coordinates (T y)) (coordinates R)}
    have hs : MeasurableSet S := measurableSet_lt measurable_const
      ((measurable_coordinates.comp hT).dist measurable_const)
    have he : ν (Function.eval j ⁻¹' S) = M.outcomeMeasure (TensorCopies.density ρ n) S :=
      (measurePreserving_eval (fun _ : Fin l => M.outcomeMeasure (TensorCopies.density ρ n)) j).measure_preimage hs.nullMeasurableSet
    have hsub : S ⊆ {y | u^2 < ShellAccounting.frobeniusSq (T y-R)} := by
      intro y hy
      have ht := mul_self_lt_mul_self hu.le (show u < dist (coordinates (T y)) (coordinates R) from hy)
      simpa only [← pow_two, distance_sq] using ht
    have hb : ν {y | u < dist (X j y) (coordinates R)} ≤ (1 : ℝ≥0∞)/4 := by
      change ν (Function.eval j ⁻¹' S) ≤ _
      rw [he]
      exact (measure_mono hsub).trans hsingle
    have h := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞)/4 ≠ ∞) hb
    simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using h
  have hf := IndependentAmplification.failure_probability_le_beta X hX hind (coordinates R) u β hbatch hβ hl
  have hbad : ν {y | 3*u < dist (MetricAmplification.select (batchCoordinates T y) u) (coordinates R)} ≤
      ENNReal.ofReal β := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hβ.le]
    exact hf
  rw [batch_outcomeMeasure]
  apply (measure_mono ?_).trans hbad
  intro y hy
  have he := selected_distance T u y R
  dsimp only [Set.mem_setOf_eq] at hy ⊢
  rw [← he] at hy
  nlinarith [dist_nonneg (x := MetricAmplification.select (batchCoordinates T y) u)
    (y := coordinates R), show 0 ≤ 3*u by positivity]

end Paper26.MatrixAmplification
