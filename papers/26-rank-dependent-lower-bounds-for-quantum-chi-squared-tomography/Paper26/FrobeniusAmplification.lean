import Paper26.FrobeniusLearning
import Paper26.ProductCollectiveMeasurement
import Paper26.IndependentAmplification
import Paper26.MatrixCoordinates

/-! Actual Frobenius amplification on `n*l` quantum copies. Metric selection
is made in the proved real Euclidean matrix coordinates, so the metric is
exactly Frobenius distance, and the selected output remains an actual density. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

namespace Paper26.FrobeniusAmplification
open QuantumModel CollectiveModel ContinuousPOVM ProductCollectiveMeasurement
  FrobeniusLearning MetricAmplification
variable {d n l : ℕ} {Ω : Type*} [MeasurableSpace Ω]
local instance matrixMeasurableSpace (m k : Type*) : MeasurableSpace (Matrix m k ℂ) :=
  inferInstanceAs (MeasurableSpace (m → k → ℂ))
local instance matrixBorelSpace (m k : Type*) [Fintype m] [Fintype k] :
    BorelSpace (Matrix m k ℂ) := inferInstanceAs (BorelSpace (m → k → ℂ))

abbrev Coordinates (d : ℕ) := EuclideanSpace ℝ (Fin (2 * d * d))

def coordinates (ρ : Density (Fin d)) : Coordinates d := MatrixCoordinates.coordinates d d ρ.matrix

theorem measurable_coordinates : Measurable (coordinates (d := d)) :=
  (MatrixCoordinates.coordinates d d).continuous.measurable.comp measurable_density_matrix

theorem distance_sq (ρ σ : Density (Fin d)) :
    dist (coordinates ρ) (coordinates σ) ^ 2 = SpectralLoss.frobeniusSq (ρ.matrix - σ.matrix) := by
  rw [dist_eq_norm]
  unfold coordinates
  rw [← map_sub, ← MatrixCoordinates.frobeniusSq_eq_norm_sq]
  exact (Regularization.frobeniusSq_eq_entryNorm _).symm

def batchCoordinates (A : Learner (Fin d) Ω n) (y : Fin l → Ω) : Fin l → Coordinates d :=
  fun j => coordinates (A.estimator.estimate (y j))

theorem measurable_batchCoordinates (A : Learner (Fin d) Ω n) :
    Measurable (batchCoordinates (l := l) A) := by
  exact measurable_pi_lambda _ fun j =>
    measurable_coordinates.comp (A.estimator.measurable_estimate.comp (measurable_pi_apply j))

theorem measurable_selectedIndex [NeZero l] (u : ℝ) :
    Measurable (fun X : Fin l → Coordinates d => MetricAmplification.selectedIndex X u) := by
  have hn := measurable_find (fun X : Fin l → Coordinates d => search_exists X u)
    (fun k => measurableSet_search u k)
  have hf : Measurable (fun k : ℕ => Fin.ofNat l k) := measurable_of_countable _
  exact hf.comp hn

def selection [NeZero l] (A : Learner (Fin d) Ω n) (u : ℝ) (y : Fin l → Ω) : Fin l :=
  MetricAmplification.selectedIndex (batchCoordinates A y) u

theorem measurable_selection [NeZero l] (A : Learner (Fin d) Ω n) (u : ℝ) :
    Measurable (selection (l := l) A u) :=
  (measurable_selectedIndex u).comp (measurable_batchCoordinates A)

def amplifiedLearner [NeZero l] (A : Learner (Fin d) Ω n) (u : ℝ) :
    Learner (Fin d) (Fin l → Ω) (n * l) :=
  selectedLearner A l (selection A u) (measurable_selection A u)

/-- The actual selected matrix's error is exactly the distance used by the
metric rule; no norm on the matrix function type is confused with Frobenius. -/
theorem selected_distance [NeZero l] (A : Learner (Fin d) Ω n) (u : ℝ)
    (y : Fin l → Ω) (ρ : Density (Fin d)) :
    dist (MetricAmplification.select (batchCoordinates A y) u) (coordinates ρ) ^ 2 =
      error (amplifiedLearner (l := l) A u) ρ y := by
  rw [MetricAmplification.select]
  change dist (coordinates (A.estimator.estimate (y (selection A u y)))) (coordinates ρ) ^ 2 = _
  rw [dist_comm, distance_sq]
  rfl

/-- Repeating an actual learner, with the native metric selector, reduces
its Frobenius failure under the true `n*l`-copy Born law to beta. -/
theorem failure_probability [NeZero l] (A : Learner (Fin d) Ω n)
    (ρ : Density (Fin d)) {u β : ℝ} (hu : 0 < u) (hβ : 0 < β)
    (hl : 8 * Real.log (1 / β) ≤ (l : ℝ))
    (hmean : (∫⁻ y, ENNReal.ofReal (error A ρ y) ∂A.outcomeMeasure ρ) ≤
      ENNReal.ofReal (u ^ 2 / 4)) :
    (amplifiedLearner (l := l) A u).outcomeMeasure ρ
      {y | (3 * u) ^ 2 < error (amplifiedLearner (l := l) A u) ρ y} ≤ ENNReal.ofReal β := by
  let ν := Measure.pi (fun _ : Fin l => A.outcomeMeasure ρ)
  let X : Fin l → (Fin l → Ω) → Coordinates d := fun j y => coordinates (A.estimator.estimate (y j))
  have hX (j : Fin l) : Measurable (X j) :=
    measurable_coordinates.comp (A.estimator.measurable_estimate.comp (measurable_pi_apply j))
  have hind : iIndepFun X ν := iIndepFun_pi (fun _ =>
    (measurable_coordinates.comp A.estimator.measurable_estimate).aemeasurable)
  have hsingle := error_failure_le_quarter A ρ (sq_pos_of_pos hu) hmean
  have hbatch (j : Fin l) : ν.real {y | u < dist (X j y) (coordinates ρ)} ≤ 1 / 4 := by
    let S : Set Ω := {y | u < dist (coordinates (A.estimator.estimate y)) (coordinates ρ)}
    have hs : MeasurableSet S := measurableSet_lt measurable_const
      ((measurable_coordinates.comp A.estimator.measurable_estimate).dist measurable_const)
    have he : ν (Function.eval j ⁻¹' S) = A.outcomeMeasure ρ S :=
      (measurePreserving_eval (fun _ : Fin l => A.outcomeMeasure ρ) j).measure_preimage hs.nullMeasurableSet
    have hsub : S ⊆ {y | u ^ 2 < error A ρ y} := by
      intro y hy
      have ht := mul_self_lt_mul_self hu.le (show u < dist (coordinates (A.estimator.estimate y))
        (coordinates ρ) from hy)
      simpa only [← pow_two, dist_comm, distance_sq, error] using ht
    have hb : ν {y | u < dist (X j y) (coordinates ρ)} ≤ (1 : ℝ≥0∞) / 4 := by
      change ν (Function.eval j ⁻¹' S) ≤ _
      rw [he]
      exact (measure_mono hsub).trans hsingle
    have h := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) / 4 ≠ ∞) hb
    simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using h
  have hf := IndependentAmplification.failure_probability_le_beta X hX hind (coordinates ρ) u β
    hbatch hβ hl
  have hbad : ν {y | 3 * u < dist (MetricAmplification.select (batchCoordinates A y) u)
      (coordinates ρ)} ≤ ENNReal.ofReal β := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hβ.le]
    exact hf
  rw [show (amplifiedLearner (l := l) A u).outcomeMeasure ρ = ν from
    selectedLearner_outcomeMeasure A l _ _ ρ]
  apply (measure_mono ?_).trans hbad
  intro y hy
  have he := selected_distance A u y ρ
  have h0 := dist_nonneg (x := MetricAmplification.select (batchCoordinates A y) u) (y := coordinates ρ)
  have hu0 : 0 ≤ 3 * u := by positivity
  dsimp only [Set.mem_setOf_eq] at hy ⊢
  rw [← he] at hy
  nlinarith

end Paper26.FrobeniusAmplification
