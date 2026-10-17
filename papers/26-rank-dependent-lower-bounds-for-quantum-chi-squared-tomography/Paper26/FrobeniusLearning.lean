import Paper26.PureUpperBounds
import Paper26.Regularization

/-!
# Actual Frobenius-to-right-loss learner reduction

Isotropic regularization and the Markov step act on actual quantum learners.
The O'Donnell--Wright input below retains the original existence quantifier:
for every positive copy count, one learner works for every density matrix.
Its sole error bound is the original squared Frobenius expectation, not a
P26 chi-squared or submatrix conclusion.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.FrobeniusLearning
open QuantumModel CollectiveModel ContinuousPOVM
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

def regularizedDensity (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (ρ : Density ι) : Density ι where
  matrix := Regularization.regularize a ρ.matrix
  positive := (Regularization.regularize_posDef ρ.matrix ρ.positive ha ha1).posSemidef
  trace_one := Regularization.regularize_trace_one ρ.matrix ρ.positive ρ.trace_one a

theorem measurable_regularizedDensity (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    Measurable (regularizedDensity (ι := ι) a ha ha1) := by
  have hm : Measurable (fun ρ : Density ι =>
      ((regularizedDensity a ha ha1 ρ).matrix : ι → ι → ℂ)) := by
    apply measurable_pi_iff.2
    intro i
    apply measurable_pi_iff.2
    intro j
    change Measurable (fun ρ : Density ι => (((1 - a : ℝ) : ℂ)) * ρ.matrix i j +
      (((a / (Fintype.card ι : ℝ) : ℝ) : ℂ)) * (1 : Matrix ι ι ℂ) i j)
    exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      measurable_density_matrix)).const_mul _).add_const _
  intro S hS
  rcases hS with ⟨T, hT, rfl⟩
  exact hm hT

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

def regularizedLearner (A : Learner ι Ω n) (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    Learner ι Ω n where
  measurement := A.measurement
  estimator := ⟨fun y => regularizedDensity a ha ha1 (A.estimator.estimate y),
    (measurable_regularizedDensity a ha ha1).comp A.estimator.measurable_estimate⟩

def error (A : Learner ι Ω n) (ρ : Density ι) (y : Ω) : ℝ :=
  SpectralLoss.frobeniusSq (ρ.matrix - (A.estimator.estimate y).matrix)

omit [Nonempty ι] in
theorem error_nonneg (A : Learner ι Ω n) (ρ : Density ι) (y : Ω) : 0 ≤ error A ρ y := by
  unfold error SpectralLoss.frobeniusSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

omit [Nonempty ι] in
theorem measurable_error (A : Learner ι Ω n) (ρ : Density ι) : Measurable (error A ρ) := by
  unfold error SpectralLoss.frobeniusSq
  apply Finset.measurable_sum Finset.univ
  intro i _
  apply Finset.measurable_sum Finset.univ
  intro j _
  exact Complex.continuous_normSq.measurable.comp
    (measurable_const.sub ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp A.estimator.measurable_matrix)))

/-- The actual regularized chi-squared successful event contains the
Frobenius event, for every input state and arbitrary density estimate. -/
theorem error_implies_success (A : Learner ι Ω n) (ρ : Density ι)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (y : Ω)
    (hy : error A ρ y ≤ ε ^ 2 / (64 * (Fintype.card ι : ℝ))) :
    chiR ρ ((regularizedLearner A (ε / 8) (by positivity) (by linarith)).estimator.estimate y) ≤
      ENNReal.ofReal ε := by
  let σ := regularizedDensity (ε / 8) (by positivity) (by linarith : ε / 8 < 1)
    (A.estimator.estimate y)
  have hσ : σ.matrix.PosDef := Regularization.regularize_posDef _
    (A.estimator.estimate y).positive (by positivity) (by linarith)
  change chiR ρ σ ≤ _
  rw [PositiveLossBridge.chiR_eq_standardRightEnergy ρ σ hσ]
  exact ENNReal.ofReal_le_ofReal (Regularization.regularization_epsilon _ _ ρ.hermitian
    (A.estimator.estimate y).positive (A.estimator.estimate y).trace_one hε hε1 hy)

omit [Nonempty ι] in
/-- Native ENNReal Markov bound for one actual experiment. -/
theorem error_failure_le_quarter (A : Learner ι Ω n) (ρ : Density ι)
    {η : ℝ} (hη : 0 < η)
    (hm : (∫⁻ y, ENNReal.ofReal (error A ρ y) ∂A.outcomeMeasure ρ) ≤
      ENNReal.ofReal (η / 4)) :
    A.outcomeMeasure ρ {y | η < error A ρ y} ≤ (1 : ℝ≥0∞) / 4 := by
  have hpos : ENNReal.ofReal η ≠ 0 := (ENNReal.ofReal_pos.2 hη).ne'
  have hmark := meas_ge_le_lintegral_div (μ := A.outcomeMeasure ρ)
    (measurable_error A ρ).ennreal_ofReal.aemeasurable
    hpos ENNReal.ofReal_ne_top
  calc
    _ ≤ A.outcomeMeasure ρ {y | ENNReal.ofReal η ≤ ENNReal.ofReal (error A ρ y)} :=
      measure_mono (fun y hy => ENNReal.ofReal_le_ofReal (le_of_lt hy))
    _ ≤ (∫⁻ y, ENNReal.ofReal (error A ρ y) ∂A.outcomeMeasure ρ) / ENNReal.ofReal η := hmark
    _ ≤ ENNReal.ofReal (η / 4) / ENNReal.ofReal η := by gcongr
    _ = (1 : ℝ≥0∞) / 4 := by
      rw [← ENNReal.ofReal_div_of_pos hη]
      have he : η / 4 / η = (1 / 4 : ℝ) := by field_simp
      rw [he, ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num

/-- The external normalized collective Frobenius experiment. The bound
holds for all density inputs after the learner has been chosen. -/
structure OWFrobeniusExperiment (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) where
  Outcome : Type
  outcomeMeasurable : MeasurableSpace Outcome
  learner : @Learner ι Outcome _ _ outcomeMeasurable n
  expected_error : ∀ ρ : Density ι,
    (∫⁻ y, ENNReal.ofReal (SpectralLoss.frobeniusSq
      (ρ.matrix - (learner.estimator.estimate y).matrix)) ∂learner.outcomeMeasure ρ) ≤
        ENNReal.ofReal ((4 * (Fintype.card ι : ℝ) - 3) / (n : ℝ))

/-- O'Donnell--Wright 2016, Theorem 1.2, as a precise original uniform
existence input. No P26 loss, probability amplification or filtering occurs. -/
structure OWFrobeniusInput (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop where
  experiment : ∀ n : ℕ, 0 < n → Nonempty (OWFrobeniusExperiment ι n)

/-- A raw normalized Frobenius expectation yields the genuine `3/4`
right-inverse learning guarantee at `1024*d²/ε²` copies. -/
theorem right_success_of_expectation (A : Learner ι Ω n) (hN : 0 < n)
    (hOW : ∀ ρ : Density ι,
      (∫⁻ y, ENNReal.ofReal (error A ρ y) ∂A.outcomeMeasure ρ) ≤
        ENNReal.ofReal ((4 * (Fintype.card ι : ℝ) - 3) / (n : ℝ)))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcopies : 1024 * (Fintype.card ι : ℝ) ^ 2 / ε ^ 2 ≤ (n : ℝ)) :
    (regularizedLearner A (ε / 8) (by positivity) (by linarith)).LearnsRank chiR
      (Fintype.card ι) (ENNReal.ofReal ε) ((3 : ℝ≥0∞) / 4) := by
  let B := regularizedLearner A (ε / 8) (by positivity) (by linarith : ε / 8 < 1)
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 hN
  let η : ℝ := ε ^ 2 / (64 * (Fintype.card ι : ℝ))
  have hη : 0 < η := by dsimp [η]; positivity
  intro ρ _
  refine ⟨B.successSet_measurable chiR ρ (LossMeasurability.measurable_chiR_comp
    (fun _ : Density ι => ρ) id measurable_const measurable_id) _, ?_⟩
  have hmean : (∫⁻ y, ENNReal.ofReal (error A ρ y) ∂A.outcomeMeasure ρ) ≤
      ENNReal.ofReal (η / 4) := by
    apply (hOW ρ).trans (ENNReal.ofReal_le_ofReal ?_)
    apply (div_le_iff₀ hn).2
    have hc := (div_le_iff₀ (sq_pos_of_pos hε)).1 hcopies
    dsimp [η]
    have he : ε ^ 2 / (64 * (Fintype.card ι : ℝ)) / 4 * (n : ℝ) =
        ε ^ 2 * n / (256 * (Fintype.card ι : ℝ)) := by ring
    rw [he]
    apply (le_div_iff₀ (by positivity : 0 < 256 * (Fintype.card ι : ℝ))).2
    nlinarith
  have hbad := error_failure_le_quarter A ρ hη hmean
  have hs : MeasurableSet {y | η < error A ρ y} :=
    measurableSet_lt measurable_const (measurable_error A ρ)
  have hgood : (3 : ℝ≥0∞) / 4 ≤ A.outcomeMeasure ρ {y | error A ρ y ≤ η} := by
    have he : {y | error A ρ y ≤ η} = {y | η < error A ρ y}ᶜ := by ext y; simp
    rw [he, measure_compl hs (measure_ne_top _ _), measure_univ]
    have h := tsub_le_tsub_left hbad (1 : ℝ≥0∞)
    have hv : (1 : ℝ≥0∞) - 1 / 4 = 3 / 4 :=
      ENNReal.sub_eq_of_eq_add' (by norm_num)
        (by rw [ENNReal.div_add_div_same]; norm_num [ENNReal.div_self])
    rwa [hv] at h
  apply hgood.trans (measure_mono ?_)
  intro y hy
  exact error_implies_success A ρ hε hε1 y hy

/-- A chosen original OW experiment, before the unknown input is supplied. -/
def chooseExperiment (O : OWFrobeniusInput ι) (n : ℕ) (hn : 0 < n) :
    OWFrobeniusExperiment ι n := Classical.choice (O.experiment n hn)

/-- Applying the native reduction to the original existential OW theorem
produces an actual learner with a uniform right-loss guarantee. -/
theorem chosen_right_success (O : OWFrobeniusInput ι) (n : ℕ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcopies : 1024 * (Fintype.card ι : ℝ) ^ 2 / ε ^ 2 ≤ (n : ℝ)) :
    let D := chooseExperiment O n hn
    letI := D.outcomeMeasurable
    (regularizedLearner D.learner (ε / 8) (by positivity) (by linarith)).LearnsRank chiR
      (Fintype.card ι) (ENNReal.ofReal ε) ((3 : ℝ≥0∞) / 4) := by
  dsimp only
  let D := chooseExperiment O n hn
  letI := D.outcomeMeasurable
  exact right_success_of_expectation D.learner hn D.expected_error hε hε1 hcopies

end Paper26.FrobeniusLearning
