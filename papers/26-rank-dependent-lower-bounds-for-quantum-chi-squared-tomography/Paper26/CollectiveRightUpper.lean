import Paper26.FrobeniusAmplification
import Mathlib.Algebra.Order.Floor.Ring

/-! Equation (11): the original uniform normalized Frobenius estimator,
actual independent quantum batches, measurable Frobenius center selection,
and actual isotropic regularization. All amplification acts on `n*l` copies. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.CollectiveRightUpper
open QuantumModel CollectiveModel ContinuousPOVM FrobeniusLearning FrobeniusAmplification
variable {d n l : ℕ} [NeZero d] [NeZero l] {Ω : Type*} [MeasurableSpace Ω]

def radius (d : ℕ) (ε : ℝ) : ℝ := ε / (24 * Real.sqrt (d : ℝ))

theorem radius_pos {ε : ℝ} (hε : 0 < ε) : 0 < radius d ε := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 (NeZero.pos d)
  unfold radius
  exact div_pos hε (by positivity)

omit [NeZero d] in
theorem radius_square (ε : ℝ) : radius d ε ^ 2 = ε ^ 2 / (576 * (d : ℝ)) := by
  unfold radius
  rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  norm_num

/-- The selected batch remains a density, then isotropic regularization
converts the amplified Frobenius accuracy to actual right-inverse loss. -/
def learner (A : Learner (Fin d) Ω n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Learner (Fin d) (Fin l → Ω) (n * l) :=
  regularizedLearner (amplifiedLearner (l := l) A (radius d ε)) (ε / 8)
    (by positivity) (by linarith)

/-- Exact finite-copy/high-confidence statement underlying Equation (11). -/
theorem learns (A : Learner (Fin d) Ω n) (hn : 0 < n)
    (hOW : ∀ ρ : Density (Fin d),
      (∫⁻ y, ENNReal.ofReal (error A ρ y) ∂A.outcomeMeasure ρ) ≤
        ENNReal.ofReal ((4 * (d : ℝ) - 3) / (n : ℝ)))
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hcopies : 9216 * (d : ℝ) ^ 2 / ε ^ 2 ≤ (n : ℝ))
    (hl : 8 * Real.log (1 / δ) ≤ (l : ℝ)) :
    (learner (l := l) A ε hε hε1).LearnsRank chiR d (ENNReal.ofReal ε)
      (1 - ENNReal.ofReal δ) := by
  let u := radius d ε
  let B := amplifiedLearner (l := l) A u
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 (NeZero.pos d)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hu : 0 < u := radius_pos hε
  have hu2 : u ^ 2 = ε ^ 2 / (576 * (d : ℝ)) := radius_square ε
  have hη : (3 * u) ^ 2 = ε ^ 2 / (64 * (d : ℝ)) := by rw [mul_pow, hu2]; ring
  intro ρ _
  let C := learner (l := l) A ε hε hε1
  refine ⟨C.successSet_measurable chiR ρ (LossMeasurability.measurable_chiR_comp
    (fun _ : Density (Fin d) => ρ) id measurable_const measurable_id) _, ?_⟩
  have hmean : (∫⁻ y, ENNReal.ofReal (error A ρ y) ∂A.outcomeMeasure ρ) ≤
      ENNReal.ofReal (u ^ 2 / 4) := by
    apply (hOW ρ).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hu2]
    apply (div_le_iff₀ hnR).2
    have hc := (div_le_iff₀ (sq_pos_of_pos hε)).1 hcopies
    have he : ε ^ 2 / (576 * (d : ℝ)) / 4 * (n : ℝ) =
        ε ^ 2 * n / (2304 * (d : ℝ)) := by ring
    rw [he]
    apply (le_div_iff₀ (by positivity : 0 < 2304 * (d : ℝ))).2
    nlinarith
  have hbad : B.outcomeMeasure ρ {y | (3 * u) ^ 2 < error B ρ y} ≤ ENNReal.ofReal δ :=
    failure_probability A ρ hu hδ hl hmean
  have hs : MeasurableSet {y | (3 * u) ^ 2 < error B ρ y} :=
    measurableSet_lt measurable_const (measurable_error B ρ)
  have hgood : 1 - ENNReal.ofReal δ ≤ B.outcomeMeasure ρ {y | error B ρ y ≤ (3 * u) ^ 2} := by
    have he : {y | error B ρ y ≤ (3 * u) ^ 2} =
        {y | (3 * u) ^ 2 < error B ρ y}ᶜ := by ext y; simp
    rw [he, measure_compl hs (measure_ne_top _ _), measure_univ]
    exact tsub_le_tsub_left hbad 1
  change 1 - ENNReal.ofReal δ ≤ B.outcomeMeasure ρ (C.successSet chiR ρ (ENNReal.ofReal ε))
  apply hgood.trans (measure_mono ?_)
  intro y hy
  apply error_implies_success B ρ hε hε1 y
  simpa only [Fintype.card_fin, ← hη] using hy

/-- The original existential OW result supplies the same learner before
any unknown density is chosen, so the high-confidence guarantee is uniform. -/
theorem chosen_learns (O : OWFrobeniusInput (Fin d)) (n : ℕ) (hn : 0 < n)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hcopies : 9216 * (d : ℝ) ^ 2 / ε ^ 2 ≤ (n : ℝ))
    (hl : 8 * Real.log (1 / δ) ≤ (l : ℝ)) :
    let D := chooseExperiment O n hn
    letI := D.outcomeMeasurable
    (learner (l := l) D.learner ε hε hε1).LearnsRank chiR d (ENNReal.ofReal ε)
      (1 - ENNReal.ofReal δ) := by
  dsimp only
  let D := chooseExperiment O n hn
  letI := D.outcomeMeasurable
  apply learns D.learner hn (fun ρ => ?_) hε hε1 hδ hcopies hl
  simpa only [error, Fintype.card_fin] using D.expected_error ρ

end Paper26.CollectiveRightUpper
