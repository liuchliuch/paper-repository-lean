import CalibrationDistance.ProtocolLoss
import CalibrationDistance.ProtocolStep
import CalibrationDistance.Deterministic

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory ENNReal

namespace CalibrationDistance.Protocol

noncomputable section

def constantAdversary (b : Bool) : Adversary where
  action _ _ := b
  measurable_action _ := measurable_const

/-- The one-round trajectory law retains exactly the forecaster's private randomization. -/
theorem one_round_law (K : BehavioralForecaster) (A : Adversary) :
    law K A.randomized 1 = (K.kernel 0 ()).map
      (fun p : Probability => ((), (p, A.action 0 ()))) := by
  haveI : IsMarkovKernel (transition K A.randomized 0) := transition_markov K A.randomized 0
  change (Measure.dirac ()).compProd (transition K A.randomized 0) = _
  rw [Measure.dirac_unit_compProd (transition K A.randomized 0)]
  calc
    _ = ((K.kernel 0 ()).prod (Measure.dirac (A.action 0 ()))).map (Prod.mk ()) :=
      congrArg (fun μ : Measure Round => μ.map (Prod.mk ()))
        (deterministic_transition_apply K A 0 ())
    _ = _ := by
      rw [Measure.prod_dirac, Measure.map_map measurable_prodMk_left measurable_prodMk_right]
      rfl

theorem roundAt_one (h : History 1) (i : Fin 1) : roundAt 1 h i = h.2 := by
  have hi : i = Fin.last 0 := Subsingleton.elim _ _
  rw [hi]
  simp only [roundAt, Fin.lastCases_last]

theorem one_round_pathLoss (p : Probability) (b : Bool) :
    pathLoss 1 ((),(p,b)) = |(p:ℝ)-boolValue b| := by
  rw [pathLoss, calDist_one _ _ (outcomes_valid 1 ((),(p,b)))]
  cases b <;> simp [forecasts,outcomes,roundAt_one,boolValue]

/-- The exact expected loss for each of the two possible deterministic first actions. -/
theorem expectedCalDist_one_formula (K : BehavioralForecaster) (A : Adversary) :
    expectedCalDist K A 1 =
      if A.action 0 () then 1-mean K 0 () else mean K 0 () := by
  change (∫ h, pathLoss 1 h ∂law K A.randomized 1) = _
  have hm : Measurable (fun p : Probability =>
      (((),(p,A.action 0 ())) : History 1)) :=
    measurable_const.prodMk (measurable_id.prodMk measurable_const)
  rw [one_round_law]
  rw [integral_map (β := History 1) (μ := K.kernel 0 ())
    (φ := fun p : Probability => (((),(p,A.action 0 ())) : History 1))
    (f := pathLoss 1) hm.aemeasurable (measurable_pathLoss 1).aestronglyMeasurable]
  simp_rw [one_round_pathLoss]
  cases hb : A.action 0 ()
  · simp only [boolValue_false, sub_zero, Bool.false_eq_true, ↓reduceIte]
    have he : (fun p : Probability => |(p:ℝ)|) = fun p : Probability => (p:ℝ) := by
      funext p
      exact abs_of_nonneg p.property.1
    rw [he]
    rfl
  · simp only [boolValue_true, ↓reduceIte]
    have he : (fun p : Probability => |(p:ℝ)-1|) = fun p : Probability => 1-(p:ℝ) := by
      funext p
      rw [abs_of_nonpos (sub_nonpos.mpr p.property.2)]
      ring
    rw [he, integral_sub (integrable_const 1) (integrable_forecast K 0 ())]
    simp [mean]

/-- The randomized-adaptive lower value is at least `1/2` when `T=1`. -/
theorem randomized_one_round_lower (K : BehavioralForecaster) :
    ∃ A : Adversary, (1/2:ℝ) ≤ expectedCalDist K A 1 := by
  by_cases hm : (1/2:ℝ) ≤ mean K 0 ()
  · refine ⟨constantAdversary false, ?_⟩
    simpa only [expectedCalDist_one_formula, constantAdversary, Bool.false_eq_true,
      ↓reduceIte] using hm
  · refine ⟨constantAdversary true, ?_⟩
    rw [expectedCalDist_one_formula]
    simp only [constantAdversary, ↓reduceIte]
    linarith

def halfProbability : Probability := ⟨1/2, by norm_num, by norm_num⟩

/-- The deterministic half forecast, viewed as a behavioral probability kernel. -/
def halfBehavioralForecaster : BehavioralForecaster where
  kernel n := Kernel.deterministic (fun _ : History n => halfProbability) measurable_const
  markov _ := inferInstance

theorem halfBehavioralForecaster_mean (n : ℕ) (h : History n) :
    mean halfBehavioralForecaster n h = 1/2 := by
  simp only [mean,halfBehavioralForecaster,Kernel.deterministic_apply]
  rw [integral_dirac]
  rfl

/-- The lower value is attained by the constant half forecast. -/
theorem halfBehavioralForecaster_one (A : Adversary) :
    expectedCalDist halfBehavioralForecaster A 1 = 1/2 := by
  rw [expectedCalDist_one_formula, halfBehavioralForecaster_mean]
  cases A.action 0 () <;> norm_num

end
end CalibrationDistance.Protocol
