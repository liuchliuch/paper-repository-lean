import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Probability.Distributions.Uniform

/-!
# The simultaneous public-history protocol

Histories are stored as nested products rather than as finite vectors.  This has
exactly one public `(forecast, outcome)` pair per completed round.  In particular
an adversary at round `n` takes `History n`, not `History (n+1)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace CalibrationDistance.Protocol

abbrev Probability := Set.Icc (0 : ℝ) 1
abbrev Round := Probability × Bool

def History : ℕ → Type
  | 0 => Unit
  | n + 1 => History n × Round

instance historyMeasurableSpace : (n : ℕ) → MeasurableSpace (History n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n + 1 => @Prod.instMeasurableSpace (History n) Round (historyMeasurableSpace n) inferInstance

/-- Public histories carry the usual finite product topology. -/
instance historyTopologicalSpace : (n : ℕ) → TopologicalSpace (History n)
  | 0 => inferInstanceAs (TopologicalSpace Unit)
  | n+1 => by
      haveI := historyTopologicalSpace n
      exact inferInstanceAs (TopologicalSpace (History n × Round))

/-- The measurable structure above is its Borel structure, as required in §2.2. -/
instance historyBorelSpace : (n : ℕ) → BorelSpace (History n)
  | 0 => inferInstanceAs (BorelSpace Unit)
  | n+1 => by
      haveI := historyBorelSpace n
      exact inferInstanceAs (BorelSpace (History n × Round))

/-- The forecaster has precisely the public history as input. -/
structure BehavioralForecaster where
  kernel : (n : ℕ) → Kernel (History n) Probability
  markov : ∀ n, IsMarkovKernel (kernel n)

attribute [instance] BehavioralForecaster.markov

/-- A deterministic past-adaptive adversary.  The current forecast is absent
from the domain. -/
structure Adversary where
  action : (n : ℕ) → History n → Bool
  measurable_action : ∀ n, Measurable (action n)

/-- Auxiliary behavioral adversaries may also randomize from public history. -/
structure RandomizedAdversary where
  kernel : (n : ℕ) → Kernel (History n) Bool
  markov : ∀ n, IsMarkovKernel (kernel n)

attribute [instance] RandomizedAdversary.markov

noncomputable def Adversary.randomized (A : Adversary) : RandomizedAdversary where
  kernel n := Kernel.deterministic (A.action n) (A.measurable_action n)
  markov n := inferInstance

/-- Product, rather than forecast-dependent, transitions express simultaneous play. -/
noncomputable def transition (K : BehavioralForecaster) (B : RandomizedAdversary)
    (n : ℕ) : Kernel (History n) Round := K.kernel n ×ₖ B.kernel n

instance transition_markov (K : BehavioralForecaster) (B : RandomizedAdversary) (n : ℕ) :
    IsMarkovKernel (transition K B n) := by
  unfold transition
  infer_instance

/-- The actual finite Ionescu--Tulcea recursion. -/
noncomputable def law (K : BehavioralForecaster) (B : RandomizedAdversary) :
    (n : ℕ) → Measure (History n)
  | 0 => Measure.dirac ()
  | n + 1 => (law K B n).compProd (transition K B n)

instance law_probability (K : BehavioralForecaster) (B : RandomizedAdversary) :
    (n : ℕ) → IsProbabilityMeasure (law K B n)
  | 0 => by unfold law; infer_instance
  | n + 1 => by
      haveI := law_probability K B n
      change IsProbabilityMeasure ((law K B n).compProd (transition K B n))
      infer_instance

@[simp] theorem law_zero (K : BehavioralForecaster) (B : RandomizedAdversary) :
    law K B 0 = Measure.dirac () := rfl

@[simp] theorem law_succ (K : BehavioralForecaster) (B : RandomizedAdversary) (n : ℕ) :
    law K B (n+1) = (law K B n).compProd (transition K B n) := rfl

/-- At a fixed history the two current actions have the product distribution. -/
theorem transition_apply (K : BehavioralForecaster) (B : RandomizedAdversary)
    (n : ℕ) (h : History n) :
    transition K B n h = (K.kernel n h).prod (B.kernel n h) :=
  Kernel.prod_apply _ _ _

/-- This is the transition displayed in Section 2.2, with the outcome a Dirac mass. -/
theorem deterministic_transition_apply (K : BehavioralForecaster) (A : Adversary)
    (n : ℕ) (h : History n) :
    transition K A.randomized n h =
      (K.kernel n h).prod (Measure.dirac (A.action n h)) := by
  rw [transition_apply]
  rfl

/-- The transition identity for nonnegative observables also records conditional independence. -/
theorem transition_lintegral (K : BehavioralForecaster) (B : RandomizedAdversary)
    (n : ℕ) (h : History n) {f : Round → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ r, f r ∂transition K B n h =
      ∫⁻ p, ∫⁻ y, f (p,y) ∂B.kernel n h ∂K.kernel n h :=
  Kernel.lintegral_prod _ _ _ hf

/-- Expectation is integration against the recursively generated trajectory law. -/
noncomputable def expectation (K : BehavioralForecaster) (A : Adversary) (T : ℕ)
    (loss : History T → ℝ) : ℝ := ∫ h, loss h ∂law K A.randomized T

/-- Conditional means are defined from the actual forecasting probability kernel. -/
noncomputable def mean (K : BehavioralForecaster) (n : ℕ) (h : History n) : ℝ :=
  ∫ p : Probability, (p : ℝ) ∂K.kernel n h

noncomputable def variance (K : BehavioralForecaster) (n : ℕ) (h : History n) : ℝ :=
  ∫ p : Probability, ((p : ℝ) - mean K n h)^2 ∂K.kernel n h

end CalibrationDistance.Protocol

namespace CalibrationDistance.Protocol

/-- Every forecast coordinate is integrable, since its range is `[0,1]`. -/
theorem integrable_forecast (K : BehavioralForecaster) (n : ℕ) (h : History n) :
    Integrable (fun p : Probability => (p : ℝ)) (K.kernel n h) := by
  apply (integrable_const (1 : ℝ)).mono' measurable_subtype_coe.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg p.property.1]
    exact p.property.2

theorem measurable_mean (K : BehavioralForecaster) (n : ℕ) :
    Measurable (mean K n) :=
  measurable_subtype_coe.stronglyMeasurable.integral_kernel.measurable

theorem mean_mem (K : BehavioralForecaster) (n : ℕ) (h : History n) :
    mean K n h ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg fun p => p.property.1
  · calc
      mean K n h ≤ ∫ _ : Probability, (1 : ℝ) ∂K.kernel n h :=
        integral_mono (integrable_forecast K n h) (integrable_const 1) fun p => p.property.2
      _ = 1 := by simp

theorem measurable_variance (K : BehavioralForecaster) (n : ℕ) :
    Measurable (variance K n) := by
  have hm : Measurable (fun hp : History n × Probability =>
      ((hp.2 : ℝ) - mean K n hp.1)^2) := by
    exact ((measurable_subtype_coe.comp measurable_snd).sub
      ((measurable_mean K n).comp measurable_fst)).pow_const 2
  exact hm.stronglyMeasurable.integral_kernel_prod_right'.measurable

theorem variance_nonneg (K : BehavioralForecaster) (n : ℕ) (h : History n) :
    0 ≤ variance K n h := integral_nonneg fun _ => sq_nonneg _

/-- A jointly measurable family of deterministic adversaries, indexed by a tape. -/
structure ParametricAdversary (Ω : Type*) [MeasurableSpace Ω] where
  action : (n : ℕ) → Ω × History n → Bool
  measurable_action : ∀ n, Measurable (action n)

noncomputable def ParametricAdversary.section {Ω : Type*} [MeasurableSpace Ω]
    (A : ParametricAdversary Ω) (w : Ω) : Adversary where
  action n h := A.action n (w,h)
  measurable_action n := (A.measurable_action n).comp measurable_prodMk_left

noncomputable def parameterTransition {Ω : Type*} [MeasurableSpace Ω]
    (K : BehavioralForecaster) (A : ParametricAdversary Ω) (n : ℕ) :
    Kernel (Ω × History n) Round :=
  (K.kernel n).comap Prod.snd measurable_snd ×ₖ
    Kernel.deterministic (A.action n) (A.measurable_action n)

instance parameterTransition_markov {Ω : Type*} [MeasurableSpace Ω]
    (K : BehavioralForecaster) (A : ParametricAdversary Ω) (n : ℕ) :
    IsMarkovKernel (parameterTransition K A n) := by
  unfold parameterTransition
  infer_instance

/-- This is a kernel *in the whole fixed tape*, not an arbitrary selected law. -/
noncomputable def parameterLaw {Ω : Type*} [MeasurableSpace Ω]
    (K : BehavioralForecaster) (A : ParametricAdversary Ω) :
    (n : ℕ) → Kernel Ω (History n)
  | 0 => Kernel.const Ω (Measure.dirac ())
  | n+1 => parameterLaw K A n ⊗ₖ parameterTransition K A n

instance parameterLaw_markov {Ω : Type*} [MeasurableSpace Ω]
    (K : BehavioralForecaster) (A : ParametricAdversary Ω) :
    (n : ℕ) → IsMarkovKernel (parameterLaw K A n)
  | 0 => by unfold parameterLaw; infer_instance
  | n+1 => by
      haveI := parameterLaw_markov K A n
      change IsMarkovKernel (parameterLaw K A n ⊗ₖ parameterTransition K A n)
      infer_instance

/-- Freezing the parameter gives exactly the ordinary deterministic-adversary law. -/
theorem parameterLaw_apply {Ω : Type*} [MeasurableSpace Ω]
    (K : BehavioralForecaster) (A : ParametricAdversary Ω) (w : Ω) :
    ∀ n, parameterLaw K A n w = law K (A.section w).randomized n
  | 0 => rfl
  | n+1 => by
      change (parameterLaw K A n ⊗ₖ parameterTransition K A n) w = _
      rw [Kernel.compProd_apply_eq_compProd_sectR
        (parameterLaw K A n) (parameterTransition K A n) w, parameterLaw_apply K A w n]
      change (law K (A.section w).randomized n).compProd _ =
        (law K (A.section w).randomized n).compProd _
      congr 1
      ext h s hs
      simp [Kernel.sectR_apply, parameterTransition, transition,
        ParametricAdversary.section, Adversary.randomized, Kernel.prod_apply, Kernel.deterministic_apply]

/-- The joint law first samples a tape, then runs the forecaster against that fixed tape. -/
noncomputable def parameterJointLaw {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (K : BehavioralForecaster) (A : ParametricAdversary Ω) (T : ℕ) :
    Measure (Ω × History T) := ν.compProd (parameterLaw K A T)

instance parameterJointLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (K : BehavioralForecaster)
    (A : ParametricAdversary Ω) (T : ℕ) :
    IsProbabilityMeasure (parameterJointLaw ν K A T) := by
  unfold parameterJointLaw
  infer_instance

/-- Fubini's equality used when adversary randomization is removed. -/
theorem parameter_integral_eq {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [SFinite ν] (K : BehavioralForecaster)
    (A : ParametricAdversary Ω) (T : ℕ) (loss : History T → ℝ)
    (hi : Integrable (fun z : Ω × History T => loss z.2) (parameterJointLaw ν K A T)) :
    (∫ z, loss z.2 ∂parameterJointLaw ν K A T) =
      ∫ w, expectation K (A.section w) T loss ∂ν := by
  rw [parameterJointLaw, Measure.integral_compProd hi]
  simp_rw [parameterLaw_apply]
  rfl

/-- The averaging argument fixes a tape; no loss bound is inserted as a protocol axiom. -/
theorem exists_fixed_parameter {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (K : BehavioralForecaster)
    (A : ParametricAdversary Ω) (T : ℕ) (loss : History T → ℝ)
    (hi : Integrable (fun z : Ω × History T => loss z.2) (parameterJointLaw ν K A T)) :
    ∃ w, (∫ z, loss z.2 ∂parameterJointLaw ν K A T) ≤
      expectation K (A.section w) T loss := by
  have hi' : Integrable (fun w => expectation K (A.section w) T loss) ν := by
    have h : Integrable (fun w => ∫ h, loss h ∂parameterLaw K A T w) ν := by
      simpa [parameterJointLaw, Measure.compProd, Kernel.prodMkLeft_apply, Kernel.const_apply]
        using hi.integral_compProd
    simpa only [parameterLaw_apply] using h
  rw [parameter_integral_eq ν K A T loss hi]
  exact exists_integral_le hi'

/-- Thresholding independent uniform tape coordinates is the adversary in §5.1. -/
noncomputable def thresholdAdversary
    (q : (n : ℕ) → History n → ℝ) (hq : ∀ n, Measurable (q n)) :
    ParametricAdversary (ℕ → Probability) where
  action n z := if (z.1 n : ℝ) ≤ q n z.2 then true else false
  measurable_action n := by
    apply Measurable.ite _ measurable_const measurable_const
    exact measurableSet_le
      (measurable_subtype_coe.comp ((measurable_pi_apply n).comp measurable_fst))
      ((hq n).comp measurable_snd)

end CalibrationDistance.Protocol

namespace CalibrationDistance.Protocol

abbrev FiniteTape (T : ℕ) := Fin T → Probability

/-- Only the first `T` tape coordinates are used by the `T`-round game. -/
noncomputable def finiteThresholdAdversary (T : ℕ)
    (q : (n : ℕ) → History n → ℝ) (hq : ∀ n, Measurable (q n)) :
    ParametricAdversary (FiniteTape T) where
  action n z := if hn : n < T then
    if (z.1 ⟨n,hn⟩ : ℝ) ≤ q n z.2 then true else false
    else false
  measurable_action n := by
    by_cases hn : n < T
    · simp only [dif_pos hn]
      apply Measurable.ite _ measurable_const measurable_const
      exact measurableSet_le
        (measurable_subtype_coe.comp ((measurable_pi_apply (⟨n,hn⟩ : Fin T)).comp measurable_fst))
        ((hq n).comp measurable_snd)
    · simp only [dif_neg hn]
      exact measurable_const

/-- A bounded Borel loss has a genuine finite expectation under every protocol law. -/
theorem integrable_bounded_loss (K : BehavioralForecaster) (B : RandomizedAdversary)
    (T : ℕ) (loss : History T → ℝ) (hl : Measurable loss) (C : ℝ)
    (hb : ∀ h, ‖loss h‖ ≤ C) : Integrable loss (law K B T) :=
  (integrable_const C).mono' hl.aestronglyMeasurable (Filter.Eventually.of_forall hb)

/-- The same boundedness criterion applies to the tape-first joint construction. -/
theorem integrable_parameter_loss {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (K : BehavioralForecaster)
    (A : ParametricAdversary Ω) (T : ℕ) (loss : History T → ℝ)
    (hl : Measurable loss) (C : ℝ) (hb : ∀ h, ‖loss h‖ ≤ C) :
    Integrable (fun z : Ω × History T => loss z.2) (parameterJointLaw ν K A T) := by
  apply (integrable_const C).mono' (hl.comp measurable_snd).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => hb z.2

/-- Coordinate projection from the nested history to the conventional finite sequence. -/
def roundAt : (n : ℕ) → History n → Fin n → Round
  | 0, _, i => Fin.elim0 i
  | n+1, h, i => Fin.lastCases h.2 (fun j => roundAt n h.1 j) i

theorem measurable_roundAt : ∀ (n : ℕ) (i : Fin n),
    Measurable (fun h : History n => roundAt n h i)
  | 0, i => Fin.elim0 i
  | n+1, i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [roundAt] using (measurable_snd : Measurable (Prod.snd : History n × Round → Round))
    · simpa [roundAt] using (measurable_roundAt n j).comp measurable_fst

def forecasts (T : ℕ) (h : History T) : Fin T → ℝ := fun i => (roundAt T h i).1

def outcomes (T : ℕ) (h : History T) : Fin T → ℝ :=
  fun i => if (roundAt T h i).2 then 1 else 0

theorem measurable_forecasts (T : ℕ) : Measurable (forecasts T) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_subtype_coe.comp (measurable_fst.comp (measurable_roundAt T i))

theorem forecasts_mem (T : ℕ) (h : History T) (i : Fin T) :
    forecasts T h i ∈ Set.Icc (0 : ℝ) 1 := (roundAt T h i).1.property

theorem measurable_outcomes (T : ℕ) : Measurable (outcomes T) := by
  apply measurable_pi_lambda
  intro i
  have hm := measurable_snd.comp (measurable_roundAt T i)
  exact (measurable_of_countable (fun b : Bool => if b then (1:ℝ) else 0)).comp hm

theorem outcomes_binary (T : ℕ) (h : History T) (i : Fin T) :
    outcomes T h i = 0 ∨ outcomes T h i = 1 := by
  unfold outcomes
  cases (roundAt T h i).2 <;> simp

end CalibrationDistance.Protocol

namespace CalibrationDistance.Protocol

/-- The transition recursion uniquely determines every finite trajectory measure. -/
theorem law_unique (K : BehavioralForecaster) (B : RandomizedAdversary)
    (ν : (n : ℕ) → Measure (History n))
    (hzero : ν 0 = Measure.dirac ())
    (hsucc : ∀ n, ν (n+1) = (ν n).compProd (transition K B n)) :
    ∀ n, ν n = law K B n
  | 0 => hzero
  | n+1 => by rw [hsucc, law_unique K B ν hzero hsucc n]; rfl

/-- Forgetting the current round recovers the preceding public-history law. -/
theorem law_succ_fst (K : BehavioralForecaster) (B : RandomizedAdversary) (n : ℕ) :
    (law K B (n+1)).fst = law K B n :=
  Measure.fst_compProd _ _

end CalibrationDistance.Protocol
