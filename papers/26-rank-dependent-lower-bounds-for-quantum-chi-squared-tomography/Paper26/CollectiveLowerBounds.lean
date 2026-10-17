import Paper26.GraphExperiment
import Paper26.GraphPrior
import Paper26.CollectiveGraphBudget
import Paper26.LossMeasurability
import Paper26.JordanLossMeasurability
import Paper26.InformationRateBounds

/-!
# Collective lower bounds from the actual graph experiment

This module applies the constructed graph prior, actual collective Born
experiment, native collective Fisher budget, coordinate-preserving volume
transfer and the proved posterior success theorem. No successful-volume,
posterior-success or sample lower-bound conclusion is an external field.

The raw geometry bundle below only groups already registered classical
matrix/Haar/chart inputs. Both actual joint spectral-loss success events are
proved measurable by `LossMeasurability` and `JordanLossMeasurability`.
The scope is `0 < r ≤ s`, `r*s ≥ 2`; no arbitrary-dimension endpoint reduction
or complete Theorem 1.2 claim is made here.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal NNReal
open MeasureTheory Set

namespace Paper26.CollectiveLowerBounds

open QuantumModel H1PosteriorBound GraphExperiment

/-- A bundle of existing raw volume inputs. None of its fields states a loss
probability, successful volume, Fisher budget, or learning lower bound. -/
structure VolumeInputs (r s : ℕ) [NeZero r] where
  chart : ChartVolume.GraphChartInput
  truncation : HaarTruncation.TruncatedHaarInput
  properNull : HaarTruncation.ProperSubspaceNullInput (Fin r ⊕ Fin s) (Fin r)
  metric : TailMass.BuresMetricInput (Fin r ⊕ Fin s)
  compression : TailMassBridges.RawCompressionInput (Fin r ⊕ Fin s) (Fintype.card (Fin r))
  lyapunov : TailConvexity.LyapunovPositivityInput (Fin s)
  brunnMinkowski : TailVolume.BrunnMinkowskiInput (Fin s) (Fin r)
  unitaryLebesgue : TailVolume.UnitaryLebesgueInput (Fin s) (Fin r)
  ballVolume : ScalarTailBall.EuclideanBallVolumeInput (Fin s) (Fin r)
  rowScaling : RightTailVolume.PositiveRowScalingInput (Fin s) (Fin r)
  haar : Measure (HaarTruncation.FrameSpace r s)
  isHaar : HaarFrames.IsHaarFrameDistribution haar

local instance matrixMeasurableSpace (m k : Type*) : MeasurableSpace (Matrix m k ℂ) :=
  inferInstanceAs (MeasurableSpace (m → k → ℂ))
local instance matrixBorelSpace (m k : Type*) [Fintype m] [Fintype k] :
    BorelSpace (Matrix m k ℂ) := inferInstanceAs (BorelSpace (m → k → ℂ))

variable {r s n : ℕ} [NeZero r]
variable {Y : Type*} [MeasurableSpace Y]
variable (A : CollectiveModel.Learner (StateIndex r s) Y n)

def chartDomain (r s : ℕ) : Set (Parameter r s) :=
  {θ | (MatrixCoordinates.coordinates r s).symm θ ∈ ChartVolume.localChart r s}

omit [NeZero r] in
theorem measurableSet_chartDomain : MeasurableSet (chartDomain r s) :=
  (ChartVolume.isClosed_localChart r s).measurableSet.preimage
    (MatrixCoordinates.measurableEquiv r s).symm.measurable

/-- The actual successful graph parameters within the prior's chart. -/
def successSection (χ : Density (StateIndex r s) → Density (StateIndex r s) → ℝ≥0∞)
    (ε : ℝ) (y : Y) : Set (Parameter r s) :=
  successParameters A χ (ENNReal.ofReal ε) (chartDomain r s) y

theorem section_eq_preimage
    (χ : Density (StateIndex r s) → Density (StateIndex r s) → ℝ≥0∞)
    (ε : ℝ) (y : Y) :
    successSection A χ ε y = (MatrixCoordinates.measurableEquiv r s).symm ⁻¹'
      ChartVolume.localSuccess r s χ (A.estimator.estimate y) ε := rfl

/-- The explicit inverse coordinates preserve the successful volume exactly. -/
theorem section_volume_eq
    (χ : Density (StateIndex r s) → Density (StateIndex r s) → ℝ≥0∞)
    (ε : ℝ) (y : Y) :
    volume (successSection A χ ε y) = HaarTruncation.matrixLebesgue r s
      (ChartVolume.localSuccess r s χ (A.estimator.estimate y) ε) := by
  rw [section_eq_preimage]
  exact (MatrixCoordinates.volume_preserving_coordinates r s).symm.measure_preimage_equiv _

/-- The actual right-inverse joint successful event is measurable. -/
theorem measurableSet_section_right (ε : ℝ) :
    MeasurableSet {z : Y × Parameter r s | z.2 ∈ successSection A chiR ε z.1} := by
  have hstate : Measurable (state (r := r) (s := s) : Parameter r s → Density (StateIndex r s)) := by
    intro B hB
    exact (MatrixCoordinates.measurableEquiv r s).symm.measurable
      (GraphFamily.measurable_density (κ := Fin r) (σ := Fin s) hB)
  have hmap : Measurable (fun z : Y × Parameter r s =>
      (state (r := r) (s := s) z.2, A.estimator.estimate z.1)) :=
    (hstate.comp measurable_snd).prodMk (A.estimator.measurable_estimate.comp measurable_fst)
  have hloss : Measurable (fun z : Y × Parameter r s =>
      chiR (state z.2) (A.estimator.estimate z.1)) := by
    intro B hB
    exact hmap (LossMeasurability.measurable_chiR (ι := StateIndex r s) hB)
  change MeasurableSet {z : Y × Parameter r s | z.2 ∈ chartDomain r s ∧
    chiR (state z.2) (A.estimator.estimate z.1) ≤ ENNReal.ofReal ε}
  exact ((measurableSet_chartDomain (r := r) (s := s)).preimage measurable_snd).inter
    (measurableSet_le hloss measurable_const)

/-- The actual Bures joint successful event is measurable, including
singular estimator outputs and the support/infinity convention. -/
theorem measurableSet_section_bures (ε : ℝ) :
    MeasurableSet {z : Y × Parameter r s | z.2 ∈ successSection A chiB ε z.1} := by
  have hstate : Measurable (state (r := r) (s := s) : Parameter r s → Density (StateIndex r s)) := by
    intro B hB
    exact (MatrixCoordinates.measurableEquiv r s).symm.measurable
      (GraphFamily.measurable_density (κ := Fin r) (σ := Fin s) hB)
  have hmap : Measurable (fun z : Y × Parameter r s =>
      (state (r := r) (s := s) z.2, A.estimator.estimate z.1)) :=
    (hstate.comp measurable_snd).prodMk (A.estimator.measurable_estimate.comp measurable_fst)
  have hloss : Measurable (fun z : Y × Parameter r s =>
      chiB (state z.2) (A.estimator.estimate z.1)) := by
    intro B hB
    exact hmap (JordanLossMeasurability.measurable_chiB (ι := StateIndex r s) hB)
  change MeasurableSet {z : Y × Parameter r s | z.2 ∈ chartDomain r s ∧
    chiB (state z.2) (A.estimator.estimate z.1) ≤ ENNReal.ofReal ε}
  exact ((measurableSet_chartDomain (r := r) (s := s)).preimage measurable_snd).inter
    (measurableSet_le hloss measurable_const)

omit [NeZero r] in
/-- The actual prior root vanishes off the local parameter domain. -/
theorem prior_zero_off_chart (w : GraphPrior.SmoothPriorWitness r s (1 / 2 : ℝ)) :
    ∀ θ ∉ chartDomain r s, w.weakRoot.root θ = 0 := by
  intro θ hθ
  by_contra hn
  exact hθ (GraphPrior.halfChart_root_support r s w (subset_closure hn))

/-- The native collective budget is averaged against the genuine normalized
prior density, with ENNReal integrals throughout. -/
theorem dataInformation_le (G : GraphFisherBudget.GraphTangentInput)
    (h : WeakH1Root (2 * r * s)) (hh : h.mass univ = 1) :
    WeakPosteriorIdentity.dataInformation A.measurement.reference h (likelihoodRoot A) ≤
      ENNReal.ofReal (8 * (n : ℝ) * s) := by
  have hd : AEMeasurable (fun θ => ENNReal.ofReal (h.root θ ^ 2)) volume :=
    (h.root_aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  have he : AEMeasurable (fun θ : Parameter r s => ∫⁻ y,
      ‖fderiv ℝ (likelihoodRoot A y) θ‖ₑ ^ (2 : ℕ) ∂A.measurement.reference) volume :=
    ((likelihoodRoot_fderiv_joint_measurable A).aestronglyMeasurable.enorm.pow_const 2).lintegral_prod_left'
  have hb (θ : Parameter r s) :
      4 * (∫⁻ y, ‖fderiv ℝ (likelihoodRoot A y) θ‖ₑ ^ (2 : ℕ) ∂A.measurement.reference) ≤
        ENNReal.ofReal (8 * (n : ℝ) * s) := by
    have hm : AEMeasurable (fun y => ‖fderiv ℝ (likelihoodRoot A y) θ‖ₑ ^ (2 : ℕ))
        A.measurement.reference :=
      (((likelihoodRoot_fderiv_joint_measurable A).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable.enorm.pow_const 2)
    calc
      _ = ∫⁻ y, 4 * ‖fderiv ℝ (likelihoodRoot A y) θ‖ₑ ^ (2 : ℕ) ∂A.measurement.reference :=
        (lintegral_const_mul'' _ hm).symm
      _ = ∫⁻ y, ENNReal.ofReal (4 * ‖fderiv ℝ (likelihoodRoot A y) θ‖ ^ (2 : ℕ))
          ∂A.measurement.reference := by
        apply lintegral_congr
        intro y
        rw [WeakPosteriorIdentity.enorm_sq_eq_ofReal_norm_sq, ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ ≤ _ := CollectiveGraphBudget.collective_fisher_budget_lintegral A G θ
  have hn : (∫⁻ θ, ENNReal.ofReal (h.root θ ^ 2)) = 1 := by
    simpa only [WeakH1Root.mass, Measure.restrict_univ] using hh
  calc
    _ = ∫⁻ θ, ENNReal.ofReal (h.root θ ^ 2) *
        (4 * ∫⁻ y, ‖fderiv ℝ (likelihoodRoot A y) θ‖ₑ ^ (2 : ℕ) ∂A.measurement.reference) := by
      unfold WeakPosteriorIdentity.dataInformation
      rw [← lintegral_const_mul'' _ (hd.mul he)]
      exact lintegral_congr (fun _ => by ac_rfl)
    _ ≤ ∫⁻ θ, ENNReal.ofReal (h.root θ ^ 2) * ENNReal.ofReal (8 * (n : ℝ) * s) :=
      lintegral_mono (fun θ => mul_le_mul_left' (hb θ) _)
    _ = _ := by rw [lintegral_mul_const'' _ hd, hn, one_mul]

omit [NeZero r] in
/-- The `2/(2rs)` power in the posterior theorem cancels the genuine `rs`
power volume bound. -/
theorem power_volume_root (hr : 0 < r) (hs : 0 < s) (b : ℝ) (hb : 0 ≤ b) :
    (ENNReal.ofReal (b ^ (r * s))) ^ (2 / ((2 * r * s : ℕ) : ℝ)) = ENNReal.ofReal b := by
  have hq : r * s ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hr hs)
  have hexp : (2 / ((2 * r * s : ℕ) : ℝ)) = 1 / ((r * s : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [hexp, ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hb _) (by positivity),
    one_div, Real.pow_rpow_inv_natCast hb hq]

/-- The actual posterior theorem, actual quantum budget, and actual successful
volume bound imply a finite ENNReal Born-success bound. The scalar inputs here
are component bounds, not a desired success conclusion. -/
theorem success_upper_of_volume
    (hp : 3 ≤ 2 * r * s) (hr : 0 < r) (hs : 0 < s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) (h : WeakH1Root (2 * r * s)) (hh : h.mass univ = 1)
    (S : Y → Set (Parameter r s)) (hS : MeasurableSet {z : Y × Parameter r s | z.2 ∈ S z.1})
    (b B : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hv : ∀ᵐ y ∂A.measurement.reference, volume (S y) ≤ ENNReal.ofReal (b ^ (r * s)))
    (hprior : h.fisher ≤ ENNReal.ofReal B) :
    priorAverageSuccess A h S ≤
      ENNReal.ofReal (b / ((2 * r * s : ℕ) : ℝ) * (B + 8 * (n : ℝ) * s)) := by
  have hbudget : h.fisher + WeakPosteriorIdentity.dataInformation A.measurement.reference h
      (likelihoodRoot A) ≤ ENNReal.ofReal (B + 8 * (n : ℝ) * s) := by
    rw [ENNReal.ofReal_add hB (by positivity)]
    exact add_le_add hprior (dataInformation_le A G h hh)
  have hd : 0 < ((2 * r * s : ℕ) : ℝ) := by positivity
  calc
    _ ≤ ENNReal.ofReal (b ^ (r * s)) ^ (2 / ((2 * r * s : ℕ) : ℝ)) /
        ((2 * r * s : ℕ) : ℝ≥0∞) *
        (h.fisher + WeakPosteriorIdentity.dataInformation A.measurement.reference h (likelihoodRoot A)) :=
      priorAverageSuccess_bound A hp Sob Coarse P U h S hS hv
    _ ≤ ENNReal.ofReal b / ((2 * r * s : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (B + 8 * (n : ℝ) * s) := by
      rw [power_volume_root hr hs b hb]
      exact mul_le_mul_left' hbudget _
    _ = _ := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos hd,
        ← ENNReal.ofReal_mul (div_nonneg hb hd.le)]

/-- The finite actual success bound is transported through the proved scalar
rate substitution; its premise is the successful-volume component bound. -/
theorem success_rate_of_volume
    (hp : 3 ≤ 2 * r * s) (hr : 0 < r) (hs : 0 < s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) (h : WeakH1Root (2 * r * s)) (hh : h.mass univ = 1)
    (S : Y → Set (Parameter r s)) (hS : MeasurableSet {z : Y × Parameter r s | z.2 ∈ S z.1})
    (K C₀ scale : ℝ) (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hscale : 0 ≤ scale)
    (hv : ∀ᵐ y ∂A.measurement.reference,
      volume (S y) ≤ ENNReal.ofReal ((K * scale / (s : ℝ)) ^ (r * s)))
    (hprior : h.fisher ≤ ENNReal.ofReal (C₀ * r * (s : ℝ) ^ 2)) :
    priorAverageSuccess A h S ≤ ENNReal.ofReal
      (InformationRateBounds.rateConstant K C₀ * scale * (1 + (n : ℝ) / ((r : ℝ) * s))) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hb := success_upper_of_volume A hp hr hs Sob Coarse P U G h hh S hS
    (K * scale / (s : ℝ)) (C₀ * r * (s : ℝ) ^ 2) (by positivity) (by positivity) hv hprior
  have hfin : priorAverageSuccess A h S ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hreal : (priorAverageSuccess A h S).toReal ≤
      (K * scale / (s : ℝ)) / (2 * (r : ℝ) * s) * (C₀ * r * (s : ℝ) ^ 2 + 8 * n * s) := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    push_cast at ht
    exact ht
  have hrate := InformationRateBounds.success_rate (K := K) (C₀ := C₀)
    (r := (r : ℝ)) (s := (s : ℝ)) (b := 1) (n := (n : ℝ))
    (scale := scale) (vroot := K * scale / (s : ℝ))
    (priorI := C₀ * r * (s : ℝ) ^ 2) (dataI := 8 * (n : ℝ) * s)
    hK hC₀ hrR hsR (by norm_num) (Nat.cast_nonneg n) hscale
    (by positivity) (by positivity) le_rfl le_rfl (by simp)
    (by simpa only [div_one] using hreal)
  calc
    priorAverageSuccess A h S = ENNReal.ofReal (priorAverageSuccess A h S).toReal :=
      (ENNReal.ofReal_toReal hfin).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by simpa only [mul_one] using hrate)

def buresVolumeConstant : ℝ := (75 / 8 : ℝ) * Real.pi * Real.exp 1 ^ 2
def rightVolumeConstant : ℝ := (225 / 8 : ℝ) * Real.pi * Real.exp 1 ^ 2

theorem buresVolumeConstant_pos : 0 < buresVolumeConstant := by
  unfold buresVolumeConstant
  positivity

theorem rightVolumeConstant_pos : 0 < rightVolumeConstant := by
  unfold rightVolumeConstant
  positivity

def buresRateConstant (C : ℝ) : ℝ :=
  InformationRateBounds.rateConstant buresVolumeConstant (16 * C)
def rightRateConstant (C : ℝ) : ℝ :=
  InformationRateBounds.rateConstant rightVolumeConstant (16 * C)

theorem buresRateConstant_pos {C : ℝ} (hC : 0 < C) : 0 < buresRateConstant C :=
  InformationRateBounds.rateConstant_pos buresVolumeConstant_pos (by positivity)

theorem rightRateConstant_pos {C : ℝ} (hC : 0 < C) : 0 < rightRateConstant C :=
  InformationRateBounds.rateConstant_pos rightVolumeConstant_pos (by positivity)

/-- Equation (30) for the genuine collective Born experiment, using the actual
half-chart prior and Corollary 2.5. Actual joint success measurability is proved. -/
theorem bures_success_rate
    (V : VolumeInputs r s) (hp : 3 ≤ 2 * r * s) (hr : 0 < r) (hrs : r ≤ s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (w : GraphPrior.SmoothPriorWitness r s (1 / 2 : ℝ))
    (hw : w.weakRoot.fisher ≤ ENNReal.ofReal ((16 * C) * r * (s : ℝ) ^ 2))
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    priorAverageSuccess A w.weakRoot (successSection A chiB ε) ≤
      ENNReal.ofReal (buresRateConstant C * ε * Real.sqrt ((r : ℝ) / s) *
        (1 + (n : ℝ) / ((r : ℝ) * s))) := by
  have hs : 0 < s := hr.trans_le hrs
  have hv : ∀ y, volume (successSection A chiB ε y) ≤ ENNReal.ofReal
      ((buresVolumeConstant * (ε * Real.sqrt ((r : ℝ) / s)) / s) ^ (r * s)) := by
    intro y
    rw [section_volume_eq]
    have h := ChartVolume.corollary_2_5_bures V.chart r s hr hrs V.truncation V.properNull
      V.metric V.compression V.lyapunov V.brunnMinkowski V.unitaryLebesgue V.ballVolume
      V.haar V.isHaar (A.estimator.estimate y) hε hε1
    convert h using 1
    unfold buresVolumeConstant
    congr 2
    ring
  have h := success_rate_of_volume A hp hr hs Sob Coarse P U G w.weakRoot w.weakRoot_normalized
    (successSection A chiB ε) (measurableSet_section_bures A ε)
    buresVolumeConstant (16 * C) (ε * Real.sqrt ((r : ℝ) / s)) buresVolumeConstant_pos.le
    (by positivity) (by positivity) (Filter.Eventually.of_forall hv) hw
  simpa only [buresRateConstant, mul_assoc] using h

/-- Equation (32) for the actual collective learner. Full joint right-inverse
loss measurability is derived, including singular estimator outputs. -/
theorem right_success_rate
    (V : VolumeInputs r s) (hp : 3 ≤ 2 * r * s) (hr : 0 < r) (hrs : r ≤ s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (w : GraphPrior.SmoothPriorWitness r s (1 / 2 : ℝ))
    (hw : w.weakRoot.fisher ≤ ENNReal.ofReal ((16 * C) * r * (s : ℝ) ^ 2))
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    priorAverageSuccess A w.weakRoot (successSection A chiR ε) ≤
      ENNReal.ofReal (rightRateConstant C * ((r : ℝ) * ε ^ 2 / s) *
        (1 + (n : ℝ) / ((r : ℝ) * s))) := by
  have hs : 0 < s := hr.trans_le hrs
  have hv : ∀ y, volume (successSection A chiR ε y) ≤ ENNReal.ofReal
      ((rightVolumeConstant * ((r : ℝ) * ε ^ 2 / s) / s) ^ (r * s)) := by
    intro y
    rw [section_volume_eq]
    have h := ChartVolume.corollary_2_5_right V.chart r s hr hrs V.truncation V.properNull
      V.metric V.compression V.rowScaling V.ballVolume V.haar V.isHaar
      (A.estimator.estimate y) hε hε1
    convert h using 1
    unfold rightVolumeConstant
    congr 2
    ring
  exact success_rate_of_volume A hp hr hs Sob Coarse P U G w.weakRoot w.weakRoot_normalized
    (successSection A chiR ε) (measurableSet_section_right A ε)
    rightVolumeConstant (16 * C) ((r : ℝ) * ε ^ 2 / s) rightVolumeConstant_pos.le
    (by positivity) (by positivity) (Filter.Eventually.of_forall hv) hw

/-- A finite ENNReal upper bound allows the actual constant-confidence
learning lower bound to pass to real success without totalization issues. -/
theorem two_thirds_le_toReal {Z : ℝ≥0∞} {B : ℝ}
    (hupper : Z ≤ ENNReal.ofReal B) (hlower : (2 : ℝ≥0∞) / 3 ≤ Z) :
    (2 / 3 : ℝ) ≤ Z.toReal := by
  have hz : Z ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  have h := ENNReal.toReal_mono hz hlower
  norm_num at h ⊢
  exact h

/-- The collective Bures lower bound on actual flat graph states. The prior
is obtained here from the raw NZ prior theorem, and all volume, information,
Born-success and scalar-extraction steps are genuinely applied. -/
theorem bures_collective_lower_bound
    (V : VolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s) (hrs2 : 2 ≤ r * s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hsmall : ε ≤ SampleLowerBounds.accuracyThreshold (buresRateConstant C))
    (hlearn : A.BuresSuccess r (ENNReal.ofReal ε)) :
    (1 / (3 * buresRateConstant C)) *
      (Real.sqrt (r : ℝ) * s * Real.sqrt (s : ℝ) / ε) ≤ (n : ℝ) := by
  have hp : 3 ≤ 2 * r * s := by nlinarith
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  obtain ⟨w, hw⟩ := GraphPrior.exists_halfChart_prior hC N r s hr hrs
  have hu := bures_success_rate A V hp hr hrs Sob Coarse P U G hC w hw hε hε1
  have hl : (2 : ℝ≥0∞) / 3 ≤
      priorAverageSuccess A w.weakRoot (successSection A chiB ε) :=
    learnsRank_le_priorAverageSuccess A chiB (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)
      w.weakRoot w.weakRoot_normalized (chartDomain r s) (prior_zero_off_chart w) hlearn
  have hrate0 : 0 ≤ buresRateConstant C := (buresRateConstant_pos hC).le
  have huR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal (by positivity)] at huR
  exact SampleLowerBounds.bures_collective (buresRateConstant_pos hC) hrR hrsR hε hsmall
    (two_thirds_le_toReal hu hl) huR

/-- The collective right-inverse lower bound on actual flat graph states,
with no joint spectral-loss-measurability premise. -/
theorem right_collective_lower_bound
    (V : VolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s) (hrs2 : 2 ≤ r * s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hsmall : ε ≤ SampleLowerBounds.accuracyThreshold (rightRateConstant C))
    (hlearn : A.RightSuccess r (ENNReal.ofReal ε)) :
    (1 / (3 * rightRateConstant C)) * ((s : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  have hp : 3 ≤ 2 * r * s := by nlinarith
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  obtain ⟨w, hw⟩ := GraphPrior.exists_halfChart_prior hC N r s hr hrs
  have hu := right_success_rate A V hp hr hrs Sob Coarse P U G hC w hw hε hε1
  have hl : (2 : ℝ≥0∞) / 3 ≤
      priorAverageSuccess A w.weakRoot (successSection A chiR ε) :=
    learnsRank_le_priorAverageSuccess A chiR (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)
      w.weakRoot w.weakRoot_normalized (chartDomain r s) (prior_zero_off_chart w) hlearn
  have hrate0 : 0 ≤ rightRateConstant C := (rightRateConstant_pos hC).le
  have huR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal (by positivity)] at huR
  exact SampleLowerBounds.right_collective (rightRateConstant_pos hC) hrR hrsR hε hsmall
    (two_thirds_le_toReal hu hl) huR

/-- One positive universal small-accuracy threshold works for both actual
collective lower bounds. It depends only on the universal NZ prior constant. -/
def accuracyThreshold (C : ℝ) : ℝ :=
  min (1 / 4) (min (SampleLowerBounds.accuracyThreshold (buresRateConstant C))
    (SampleLowerBounds.accuracyThreshold (rightRateConstant C)))

theorem accuracyThreshold_pos {C : ℝ} (hC : 0 < C) : 0 < accuracyThreshold C :=
  lt_min (by norm_num) (lt_min
    (SampleLowerBounds.accuracyThreshold_pos (buresRateConstant_pos hC))
    (SampleLowerBounds.accuracyThreshold_pos (rightRateConstant_pos hC)))

/-- Final flat-chart Bures collective sample lower bound, with one universal
accuracy threshold and no experiment-regularity or loss-measurability input. -/
theorem bures_collective
    (V : VolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s) (hrs2 : 2 ≤ r * s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyThreshold C)
    (hlearn : A.BuresSuccess r (ENNReal.ofReal ε)) :
    (1 / (3 * buresRateConstant C)) *
      (Real.sqrt (r : ℝ) * s * Real.sqrt (s : ℝ) / ε) ≤ (n : ℝ) := by
  have hε1 : ε ≤ 1 / 4 := hsmall.trans (min_le_left _ _)
  have hsmallB : ε ≤ SampleLowerBounds.accuracyThreshold (buresRateConstant C) :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  exact bures_collective_lower_bound A V hr hrs hrs2 Sob Coarse P U G hC N hε hε1 hsmallB hlearn

/-- Final flat-chart right-inverse collective sample lower bound, with the
same universal small-accuracy threshold. -/
theorem right_collective
    (V : VolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s) (hrs2 : 2 ≤ r * s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyThreshold C)
    (hlearn : A.RightSuccess r (ENNReal.ofReal ε)) :
    (1 / (3 * rightRateConstant C)) * ((s : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  have hε1 : ε ≤ 1 / 4 := hsmall.trans (min_le_left _ _)
  have hsmallR : ε ≤ SampleLowerBounds.accuracyThreshold (rightRateConstant C) :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  exact right_collective_lower_bound A V hr hrs hrs2 Sob Coarse P U G hC N hε hε1 hsmallR hlearn

end Paper26.CollectiveLowerBounds
