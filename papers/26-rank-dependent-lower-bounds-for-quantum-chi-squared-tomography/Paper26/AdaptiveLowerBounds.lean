import Paper26.AdaptiveGraphBudget
import Paper26.CollectiveMainLowerBounds

/-!
# Actual adaptive lower bounds

The actual adaptive experiment is embedded by the proved tensor-effect
construction. The posterior theorem and graph volume bounds are applied to
that actual learner, with the native adaptive information budget4ns/r rather
than the collective8ns budget. The flat graph estimates extend to every
`d ≥ 2`, `1 ≤ r ≤ d` on the named ambient index, using the pure-qubit
endpoint and the native rank comparison. The common positive coefficient and
small-accuracy threshold are those of `CollectiveMainLowerBounds`. No success
or sample conclusion is an input.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal NNReal
open MeasureTheory Set

namespace Paper26.AdaptiveLowerBounds

open QuantumModel H1PosteriorBound GraphExperiment CollectiveLowerBounds

universe u
variable {r s n : ℕ} [NeZero r] {Seed Ω : Type u}
  [MeasurableSpace Seed] [MeasurableSpace Ω]
  (A : AdaptiveModel.Learner (StateIndex r s) Seed Ω n)

abbrev embedded := AdaptiveCollectiveEmbedding.collectiveLearner A

/-- The native adaptive budget is averaged against the genuine normalized
prior density, with ENNReal integrals throughout. -/
theorem dataInformation_le (G : GraphFisherBudget.GraphTangentInput)
    (h : WeakH1Root (2 * r * s)) (hh : h.mass univ = 1) :
    WeakPosteriorIdentity.dataInformation (embedded A).measurement.reference h (likelihoodRoot (embedded A)) ≤
      ENNReal.ofReal (4 * (n : ℝ) * s / r) := by
  have hd : AEMeasurable (fun θ => ENNReal.ofReal (h.root θ ^ 2)) volume :=
    (h.root_aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  have he : AEMeasurable (fun θ : Parameter r s => ∫⁻ y,
      ‖fderiv ℝ (likelihoodRoot (embedded A) y) θ‖ₑ ^ (2 : ℕ) ∂(embedded A).measurement.reference) volume :=
    ((likelihoodRoot_fderiv_joint_measurable (embedded A)).aestronglyMeasurable.enorm.pow_const 2).lintegral_prod_left'
  have hb (θ : Parameter r s) :
      4 * (∫⁻ y, ‖fderiv ℝ (likelihoodRoot (embedded A) y) θ‖ₑ ^ (2 : ℕ) ∂(embedded A).measurement.reference) ≤
        ENNReal.ofReal (4 * (n : ℝ) * s / r) := by
    have hm : AEMeasurable (fun y => ‖fderiv ℝ (likelihoodRoot (embedded A) y) θ‖ₑ ^ (2 : ℕ))
        (embedded A).measurement.reference :=
      (((likelihoodRoot_fderiv_joint_measurable (embedded A)).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable.enorm.pow_const 2)
    calc
      _ = ∫⁻ y, 4 * ‖fderiv ℝ (likelihoodRoot (embedded A) y) θ‖ₑ ^ (2 : ℕ) ∂(embedded A).measurement.reference :=
        (lintegral_const_mul'' _ hm).symm
      _ = ∫⁻ y, ENNReal.ofReal (4 * ‖fderiv ℝ (likelihoodRoot (embedded A) y) θ‖ ^ (2 : ℕ))
          ∂(embedded A).measurement.reference := by
        apply lintegral_congr
        intro y
        rw [WeakPosteriorIdentity.enorm_sq_eq_ofReal_norm_sq, ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ ≤ _ := by
        convert AdaptiveGraphBudget.adaptive_fisher_budget_lintegral A G θ using 1
        congr 1
        ring
  have hn : (∫⁻ θ, ENNReal.ofReal (h.root θ ^ 2)) = 1 := by
    simpa only [WeakH1Root.mass, Measure.restrict_univ] using hh
  calc
    _ = ∫⁻ θ, ENNReal.ofReal (h.root θ ^ 2) *
        (4 * ∫⁻ y, ‖fderiv ℝ (likelihoodRoot (embedded A) y) θ‖ₑ ^ (2 : ℕ) ∂(embedded A).measurement.reference) := by
      unfold WeakPosteriorIdentity.dataInformation
      rw [← lintegral_const_mul'' _ (hd.mul he)]
      exact lintegral_congr (fun _ => by ac_rfl)
    _ ≤ ∫⁻ θ, ENNReal.ofReal (h.root θ ^ 2) * ENNReal.ofReal (4 * (n : ℝ) * s / r) :=
      lintegral_mono (fun θ => mul_le_mul_left' (hb θ) _)
    _ = _ := by rw [lintegral_mul_const'' _ hd, hn, one_mul]

/-- The actual posterior theorem, actual quantum budget, and actual successful
volume bound imply a finite ENNReal Born-success bound. The scalar inputs here
are component bounds, not a desired success conclusion. -/
theorem success_upper_of_volume
    (hp : 3 ≤ 2 * r * s) (hr : 0 < r) (hs : 0 < s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) (h : WeakH1Root (2 * r * s)) (hh : h.mass univ = 1)
    (S : AdaptiveModel.History Seed Ω n → Set (Parameter r s)) (hS : MeasurableSet {z : AdaptiveModel.History Seed Ω n × Parameter r s | z.2 ∈ S z.1})
    (b B₀ : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B₀)
    (hv : ∀ᵐ y ∂(embedded A).measurement.reference, volume (S y) ≤ ENNReal.ofReal (b ^ (r * s)))
    (hprior : h.fisher ≤ ENNReal.ofReal B₀) :
    priorAverageSuccess (embedded A) h S ≤
      ENNReal.ofReal (b / ((2 * r * s : ℕ) : ℝ) * (B₀ + 4 * (n : ℝ) * s / r)) := by
  have hbudget : h.fisher + WeakPosteriorIdentity.dataInformation (embedded A).measurement.reference h
      (likelihoodRoot (embedded A)) ≤ ENNReal.ofReal (B₀ + 4 * (n : ℝ) * s / r) := by
    rw [ENNReal.ofReal_add hB (by positivity)]
    exact add_le_add hprior (dataInformation_le A G h hh)
  have hd : 0 < ((2 * r * s : ℕ) : ℝ) := by positivity
  calc
    _ ≤ ENNReal.ofReal (b ^ (r * s)) ^ (2 / ((2 * r * s : ℕ) : ℝ)) /
        ((2 * r * s : ℕ) : ℝ≥0∞) *
        (h.fisher + WeakPosteriorIdentity.dataInformation (embedded A).measurement.reference h (likelihoodRoot (embedded A))) :=
      priorAverageSuccess_bound (embedded A) hp Sob Coarse P U h S hS hv
    _ ≤ ENNReal.ofReal b / ((2 * r * s : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (B₀ + 4 * (n : ℝ) * s / r) := by
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
    (S : AdaptiveModel.History Seed Ω n → Set (Parameter r s)) (hS : MeasurableSet {z : AdaptiveModel.History Seed Ω n × Parameter r s | z.2 ∈ S z.1})
    (K C₀ scale : ℝ) (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hscale : 0 ≤ scale)
    (hv : ∀ᵐ y ∂(embedded A).measurement.reference,
      volume (S y) ≤ ENNReal.ofReal ((K * scale / (s : ℝ)) ^ (r * s)))
    (hprior : h.fisher ≤ ENNReal.ofReal (C₀ * r * (s : ℝ) ^ 2)) :
    priorAverageSuccess (embedded A) h S ≤ ENNReal.ofReal
      (InformationRateBounds.rateConstant K C₀ * scale * (1 + (n : ℝ) / ((r : ℝ) ^ 2 * s))) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hb := success_upper_of_volume A hp hr hs Sob Coarse P U G h hh S hS
    (K * scale / (s : ℝ)) (C₀ * r * (s : ℝ) ^ 2) (by positivity) (by positivity) hv hprior
  have hfin : priorAverageSuccess (embedded A) h S ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hreal : (priorAverageSuccess (embedded A) h S).toReal ≤
      (K * scale / (s : ℝ)) / (2 * (r : ℝ) * s) * (C₀ * r * (s : ℝ) ^ 2 + 4 * n * s / r) := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    push_cast at ht
    exact ht
  have hrate := InformationRateBounds.success_rate (K := K) (C₀ := C₀)
    (r := (r : ℝ)) (s := (s : ℝ)) (b := (r : ℝ)) (n := (n : ℝ))
    (scale := scale) (vroot := K * scale / (s : ℝ))
    (priorI := C₀ * r * (s : ℝ) ^ 2) (dataI := 4 * (n : ℝ) * s / r)
    hK hC₀ hrR hsR hrR (Nat.cast_nonneg n) hscale
    (by positivity) (by positivity) le_rfl le_rfl (by
      apply div_le_div_of_nonneg_right _ hrR.le
      nlinarith [show 0 ≤ (n : ℝ) * s by positivity])
    (by simpa only [div_one] using hreal)
  calc
    priorAverageSuccess (embedded A) h S = ENNReal.ofReal (priorAverageSuccess (embedded A) h S).toReal :=
      (ENNReal.ofReal_toReal hfin).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      convert hrate using 1
      ring)

/-- Equation (31) for the genuine adaptive Born experiment, using the actual
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
    priorAverageSuccess (embedded A) w.weakRoot (successSection (embedded A) chiB ε) ≤
      ENNReal.ofReal (buresRateConstant C * ε * Real.sqrt ((r : ℝ) / s) *
        (1 + (n : ℝ) / ((r : ℝ) ^ 2 * s))) := by
  have hs : 0 < s := hr.trans_le hrs
  have hv : ∀ y, volume (successSection (embedded A) chiB ε y) ≤ ENNReal.ofReal
      ((buresVolumeConstant * (ε * Real.sqrt ((r : ℝ) / s)) / s) ^ (r * s)) := by
    intro y
    rw [section_volume_eq]
    have h := ChartVolume.corollary_2_5_bures V.chart r s hr hrs V.truncation V.properNull
      V.metric V.compression V.lyapunov V.brunnMinkowski V.unitaryLebesgue V.ballVolume
      V.haar V.isHaar ((embedded A).estimator.estimate y) hε hε1
    convert h using 1
    unfold buresVolumeConstant
    congr 2
    ring
  have h := success_rate_of_volume A hp hr hs Sob Coarse P U G w.weakRoot w.weakRoot_normalized
    (successSection (embedded A) chiB ε) (measurableSet_section_bures (embedded A) ε)
    buresVolumeConstant (16 * C) (ε * Real.sqrt ((r : ℝ) / s)) buresVolumeConstant_pos.le
    (by positivity) (by positivity) (Filter.Eventually.of_forall hv) hw
  simpa only [buresRateConstant, mul_assoc] using h

/-- Equation (33) for the actual adaptive learner. Full joint right-inverse
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
    priorAverageSuccess (embedded A) w.weakRoot (successSection (embedded A) chiR ε) ≤
      ENNReal.ofReal (rightRateConstant C * ((r : ℝ) * ε ^ 2 / s) *
        (1 + (n : ℝ) / ((r : ℝ) ^ 2 * s))) := by
  have hs : 0 < s := hr.trans_le hrs
  have hv : ∀ y, volume (successSection (embedded A) chiR ε y) ≤ ENNReal.ofReal
      ((rightVolumeConstant * ((r : ℝ) * ε ^ 2 / s) / s) ^ (r * s)) := by
    intro y
    rw [section_volume_eq]
    have h := ChartVolume.corollary_2_5_right V.chart r s hr hrs V.truncation V.properNull
      V.metric V.compression V.rowScaling V.ballVolume V.haar V.isHaar
      ((embedded A).estimator.estimate y) hε hε1
    convert h using 1
    unfold rightVolumeConstant
    congr 2
    ring
  exact success_rate_of_volume A hp hr hs Sob Coarse P U G w.weakRoot w.weakRoot_normalized
    (successSection (embedded A) chiR ε) (measurableSet_section_right (embedded A) ε)
    rightVolumeConstant (16 * C) ((r : ℝ) * ε ^ 2 / s) rightVolumeConstant_pos.le
    (by positivity) (by positivity) (Filter.Eventually.of_forall hv) hw

/-- The adaptive Bures lower bound on actual flat graph states. The prior
is obtained here from the raw NZ prior theorem, and all volume, information,
Born-success and scalar-extraction steps are genuinely applied. -/
theorem bures_adaptive_lower_bound
    (V : VolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s) (hrs2 : 2 ≤ r * s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hsmall : ε ≤ SampleLowerBounds.accuracyThreshold (buresRateConstant C))
    (hlearn : A.BuresSuccess r (ENNReal.ofReal ε)) :
    (1 / (3 * buresRateConstant C)) *
      ((r : ℝ) * Real.sqrt (r : ℝ) * s * Real.sqrt (s : ℝ) / ε) ≤ (n : ℝ) := by
  have hp : 3 ≤ 2 * r * s := by nlinarith
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  obtain ⟨w, hw⟩ := GraphPrior.exists_halfChart_prior hC N r s hr hrs
  have hu := bures_success_rate A V hp hr hrs Sob Coarse P U G hC w hw hε hε1
  have hl : (2 : ℝ≥0∞) / 3 ≤
      priorAverageSuccess (embedded A) w.weakRoot (successSection (embedded A) chiB ε) :=
    learnsRank_le_priorAverageSuccess (embedded A) chiB (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)
      w.weakRoot w.weakRoot_normalized (chartDomain r s) (prior_zero_off_chart w)
      ((AdaptiveCollectiveEmbedding.collectiveLearner_learnsRank_iff A _ _ _ _).2 hlearn)
  have hrate0 : 0 ≤ buresRateConstant C := (buresRateConstant_pos hC).le
  have huR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal (by positivity)] at huR
  exact SampleLowerBounds.bures_one_copy (buresRateConstant_pos hC) hrR hrsR hε hsmall
    (two_thirds_le_toReal hu hl) huR

/-- The adaptive right-inverse lower bound on actual flat graph states,
with no joint spectral-loss-measurability premise. -/
theorem right_adaptive_lower_bound
    (V : VolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s) (hrs2 : 2 ≤ r * s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hsmall : ε ≤ SampleLowerBounds.accuracyThreshold (rightRateConstant C))
    (hlearn : A.RightSuccess r (ENNReal.ofReal ε)) :
    (1 / (3 * rightRateConstant C)) * ((r : ℝ) * (s : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  have hp : 3 ≤ 2 * r * s := by nlinarith
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  obtain ⟨w, hw⟩ := GraphPrior.exists_halfChart_prior hC N r s hr hrs
  have hu := right_success_rate A V hp hr hrs Sob Coarse P U G hC w hw hε hε1
  have hl : (2 : ℝ≥0∞) / 3 ≤
      priorAverageSuccess (embedded A) w.weakRoot (successSection (embedded A) chiR ε) :=
    learnsRank_le_priorAverageSuccess (embedded A) chiR (ENNReal.ofReal ε) ((2 : ℝ≥0∞) / 3)
      w.weakRoot w.weakRoot_normalized (chartDomain r s) (prior_zero_off_chart w)
      ((AdaptiveCollectiveEmbedding.collectiveLearner_learnsRank_iff A _ _ _ _).2 hlearn)
  have hrate0 : 0 ≤ rightRateConstant C := (rightRateConstant_pos hC).le
  have huR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal (by positivity)] at huR
  exact SampleLowerBounds.right_one_copy (rightRateConstant_pos hC) hrR hrsR hε hsmall
    (two_thirds_le_toReal hu hl) huR

/-- Final flat-chart Bures adaptive sample lower bound, with one universal
accuracy threshold and no experiment-regularity or loss-measurability input. -/
theorem bures_adaptive
    (V : VolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s) (hrs2 : 2 ≤ r * s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyThreshold C)
    (hlearn : A.BuresSuccess r (ENNReal.ofReal ε)) :
    (1 / (3 * buresRateConstant C)) *
      ((r : ℝ) * Real.sqrt (r : ℝ) * s * Real.sqrt (s : ℝ) / ε) ≤ (n : ℝ) := by
  have hε1 : ε ≤ 1 / 4 := hsmall.trans (min_le_left _ _)
  have hsmallB : ε ≤ SampleLowerBounds.accuracyThreshold (buresRateConstant C) :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  exact bures_adaptive_lower_bound A V hr hrs hrs2 Sob Coarse P U G hC N hε hε1 hsmallB hlearn

/-- Final flat-chart right-inverse adaptive sample lower bound, with the
same universal small-accuracy threshold. -/
theorem right_adaptive
    (V : VolumeInputs r s) (hr : 0 < r) (hrs : r ≤ s) (hrs2 : 2 ≤ r * s)
    (Sob : TalentiH1SharpInput (2 * r * s)) (Coarse : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyThreshold C)
    (hlearn : A.RightSuccess r (ENNReal.ofReal ε)) :
    (1 / (3 * rightRateConstant C)) * ((r : ℝ) * (s : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  have hε1 : ε ≤ 1 / 4 := hsmall.trans (min_le_left _ _)
  have hsmallR : ε ≤ SampleLowerBounds.accuracyThreshold (rightRateConstant C) :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  exact right_adaptive_lower_bound A V hr hrs hrs2 Sob Coarse P U G hC N hε hε1 hsmallR hlearn

namespace Main

open CollectiveMainLowerBounds SymmetricSupport

/-- Restriction of an actual adaptive learning promise to a smaller rank. -/
theorem learnsRank_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n k r : ℕ} (A : AdaptiveModel.Learner ι Seed Ω n)
    (loss : Density ι → Density ι → ℝ≥0∞) (ε q : ℝ≥0∞)
    (hkr : k ≤ r) (hA : A.LearnsRank loss r ε q) :
    A.LearnsRank loss k ε q := by
  intro ρ hρ
  exact hA ρ (hρ.trans hkr)

variable {k : ℕ} [NeZero k]

/-- Both graph and endpoint proofs give this one reduced Bures rate. -/
theorem reduced_bures (V : RawVolumeInputs k s) (hk : 0 < k) (hks : k ≤ s)
    (An : 2 ≤ k * s → AnalysisInputs (2 * k * s))
    (P : SymmetricProjectorInput (Fin k ⊕ Fin s) n)
    (A : AdaptiveModel.Learner (Fin k ⊕ Fin s) Seed Ω n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : A.BuresSuccess k (ENNReal.ofReal ε)) :
    baseConstant C * ((k : ℝ) * Real.sqrt (k : ℝ) * s * Real.sqrt (s : ℝ) / ε) ≤ (n : ℝ) := by
  by_cases hprod : 2 ≤ k * s
  · let B := An hprod
    have hb := AdaptiveLowerBounds.bures_adaptive A V.toVolumeInputs hk hks hprod
      B.sobolev B.coarse B.product B.unique G hC N hε
      (hsmall.trans (min_le_left _ _)) hA
    exact (mul_le_mul_of_nonneg_right (baseConstant_le_chart_bures C) (by positivity)).trans hb
  · have hs : 0 < s := hk.trans_le hks
    have hmul : k * s = 1 := by have hpos := Nat.mul_pos hk hs; omega
    obtain ⟨rfl, rfl⟩ := mul_eq_one.mp hmul
    have hb := PureCollectiveLowerBounds.qubit_bures_lower V.toBuresPure P (embedded A) hε
      (hsmall.trans (min_le_right _ _))
      ((AdaptiveCollectiveEmbedding.collectiveLearner_learnsRank_iff A _ _ _ _).2 hA)
    simp only [Nat.cast_one, Real.sqrt_one, one_mul] at ⊢
    calc
      baseConstant C * (1 / ε) ≤ (1 / (18 * Real.exp 1 ^ 2)) * (1 / ε) :=
        mul_le_mul_of_nonneg_right (baseConstant_le_qubit_bures C) (by positivity)
      _ = 1 / (18 * Real.exp 1 ^ 2 * ε) := by ring
      _ ≤ (n : ℝ) := hb

/-- Both graph and endpoint proofs give this one reduced right-inverse rate. -/
theorem reduced_right (V : RawVolumeInputs k s) (hk : 0 < k) (hks : k ≤ s)
    (An : 2 ≤ k * s → AnalysisInputs (2 * k * s))
    (P : SymmetricProjectorInput (Fin k ⊕ Fin s) n)
    (A : AdaptiveModel.Learner (Fin k ⊕ Fin s) Seed Ω n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : A.RightSuccess k (ENNReal.ofReal ε)) :
    baseConstant C * ((k : ℝ) * (s : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  by_cases hprod : 2 ≤ k * s
  · let B := An hprod
    have hb := AdaptiveLowerBounds.right_adaptive A V.toVolumeInputs hk hks hprod
      B.sobolev B.coarse B.product B.unique G hC N hε
      (hsmall.trans (min_le_left _ _)) hA
    exact (mul_le_mul_of_nonneg_right (baseConstant_le_chart_right C) (by positivity)).trans hb
  · have hs : 0 < s := hk.trans_le hks
    have hmul : k * s = 1 := by have hpos := Nat.mul_pos hk hs; omega
    obtain ⟨rfl, rfl⟩ := mul_eq_one.mp hmul
    have hb := PureCollectiveLowerBounds.qubit_right_lower V.toRightPure P (embedded A) hε
      (hsmall.trans (min_le_right _ _))
      ((AdaptiveCollectiveEmbedding.collectiveLearner_learnsRank_iff A _ _ _ _).2 hA)
    simp only [Nat.cast_one, one_pow, one_mul] at ⊢
    calc
      baseConstant C * (1 / ε ^ 2) ≤ (1 / (54 * Real.exp 1 ^ 2)) * (1 / ε ^ 2) :=
        mul_le_mul_of_nonneg_right (baseConstant_le_qubit_right C) (by positivity)
      _ = 1 / (54 * Real.exp 1 ^ 2 * ε ^ 2) := by ring
      _ ≤ (n : ℝ) := hb

omit [NeZero k] in
/-- Theorem 1.2's adaptive Bures rate on the named ambient index, for
every `d ≥ 2` and `1 ≤ r ≤ d`, including the pure qubit endpoint. -/
theorem bures_adaptive {d r n : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (V : RawVolumeInputs (RankReduction.reducedRank d r) (d - RankReduction.reducedRank d r))
    (An : 2 ≤ RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r) →
      AnalysisInputs (2 * RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r)))
    (P : SymmetricProjectorInput (AmbientIndex d r) n)
    (A : AdaptiveModel.Learner (AmbientIndex d r) Seed Ω n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : A.BuresSuccess r (ENNReal.ofReal ε)) :
    sampleConstant C * ((r : ℝ) * Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε) ≤ (n : ℝ) := by
  obtain ⟨hk, hkr, hks, _, _⟩ := RankReduction.reducedRank_properties d r hd hr hrd
  letI : NeZero (RankReduction.reducedRank d r) := ⟨hk.ne'⟩
  have hlearn : A.BuresSuccess (RankReduction.reducedRank d r) (ENNReal.ofReal ε) :=
    learnsRank_mono A chiB _ _ hkr hA
  have hb := reduced_bures V hk hks An P A G hC N hε hsmall hlearn
  have hcmp := (RankReduction.compare_reduced_rates d r hd hr hrd).2.1
  calc
    sampleConstant C * ((r : ℝ) * Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε) ≤
        sampleConstant C *
          (32 * ((RankReduction.reducedRank d r : ℝ) * Real.sqrt (RankReduction.reducedRank d r : ℝ) *
            ((d - RankReduction.reducedRank d r : ℕ) : ℝ) * Real.sqrt ((d - RankReduction.reducedRank d r : ℕ) : ℝ)) / ε) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcmp hε.le)
        (sampleConstant_pos hC).le
    _ = baseConstant C * ((RankReduction.reducedRank d r : ℝ) * Real.sqrt (RankReduction.reducedRank d r : ℝ) *
        ((d - RankReduction.reducedRank d r : ℕ) : ℝ) * Real.sqrt ((d - RankReduction.reducedRank d r : ℕ) : ℝ) / ε) := by
      unfold sampleConstant
      ring
    _ ≤ (n : ℝ) := hb

omit [NeZero k] in
/-- Theorem 1.2's adaptive right-inverse rate, with the same positive
universal coefficient and accuracy threshold as the Bures rate. -/
theorem right_adaptive {d r n : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (V : RawVolumeInputs (RankReduction.reducedRank d r) (d - RankReduction.reducedRank d r))
    (An : 2 ≤ RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r) →
      AnalysisInputs (2 * RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r)))
    (P : SymmetricProjectorInput (AmbientIndex d r) n)
    (A : AdaptiveModel.Learner (AmbientIndex d r) Seed Ω n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : A.RightSuccess r (ENNReal.ofReal ε)) :
    sampleConstant C * ((r : ℝ) * (d : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) := by
  obtain ⟨hk, hkr, hks, _, _⟩ := RankReduction.reducedRank_properties d r hd hr hrd
  letI : NeZero (RankReduction.reducedRank d r) := ⟨hk.ne'⟩
  have hlearn : A.RightSuccess (RankReduction.reducedRank d r) (ENNReal.ofReal ε) :=
    learnsRank_mono A chiR _ _ hkr hA
  have hb := reduced_right V hk hks An P A G hC N hε hsmall hlearn
  have hcmp := (RankReduction.compare_reduced_rates d r hd hr hrd).2.2.2
  calc
    sampleConstant C * ((r : ℝ) * (d : ℝ) ^ 2 / ε ^ 2) ≤ sampleConstant C *
        (32 * ((RankReduction.reducedRank d r : ℝ) * ((d - RankReduction.reducedRank d r : ℕ) : ℝ) ^ 2) / ε ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcmp (sq_nonneg ε))
        (sampleConstant_pos hC).le
    _ = baseConstant C * ((RankReduction.reducedRank d r : ℝ) * ((d - RankReduction.reducedRank d r : ℕ) : ℝ) ^ 2 / ε ^ 2) := by
      unfold sampleConstant
      ring
    _ ≤ (n : ℝ) := hb

end Main

end Paper26.AdaptiveLowerBounds
