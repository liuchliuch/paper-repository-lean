import Paper26.OneCopyNormalized
import Paper26.OneCopyProductProtocol
import Paper26.FrobeniusLearning
import Paper26.LossMeasurability

/-!
# The actual one-copy right-inverse upper bound (Eq. 12)

A single fixed covariant one-copy POVM is repeated on fresh copies. The common
measurable water-filled reconstruction is isotropically regularized. Native
matrix regularization transfers the proved Frobenius event to the actual
QuantumModel.chiR event, and the actual adaptive/operator protocols have the
proved product Born law. No statistical upper bound is an external input.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory
namespace Paper26.OneCopyRightUpper
open QuantumModel ContinuousPOVM OneCopyObservation OneCopySubmatrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Accuracy required by the native epsilon/8 matrix regularization theorem. -/
def frobeniusAccuracy (ε : ℝ) : ℝ := ε^2/(64*(Fintype.card ι:ℝ))

lemma accuracy_pos {ε : ℝ} (hε : 0 < ε) : 0 < frobeniusAccuracy (ι:=ι) ε := by
  unfold frobeniusAccuracy
  have hd : (0:ℝ)<Fintype.card ι := by exact_mod_cast Fintype.card_pos (α:=ι)
  positivity

lemma accuracy_lt_one {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    frobeniusAccuracy (ι:=ι) ε < 1 := by
  have hd : (1:ℝ)≤Fintype.card ι := by exact_mod_cast Fintype.card_pos (α:=ι)
  unfold frobeniusAccuracy
  apply (div_lt_iff₀ (by positivity : 0 < 64*(Fintype.card ι:ℝ))).mpr
  nlinarith

def regularizedEstimator {Ω : Type*} [MeasurableSpace Ω] (T : Estimator ι Ω)
    (ε : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1) : Estimator ι Ω where
  estimate := fun z => FrobeniusLearning.regularizedDensity (ε/8) (by positivity) (by linarith) (T.estimate z)
  measurable_estimate := (FrobeniusLearning.measurable_regularizedDensity (ε/8) (by positivity)
    (by linarith)).comp T.measurable_estimate

lemma regularization_success (ρ τ : Density ι) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (herr : ShellAccounting.frobeniusSq (τ.matrix-ρ.matrix) ≤ frobeniusAccuracy (ι:=ι) ε) :
    chiR ρ (FrobeniusLearning.regularizedDensity (ε/8) (by positivity) (by linarith) τ) ≤ ENNReal.ofReal ε := by
  have hf : SpectralLoss.frobeniusSq (ρ.matrix-τ.matrix) ≤ ε^2/(64*(Fintype.card ι:ℝ)) := by
    rw [Regularization.frobeniusSq_eq_entryNorm]
    have he : ShellAccounting.frobeniusSq (ρ.matrix-τ.matrix) =
        ShellAccounting.frobeniusSq (τ.matrix-ρ.matrix) := by
      unfold ShellAccounting.frobeniusSq
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.sub_apply, norm_sub_rev]
    rw [he]
    exact herr
  let σ := FrobeniusLearning.regularizedDensity (ε/8) (by positivity) (by linarith : ε/8<1) τ
  have hσ : σ.matrix.PosDef := Regularization.regularize_posDef _ τ.positive (by positivity) (by linarith)
  change chiR ρ σ ≤ _
  rw [PositiveLossBridge.chiR_eq_standardRightEnergy ρ σ hσ]
  exact ENNReal.ofReal_le_ofReal (Regularization.regularization_epsilon _ _ ρ.hermitian τ.positive τ.trace_one hε hε₁ hf)

lemma logarithm_budget {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) :
    0 ≤ Real.log (2*(Fintype.card ι:ℝ)/δ) ∧
      Real.log (2*(Fintype.card ι:ℝ)/(δ/2)) ≤ 2*Real.log (2*(Fintype.card ι:ℝ)/δ) := by
  have hd : (1:ℝ)≤Fintype.card ι := by exact_mod_cast Fintype.card_pos (α:=ι)
  have hx : 2 ≤ 2*(Fintype.card ι:ℝ)/δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  have hx₀ : 0 < 2*(Fintype.card ι:ℝ)/δ := by positivity
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<2) hx
  constructor
  · exact Real.log_nonneg (by linarith)
  · have he : 2*(Fintype.card ι:ℝ)/(δ/2) = 2*(2*(Fintype.card ι:ℝ)/δ) := by ring
    rw [he, Real.log_mul (by norm_num) (ne_of_gt hx₀)]
    linarith

/-- Simplification of both actual Frobenius copy terms at η=ε²/(64d).
The deliberately loose absolute constant avoids any asymptotic assumptions. -/
lemma cost_simplify (s r : ℕ) (hs : 0 < s) (hsr : s ≤ r) {ε δ : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hδ₁ : δ < 1) :
    72*((s:ℝ)*Fintype.card ι/frobeniusAccuracy (ι:=ι) ε +
      Fintype.card ι*Real.sqrt ((s:ℝ)/frobeniusAccuracy (ι:=ι) ε))*
        Real.log (2*(Fintype.card ι:ℝ)/(δ/2)) ≤
      18432*(r:ℝ)*(Fintype.card ι:ℝ)^2/ε^2*Real.log (2*(Fintype.card ι:ℝ)/δ) := by
  have hη := accuracy_pos (ι:=ι) hε
  have hη₁ := accuracy_lt_one (ι:=ι) hε hε₁
  have hs₁ : (1:ℝ)≤s := by exact_mod_cast hs
  have hsrℝ : (s:ℝ)≤r := by exact_mod_cast hsr
  have hx : 1 ≤ (s:ℝ)/frobeniusAccuracy (ι:=ι) ε := (le_div_iff₀ hη).mpr (by nlinarith)
  have hsq := Real.sq_sqrt (show 0 ≤ (s:ℝ)/frobeniusAccuracy (ι:=ι) ε by positivity)
  have hsqrt : Real.sqrt ((s:ℝ)/frobeniusAccuracy (ι:=ι) ε) ≤ (s:ℝ)/frobeniusAccuracy (ι:=ι) ε := by
    nlinarith [sq_nonneg (Real.sqrt ((s:ℝ)/frobeniusAccuracy (ι:=ι) ε)-1)]
  have hterm : (s:ℝ)*Fintype.card ι/frobeniusAccuracy (ι:=ι) ε +
      Fintype.card ι*Real.sqrt ((s:ℝ)/frobeniusAccuracy (ι:=ι) ε) ≤
        128*(r:ℝ)*(Fintype.card ι:ℝ)^2/ε^2 := by
    have hm := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ (Fintype.card ι:ℝ) by positivity)
    have hcomm : (Fintype.card ι:ℝ)*((s:ℝ)/frobeniusAccuracy (ι:=ι) ε) =
        (s:ℝ)*Fintype.card ι/frobeniusAccuracy (ι:=ι) ε := by ring
    rw [hcomm] at hm
    have he : 2*((s:ℝ)*Fintype.card ι/frobeniusAccuracy (ι:=ι) ε) =
        128*(s:ℝ)*(Fintype.card ι:ℝ)^2/ε^2 := by unfold frobeniusAccuracy; field_simp; ring
    calc
      _ ≤ 2*((s:ℝ)*Fintype.card ι/frobeniusAccuracy (ι:=ι) ε) := by nlinarith [hm]
      _ = _ := he
      _ ≤ 128*(r:ℝ)*(Fintype.card ι:ℝ)^2/ε^2 := by gcongr
  have hl := logarithm_budget (ι:=ι) hδ hδ₁
  have hlβ : 0 ≤ Real.log (2*(Fintype.card ι:ℝ)/(δ/2)) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ (by positivity : 0 < δ/2)).mpr (by
      have hd : (1:ℝ)≤Fintype.card ι := by exact_mod_cast Fintype.card_pos (α:=ι)
      nlinarith)
  calc
    _ ≤ 72*(128*(r:ℝ)*(Fintype.card ι:ℝ)^2/ε^2)*
        (2*Real.log (2*(Fintype.card ι:ℝ)/δ)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hterm (by norm_num)) hl.2 hlβ (by positivity)
    _ = _ := by ring

/-- One common actual regularized tuple estimator succeeds on all promised
states, under the actual fixed one-copy POVM's product Born law. -/
theorem exists_product_routine (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ] (H : HaarCoordinateMoments μ)
    (r : ℕ) (hr : 0 < r) {ε δ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ (N : ℕ) (T : Estimator ι (Fin N → Outcome ι)),
      (N:ℝ) < 18432*(r:ℝ)*(Fintype.card ι:ℝ)^2/ε^2*Real.log (2*(Fintype.card ι:ℝ)/δ) ∧
      ∀ ρ : Density ι, ρ.matrix.rank ≤ r →
        MeasurableSet (OneCopyProductProtocol.sampleSuccessSet T chiR ρ (ENNReal.ofReal ε)) ∧
        ENNReal.ofReal (1-δ) ≤ OneCopyProductProtocol.sampleMeasure (OneCopyNormalized.fullMeasurement μ H) ρ N
          (OneCopyProductProtocol.sampleSuccessSet T chiR ρ (ENNReal.ofReal ε)) := by
  obtain ⟨N,T,_,_,hcost,hT⟩ := OneCopyNormalized.uniform_normalized_routine B Weyl S μ H r hr
    (frobeniusAccuracy (ι:=ι) ε) (δ/2) (accuracy_pos hε) (accuracy_lt_one hε hε₁) (by positivity) (by linarith)
  let U := regularizedEstimator T ε hε hε₁
  refine ⟨N,U,?_,?_⟩
  · have hs : 0 < min r (Fintype.card ι) := lt_min hr Fintype.card_pos
    have hc := cost_simplify (ι:=ι) (min r (Fintype.card ι)) r hs (min_le_left _ _) hε hε₁ hδ hδ₁
    apply hcost.trans_le
    simpa only [Nat.cast_min] using hc
  · intro ρ hρ
    refine ⟨LossMeasurability.measurableSet_chiR_success (fun _ => ρ) U.estimate measurable_const U.measurable_estimate _, ?_⟩
    have hp := (hT ρ hρ).2
    have hδβ : ENNReal.ofReal (1-δ) ≤ ENNReal.ofReal (1-δ/2) := ENNReal.ofReal_le_ofReal (by linarith)
    apply (hδβ.trans hp).trans
    apply measure_mono
    intro z hz
    exact regularization_success ρ (T.estimate z) hε hε₁ hz

/-- Equation (12) as a genuine N-round adaptive learner on fresh copies. -/
theorem eq_12_adaptive (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ] (H : HaarCoordinateMoments μ)
    (r : ℕ) (hr : 0 < r) {ε δ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ (N : ℕ) (A : AdaptiveModel.Learner ι PUnit (Outcome ι) N),
      (N:ℝ) < 18432*(r:ℝ)*(Fintype.card ι:ℝ)^2/ε^2*Real.log (2*(Fintype.card ι:ℝ)/δ) ∧
      A.LearnsRank chiR r (ENNReal.ofReal ε) (ENNReal.ofReal (1-δ)) := by
  obtain ⟨N,T,hN,hT⟩ := exists_product_routine B Weyl S μ H r hr hε hε₁ hδ hδ₁
  refine ⟨N,OneCopyProductProtocol.learner (OneCopyNormalized.fullMeasurement μ H) T,hN,?_⟩
  exact (OneCopyProductProtocol.learner_learnsRank_iff _ T chiR r _ _).mpr hT

/-- The same statistical guarantee in the original raw operator-valued
one-copy protocol, for every ordinary fixed-space RN witness. -/
theorem eq_12_operator (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ] (H : HaarCoordinateMoments μ)
    (RN : CollectiveModel.OperatorRadonNikodymInput ι (Outcome ι))
    (r : ℕ) (hr : 0 < r) {ε δ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ (N : ℕ) (A : AdaptiveOperatorModelTransport.OperatorLearner ι PUnit (Outcome ι) N),
      (N:ℝ) < 18432*(r:ℝ)*(Fintype.card ι:ℝ)^2/ε^2*Real.log (2*(Fintype.card ι:ℝ)/δ) ∧
      A.LearnsRank RN chiR r (ENNReal.ofReal ε) (ENNReal.ofReal (1-δ)) := by
  obtain ⟨N,T,hN,hT⟩ := exists_product_routine B Weyl S μ H r hr hε hε₁ hδ hδ₁
  refine ⟨N,OneCopyProductProtocol.operatorLearner (OneCopyNormalized.fullMeasurement μ H) T,hN,?_⟩
  exact OneCopyProductProtocol.operatorLearner_learnsRank _ T RN chiR r _ _ hT

/-- Actual source achievability at confidence 2/3 with one common raw protocol. -/
theorem source_adaptiveAchievable (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ] (H : HaarCoordinateMoments μ)
    (RN : SourceCopyComplexity.AllFixedOperatorRN ι) (r : ℕ) (hr : 0 < r)
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ N : ℕ, (N:ℝ) < 18432*(r:ℝ)*(Fintype.card ι:ℝ)^2/ε^2*Real.log (6*(Fintype.card ι:ℝ)) ∧
      SourceCopyComplexity.adaptiveAchievable RN chiR r (ENNReal.ofReal ε) N := by
  obtain ⟨N,T,hN,hT⟩ := exists_product_routine B Weyl S μ H r hr hε hε₁
    (by norm_num : (0:ℝ)<1/3) (by norm_num : (1/3:ℝ)<1)
  refine ⟨N,?_,OneCopyProductProtocol.adaptiveAchievable (OneCopyNormalized.fullMeasurement μ H) T RN chiR r _ ?_⟩
  · have he : 2*(Fintype.card ι:ℝ)/(1/3:ℝ) = 6*(Fintype.card ι:ℝ) := by ring
    simpa only [he] using hN
  · intro ρ hρ
    refine ⟨(hT ρ hρ).1,?_⟩
    have he : ENNReal.ofReal (1-(1/3:ℝ)) = (2:ℝ≥0∞)/3 := by
      rw [show (1-(1/3:ℝ)) = 2/3 by norm_num, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3)]
      norm_num
    simpa only [he] using (hT ρ hρ).2

/-- Source Eq. (12) as an upper bound on the original raw one-copy minimum,
with the ordinary RN theorem used only to name the actual Born measures. -/
theorem source_Nonecopy_upper (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{0,0})
    (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ] (H : HaarCoordinateMoments μ)
    (RN : SourceCopyComplexity.AllFixedOperatorRN ι) (r : ℕ) (hr : 0 < r)
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    SourceCopyComplexity.Nonecopy RN chiR r (ENNReal.ofReal ε) ≤
      ENNReal.ofReal (18432*(r:ℝ)*(Fintype.card ι:ℝ)^2/ε^2*Real.log (6*(Fintype.card ι:ℝ))) := by
  obtain ⟨N,hN,hA⟩ := source_adaptiveAchievable B Weyl S μ H RN r hr hε hε₁
  calc
    _ ≤ (N:ℝ≥0∞) := CopyComplexity.minimumCopies_le hA
    _ ≤ _ := by
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (le_of_lt hN)

end Paper26.OneCopyRightUpper
