import Paper35.GaussianWholeLine
import Paper35.GaussianLaw
import Mathlib.Tactic.FinCases
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace Paper35.GaussianLift
open Source GaussianMarked

theorem covarianceForm_pos_of_posDef {m : ℕ} (Ω : Matrix (Fin m) (Fin m) ℝ)
    (hΩ : Ω.PosDef) (q : Space m) (hq : q ≠ 0) : 0 < covarianceForm Ω q := by
  have hq' : (WithLp.ofLp q : Fin m → ℝ) ≠ 0 := by
    intro h
    apply hq
    exact WithLp.ofLp_injective 2 h
  simpa only [covarianceForm,EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toEuclideanLin_apply,WithLp.ofLp_toLp,RCLike.re_to_real,dotProduct_comm] using hΩ.re_dotProduct_pos hq'

theorem rootMap_injective_of_posDef {m : ℕ} (Ω : Matrix (Fin m) (Fin m) ℝ)
    (hΩ : Ω.PosDef) : Function.Injective (rootMap Ω) := by
  intro x y hxy
  by_contra hne
  have hp := rootMap_ne_zero Ω hΩ.posSemidef (x-y)
    (covarianceForm_pos_of_posDef Ω hΩ (x-y) (sub_ne_zero.mpr hne))
  apply hp
  rw [map_sub,hxy,sub_self]

def affineSample {m K : ℕ} (g : Model m) (Z : Fin K → Space m) : Fin K → Space m :=
  fun j => g.mean+rootMap g.covariance (Z j)

theorem measurableEmbedding_affineSample {m K : ℕ} (g : Model m)
    (hΩ : g.covariance.PosDef) : MeasurableEmbedding (affineSample (K := K) g) := by
  have hc : Continuous (affineSample (K := K) g) := by
    apply continuous_pi
    intro j
    exact continuous_const.add ((rootMap g.covariance).continuous.comp (continuous_apply j))
  apply hc.measurableEmbedding
  intro Z W h
  funext j
  exact rootMap_injective_of_posDef g.covariance hΩ
    (add_left_cancel (congrFun h j))

def lineFeature (t : ℝ) : Space 2 := WithLp.toLp 2 ![t,1]
def lineOffset : Space 2 := WithLp.toLp 2 ![0,1]
def lineDirection : Space 2 := WithLp.toLp 2 ![1,0]

theorem lineFeature_eq (t : ℝ) : lineFeature t = lineOffset+t•lineDirection := by
  ext i
  fin_cases i <;> simp [lineFeature,lineOffset,lineDirection]

theorem lineFeature_ne_zero (t : ℝ) : lineFeature t ≠ 0 := by
  intro h
  have hh := congrArg (fun x : Space 2 => x 1) h
  norm_num [lineFeature] at hh

theorem lineDirection_ne_zero : lineDirection ≠ 0 := by
  intro h
  have hh := congrArg (fun x : Space 2 => x 0) h
  norm_num [lineDirection] at hh

/-- Actual slope/intercept scores A_j t+B_j of jointly Gaussian pairs. -/
def lineScores {K : ℕ} (θ : Fin K → Space 2) : Fin K → ℝ → ℝ :=
  fun j t => θ j 0*t+θ j 1

theorem lineScores_eq_inner {K : ℕ} (θ : Fin K → Space 2) (j : Fin K) (t : ℝ) :
    lineScores θ j t = inner ℝ (θ j) (lineFeature t) := by
  simp [lineScores,lineFeature,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,mul_comm]

theorem lineScores_affineSample {K : ℕ} (g : Model 2) (Z : Fin K → Space 2) :
    lineScores (affineSample g Z) = fun j t => inner ℝ g.mean (lineFeature t)+
      inner ℝ (Z j) (lineCurve (rootMap g.covariance lineOffset)
        (rootMap g.covariance lineDirection) t) := by
  funext j t
  rw [lineScores_eq_inner,affineSample,inner_add_left]
  congr 1
  calc
    _ = inner ℝ (Z j) (rootMap g.covariance (lineFeature t)) := rootMap_symmetric g.covariance _ _
    _ = _ := by
      rw [lineFeature_eq,map_add,map_smul]
      rfl

theorem root_line_nonzero (g : Model 2) (hΩ : g.covariance.PosDef) (t : ℝ) :
    lineCurve (rootMap g.covariance lineOffset) (rootMap g.covariance lineDirection) t ≠ 0 := by
  have heq : lineCurve (rootMap g.covariance lineOffset) (rootMap g.covariance lineDirection) t =
      rootMap g.covariance (lineFeature t) := by
    rw [lineFeature_eq,map_add,map_smul]
    rfl
  rw [heq]
  exact rootMap_ne_zero g.covariance g.covariance_psd _
    (covarianceForm_pos_of_posDef g.covariance hΩ _ (lineFeature_ne_zero t))

/-- Formula (7.8) with the original full jointly Gaussian slope/intercept law:
arbitrary pair mean, every positive definite 2×2 covariance, actual global
switch count, and iid candidates. -/
theorem jointlyGaussian_whole_line_7_8
    (hrep : GaussianRepresentationLaw) (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmax : GaussianMaxIntegralLaw)
    (hlength : ACCurveLengthLaw) (g : Model 2) (hΩ : g.covariance.PosDef) (n : ℕ)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample 2 n) (CurveParameter 1)) :
    (∫⁻ θ, wholeSwitchCount (lineScores θ) ∂g.sampleLaw (n+2)) =
      ENNReal.ofReal (Real.sqrt Real.pi*Paper35.gaussianMaxMean (n+2)) := by
  have hpres : MeasurePreserving (affineSample (K := n+2) g)
      (gaussianIid 2 (n+2)) (g.sampleLaw (n+2)) := by
    refine ⟨(measurableEmbedding_affineSample g hΩ).measurable,?_⟩
    exact (g.sampleLaw_eq_map hrep (n+2)).symm
  rw [← hpres.lintegral_comp_emb (measurableEmbedding_affineSample g hΩ)]
  simp only [lineScores_affineSample]
  apply gaussian_whole_line_formula_7_8 hcrofton hregular hproj hrot hmax hlength
    2 n (by norm_num) _ _ _ _ (root_line_nonzero g hΩ) hLN
  exact rootMap_ne_zero g.covariance g.covariance_psd _
    (covarianceForm_pos_of_posDef g.covariance hΩ _ lineDirection_ne_zero)

theorem aemeasurable_jointlyGaussian_whole_count
    (hrep : GaussianRepresentationLaw) (hregular : ClassicalCroftonRegularityLaw)
    (hrot : GaussianPairReconstructionLaw) (g : Model 2) (hΩ : g.covariance.PosDef) (n : ℕ)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample 2 n) (CurveParameter 1)) :
    AEMeasurable (fun θ => wholeSwitchCount (lineScores θ)) (g.sampleLaw (n+2)) := by
  rw [g.sampleLaw_eq_map hrep (n+2)]
  apply (measurableEmbedding_affineSample g hΩ).aemeasurable_map_iff.mpr
  simp only [Function.comp_def,lineScores_affineSample]
  exact aemeasurable_gaussian_whole_count hregular hrot 2 n (by norm_num)
    _ _ _ (root_line_nonzero g hΩ) hLN

theorem jointlyGaussian_window_count
    (hrep : GaussianRepresentationLaw) (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmax : GaussianMaxIntegralLaw)
    (hlength : ACCurveLengthLaw) (g : Model 2) (hΩ : g.covariance.PosDef) (n : ℕ)
    (R : ℝ) (hR : 0 < R)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample 2 n) (CurveParameter 1)) :
    (∫⁻ θ, ((switchWindow (lineScores θ) R).encard : ℝ≥0∞) ∂g.sampleLaw (n+2)) =
      ENNReal.ofReal (Paper35.gaussianRankCoefficient (n+2)*Real.arccos
        (inner ℝ (rootMap g.covariance lineOffset-R•rootMap g.covariance lineDirection)
          (rootMap g.covariance lineOffset+R•rootMap g.covariance lineDirection)/
        (‖rootMap g.covariance lineOffset-R•rootMap g.covariance lineDirection‖*
          ‖rootMap g.covariance lineOffset+R•rootMap g.covariance lineDirection‖))) := by
  have hpres : MeasurePreserving (affineSample (K := n+2) g)
      (gaussianIid 2 (n+2)) (g.sampleLaw (n+2)) := by
    refine ⟨(measurableEmbedding_affineSample g hΩ).measurable,?_⟩
    exact (g.sampleLaw_eq_map hrep (n+2)).symm
  rw [← hpres.lintegral_comp_emb (measurableEmbedding_affineSample g hΩ)]
  simp only [lineScores_affineSample]
  exact gaussian_window_expectedCount hcrofton hregular hproj hrot hmax hlength
    2 n (by norm_num) _ _ _ (root_line_nonzero g hΩ) R hR hLN

/-- Every bounded nonempty symmetric interval has strictly fewer expected
switches than the whole line, with the original positive definite pair law. -/
theorem jointlyGaussian_window_count_lt_whole
    (hrep : GaussianRepresentationLaw) (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmax : GaussianMaxIntegralLaw)
    (hlength : ACCurveLengthLaw) (g : Model 2) (hΩ : g.covariance.PosDef) (n : ℕ)
    (R : ℝ) (hR : 0 < R)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample 2 n) (CurveParameter 1)) :
    (∫⁻ θ, ((switchWindow (lineScores θ) R).encard : ℝ≥0∞) ∂g.sampleLaw (n+2)) <
      ∫⁻ θ, wholeSwitchCount (lineScores θ) ∂g.sampleLaw (n+2) := by
  let a := rootMap g.covariance lineOffset
  let b := rootMap g.covariance lineDirection
  have hpres : MeasurePreserving (affineSample (K := n+2) g)
      (gaussianIid 2 (n+2)) (g.sampleLaw (n+2)) := by
    refine ⟨(measurableEmbedding_affineSample g hΩ).measurable,?_⟩
    exact (g.sampleLaw_eq_map hrep (n+2)).symm
  rw [← hpres.lintegral_comp_emb (measurableEmbedding_affineSample g hΩ),
      ← hpres.lintegral_comp_emb (measurableEmbedding_affineSample g hΩ)]
  simp only [lineScores_affineSample]
  rw [gaussian_window_expectedCount hcrofton hregular hproj hrot hmax hlength
      2 n (by norm_num) a b _ (root_line_nonzero g hΩ) R hR hLN,
    gaussian_whole_line_expectedCount hcrofton hregular hproj hrot hmax hlength
      2 n (by norm_num) a b
      (rootMap_ne_zero g.covariance g.covariance_psd _
        (covarianceForm_pos_of_posDef g.covariance hΩ _ lineDirection_ne_zero))
      _ (root_line_nonzero g hΩ) hLN]
  apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos
    (Paper35.gaussianRankCoefficient_pos (by omega : 2≤n+2)) Real.pi_pos)).mpr
  apply mul_lt_mul_of_pos_left _ (Paper35.gaussianRankCoefficient_pos (by omega : 2≤n+2))
  exact Gaussian.angle_lt_pi_of_segment_nonzero (a-R•b) (a+R•b)
    (line_segment_nonzero a b (root_line_nonzero g hΩ) R)

def intervalSwitchCount {K : ℕ} (f : Fin K → ℝ → ℝ) (a b : ℝ) : ℝ≥0∞ :=
  (globalSwitchSet f ∩ Ioo a b).encard

theorem jointlyGaussian_interval_count_lt_whole
    (hrep : GaussianRepresentationLaw) (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmax : GaussianMaxIntegralLaw)
    (hlength : ACCurveLengthLaw) (g : Model 2) (hΩ : g.covariance.PosDef) (n : ℕ)
    (a b : ℝ)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample 2 n) (CurveParameter 1)) :
    (∫⁻ θ, intervalSwitchCount (lineScores θ) a b ∂g.sampleLaw (n+2)) <
      ∫⁻ θ, wholeSwitchCount (lineScores θ) ∂g.sampleLaw (n+2) := by
  let R := |a|+|b|+1
  have hR : 0 < R := by dsimp [R]; positivity
  apply lt_of_le_of_lt _ (jointlyGaussian_window_count_lt_whole hrep hcrofton hregular hproj hrot
    hmax hlength g hΩ n R hR hLN)
  apply lintegral_mono
  intro θ
  apply ENat.toENNReal_mono
  apply Set.encard_mono
  rintro s ⟨hs,ha,hb⟩
  refine ⟨hs,?_,?_⟩
  · dsimp [R]
    linarith [neg_abs_le a,abs_nonneg b]
  · dsimp [R]
    linarith [le_abs_self b,abs_nonneg a]

theorem aemeasurable_jointlyGaussian_window_count
    (hrep : GaussianRepresentationLaw) (hregular : ClassicalCroftonRegularityLaw)
    (hrot : GaussianPairReconstructionLaw) (g : Model 2) (hΩ : g.covariance.PosDef) (n : ℕ)
    (R : ℝ) (hR : 0 < R)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample 2 n) (CurveParameter 1)) :
    AEMeasurable (fun θ => ((switchWindow (lineScores θ) R).encard : ℝ≥0∞))
      (g.sampleLaw (n+2)) := by
  rw [g.sampleLaw_eq_map hrep (n+2)]
  apply (measurableEmbedding_affineSample g hΩ).aemeasurable_map_iff.mpr
  simp only [Function.comp_def,lineScores_affineSample]
  exact aemeasurable_gaussian_window_count hregular hrot 2 n (by norm_num)
    _ _ _ (root_line_nonzero g hΩ) R hR hLN

theorem jointlyGaussian_whole_count_eq_iSup_windows
    (hrep : GaussianRepresentationLaw) (hregular : ClassicalCroftonRegularityLaw)
    (hrot : GaussianPairReconstructionLaw) (g : Model 2) (hΩ : g.covariance.PosDef) (n : ℕ)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample 2 n) (CurveParameter 1)) :
    (∫⁻ θ, wholeSwitchCount (lineScores θ) ∂g.sampleLaw (n+2)) =
      ⨆ k : ℕ, ∫⁻ θ, ((switchWindow (lineScores θ) (windowRadius k)).encard : ℝ≥0∞)
        ∂g.sampleLaw (n+2) := by
  simp only [wholeSwitchCount_eq_iSup]
  apply lintegral_iSup'
  · intro k
    exact aemeasurable_jointlyGaussian_window_count hrep hregular hrot g hΩ n
      (windowRadius k) (by dsimp [windowRadius]; positivity) hLN
  · exact Filter.Eventually.of_forall (fun θ j k hjk =>
      ENat.toENNReal_mono (Set.encard_mono (switchWindow_monotone (lineScores θ) hjk)))

/-- The exact supremum over all bounded intervals, in the original Gaussian
slope/intercept model, agrees with (7.8). -/
theorem jointlyGaussian_interval_supremum_7_8
    (hrep : GaussianRepresentationLaw) (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmax : GaussianMaxIntegralLaw)
    (hlength : ACCurveLengthLaw) (g : Model 2) (hΩ : g.covariance.PosDef) (n : ℕ)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample 2 n) (CurveParameter 1)) :
    (⨆ a : ℝ, ⨆ b : ℝ, ∫⁻ θ, intervalSwitchCount (lineScores θ) a b ∂g.sampleLaw (n+2)) =
      ENNReal.ofReal (Real.sqrt Real.pi*Paper35.gaussianMaxMean (n+2)) := by
  rw [← jointlyGaussian_whole_line_7_8 hrep hcrofton hregular hproj hrot hmax hlength g hΩ n hLN]
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro b
    apply lintegral_mono
    intro θ
    exact ENat.toENNReal_mono (Set.encard_mono inter_subset_left)
  · rw [jointlyGaussian_whole_count_eq_iSup_windows hrep hregular hrot g hΩ n hLN]
    apply iSup_le
    intro k
    exact le_iSup_of_le (-windowRadius k) (le_iSup_of_le (windowRadius k) le_rfl)
end Paper35.GaussianLift
