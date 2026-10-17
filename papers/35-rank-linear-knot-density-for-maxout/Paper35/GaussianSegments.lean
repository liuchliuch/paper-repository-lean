import Paper35.GaussianArc
import Paper35.GaussianLift
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace Paper35.GaussianMarked

theorem segment_hasDerivAt {m : ℕ} (a b : Source.Space m) (t : ℝ) :
    HasDerivAt (segment a b) (b-a) t := by
  have h := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).smul_const a).add
    ((hasDerivAt_id t).smul_const b)
  simpa only [zero_sub, one_smul, neg_smul, neg_add_eq_sub, segment] using h

theorem segment_lipschitz {m : ℕ} (a b : Source.Space m) (L : ℝ) :
    LipschitzOnWith ‖b-a‖₊ (segment a b) (Icc 0 L) := by
  exact Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Icc 0 L)
    (fun t _ => (segment_hasDerivAt a b t).hasDerivWithinAt) (fun _ _ => le_rfl)

theorem normalized_segment_AC {m : ℕ} (a b : Source.Space m)
    (hnz : ∀ t ∈ Icc (0:ℝ) 1, segment a b t ≠ 0) :
    AbsolutelyContinuousOnInterval (fun t => Gaussian.normalize (segment a b t)) 0 1 := by
  obtain ⟨C,hC⟩ := GaussianLift.normalized_lipschitzOn (by norm_num : (0:ℝ)≤1)
    (segment_lipschitz a b 1) hnz
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
  simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hC

/-- Corollary 6.3 for an actual affine lifted segment, with an arbitrary common
mean. All count transportation and the minor-arc geometry are proved. -/
theorem gaussian_segment_expectedSwitchCount
    (hcrofton : ClassicalCroftonLaw) (hregular : ClassicalCroftonRegularityLaw)
    (hproj : GaussianUnitProjectionLaw) (hrot : GaussianPairReconstructionLaw)
    (hmax : GaussianMaxIntegralLaw) (hlength : ACCurveLengthLaw)
    (m n : ℕ) (hm : 1 ≤ m) (a b : Source.Space m) (mean : ℝ → ℝ)
    (hnz : ∀ t ∈ Icc (0:ℝ) 1, segment a b t ≠ 0)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter 1)) :
    expectedSwitchCount (gaussianIid m (n+2))
      (fun Z j t => mean t + inner ℝ (Z j) (segment a b t)) 1 =
      ENNReal.ofReal (Paper35.gaussianRankCoefficient (n+2) *
        Real.arccos (inner ℝ a b/(‖a‖*‖b‖))) := by
  have hcount (Z : Fin (n+2) → Source.Space m) :
      switchCount (fun j t => mean t + inner ℝ (Z j) (segment a b t)) 1 =
        switchCount (gaussianScores (fun t => Gaussian.normalize (segment a b t)) Z) 1 := by
    unfold switchCount
    congr 2
    exact Gaussian.covarianceLift_switchSet_on Z (segment a b) mean 1
      (fun t ht => hnz t ⟨ht.1.le,ht.2.le⟩)
  unfold expectedSwitchCount
  simp_rw [hcount]
  change expectedSwitchCount (gaussianIid m (n+2))
    (gaussianScores (fun t => Gaussian.normalize (segment a b t))) 1 = _
  rw [gaussian_upper_envelope_all_dimensions hcrofton hregular hproj hrot hmax hlength
    m n hm 1 (by norm_num) _ (normalized_segment_AC a b hnz)
    (fun t ht => Gaussian.normalize_norm _ (hnz t ht)) hLN,
    normalized_segment_variation hlength a b hnz,
    ← ENNReal.ofReal_mul (Paper35.gaussianRankCoefficient_nonneg (n+2))]

/-- Actual segment count is measurable under its iid Gaussian coefficient law. -/
theorem aemeasurable_gaussian_segment_count
    (hregular : ClassicalCroftonRegularityLaw) (hrot : GaussianPairReconstructionLaw)
    (m n : ℕ) (hm : 1 ≤ m) (a b : Source.Space m) (mean : ℝ → ℝ)
    (hnz : ∀ t ∈ Icc (0:ℝ) 1, segment a b t ≠ 0)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter 1)) :
    AEMeasurable (fun Z => switchCount
      (fun j t => mean t + inner ℝ (Z j) (segment a b t)) 1) (gaussianIid m (n+2)) := by
  have hcount (Z : Fin (n+2) → Source.Space m) :
      switchCount (fun j t => mean t + inner ℝ (Z j) (segment a b t)) 1 =
        switchCount (gaussianScores (fun t => Gaussian.normalize (segment a b t)) Z) 1 := by
    unfold switchCount
    congr 2
    exact Gaussian.covarianceLift_switchSet_on Z (segment a b) mean 1
      (fun t ht => hnz t ⟨ht.1.le,ht.2.le⟩)
  simp_rw [hcount]
  exact aemeasurable_iid_switchCount_all_dimensions hrot hregular m n hm 1 (by norm_num)
    _ (normalized_segment_AC a b hnz) (fun t ht => Gaussian.normalize_norm _ (hnz t ht)) hLN
end Paper35.GaussianMarked
