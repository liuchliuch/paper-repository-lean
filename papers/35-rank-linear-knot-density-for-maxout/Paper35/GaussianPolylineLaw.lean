import Paper35.GaussianPolyline
import Paper35.GaussianLaw
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace Paper35.GaussianLift
open Source GaussianMarked

/-- The actual covariance kernel qᵀΩr in the endpoint formula. -/
def covarianceKernel {m : ℕ} (Ω : Matrix (Fin m) (Fin m) ℝ) (q r : Space m) : ℝ :=
  inner ℝ q (Matrix.toEuclideanLin Ω r)

theorem inner_rootMap {m : ℕ} (Ω : Matrix (Fin m) (Fin m) ℝ) (hΩ : Ω.PosSemidef)
    (q r : Space m) : inner ℝ (rootMap Ω q) (rootMap Ω r) = covarianceKernel Ω q r := by
  calc
    _ = inner ℝ q (rootMap Ω (rootMap Ω r)) := rootMap_symmetric Ω _ _
    _ = _ := by rw [rootMap_sq Ω hΩ]; rfl

theorem norm_rootMap_eq_sqrt_covarianceForm {m : ℕ}
    (Ω : Matrix (Fin m) (Fin m) ℝ) (hΩ : Ω.PosSemidef) (q : Space m) :
    ‖rootMap Ω q‖ = Real.sqrt (covarianceForm Ω q) := by
  rw [← norm_rootMap_sq Ω hΩ q,Real.sqrt_sq (norm_nonneg _)]

theorem feature_segment {d : ℕ} (a b : Space d) (r : ℝ) :
    feature (GaussianMarked.segment a b r) = GaussianMarked.segment (feature a) (feature b) r := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [feature,GaussianMarked.segment,Fin.snoc_last]
  · simp [feature,GaussianMarked.segment,Fin.snoc_castSucc]

theorem lifted_affine_piece {d : ℕ} (Ω : Matrix (Fin (d+1)) (Fin (d+1)) ℝ)
    (γ : ℝ → Space d) (a b : ℝ) (hpiece : AffinePiece γ a b) :
    AffinePiece (fun s => rootMap Ω (feature (γ s))) a b := by
  intro r hr
  change rootMap Ω (feature (γ (a+r*(b-a)))) =
    GaussianMarked.segment (rootMap Ω (feature (γ a))) (rootMap Ω (feature (γ b))) r
  rw [hpiece r hr,feature_segment]
  simp only [GaussianMarked.segment,map_add,map_smul]

/-- Corollary 6.3 for the actual jointly Gaussian augmented coefficients and
original piecewise affine probe. This is the endpoint covariance-kernel sum
of the paper, with arbitrary common mean and singular PSD covariance allowed. -/
theorem jointlyGaussian_polyline_arccos
    (hrep : GaussianRepresentationLaw) (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmax : GaussianMaxIntegralLaw)
    (hlength : ACCurveLengthLaw) {d : ℕ} (g : Model (d+1)) (n : ℕ) (p : Probe d)
    (hvar : ∀ s ∈ Icc 0 p.length, 0 < covarianceForm g.covariance (feature (p.curve s)))
    (knots : ℕ → ℝ) (hmono : Monotone knots) (N : ℕ)
    (h0 : knots 0 = 0) (hN : knots N = p.length)
    (hpieces : ∀ i < N, AffinePiece p.curve (knots i) (knots (i+1)))
    (hLNsource : VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d (n+2)) ℝ)
    (hLNmark : VisibleCrossing.LusinNovikovInput (MarkSample (d+1) n) (CurveParameter p.length)) :
    expectedSwitchCount (g.sampleLaw (n+2)) (scores p) p.length =
      ENNReal.ofReal (Paper35.gaussianRankCoefficient (n+2)) *
        ∑ i ∈ Finset.range N, ENNReal.ofReal (Real.arccos
          (covarianceKernel g.covariance (feature (p.curve (knots i)))
            (feature (p.curve (knots (i+1)))) /
          (Real.sqrt (covarianceForm g.covariance (feature (p.curve (knots i)))) *
            Real.sqrt (covarianceForm g.covariance (feature (p.curve (knots (i+1)))))))) := by
  rw [jointlyGaussian_spherical_length hrep hcrofton hregular hproj hrot hmax hlength
    g n p hvar hLNsource hLNmark]
  have hlengthsum := normalized_polyline_variation hlength
    (fun s => rootMap g.covariance (feature (p.curve s))) knots hmono N p.length h0 hN
    (fun i hi => lifted_affine_piece g.covariance p.curve _ _ (hpieces i hi))
    (fun s hs => rootMap_ne_zero g.covariance g.covariance_psd _ (hvar s hs))
  change ENNReal.ofReal (Paper35.gaussianRankCoefficient (n+2)) *
    eVariationOn (fun s => Gaussian.normalize (rootMap g.covariance (feature (p.curve s))))
      (Icc 0 p.length) = _
  rw [hlengthsum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_rootMap g.covariance g.covariance_psd,
    norm_rootMap_eq_sqrt_covarianceForm g.covariance g.covariance_psd,
    norm_rootMap_eq_sqrt_covarianceForm g.covariance g.covariance_psd]

/-- The one-segment form of Corollary 6.3, on the original probe interval and
with the source covariance kernel at its two actual endpoints. -/
theorem jointlyGaussian_segment_arccos
    (hrep : GaussianRepresentationLaw) (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmax : GaussianMaxIntegralLaw)
    (hlength : ACCurveLengthLaw) {d : ℕ} (g : Model (d+1)) (n : ℕ) (p : Probe d)
    (hvar : ∀ s ∈ Icc 0 p.length, 0 < covarianceForm g.covariance (feature (p.curve s)))
    (hpiece : AffinePiece p.curve 0 p.length)
    (hLNsource : VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d (n+2)) ℝ)
    (hLNmark : VisibleCrossing.LusinNovikovInput (MarkSample (d+1) n) (CurveParameter p.length)) :
    expectedSwitchCount (g.sampleLaw (n+2)) (scores p) p.length =
      ENNReal.ofReal (Paper35.gaussianRankCoefficient (n+2) * Real.arccos
        (covarianceKernel g.covariance (feature (p.curve 0)) (feature (p.curve p.length)) /
          (Real.sqrt (covarianceForm g.covariance (feature (p.curve 0))) *
            Real.sqrt (covarianceForm g.covariance (feature (p.curve p.length)))))) := by
  let knots : ℕ → ℝ := fun k => if k=0 then 0 else p.length
  have hmono : Monotone knots := by
    intro i j hij
    by_cases hi : i=0
    · subst i
      by_cases hj : j=0
      · subst j
        rfl
      · simpa only [knots,ite_true,if_neg hj] using p.length_pos.le
    · have hj : j≠0 := by omega
      simp only [knots,if_neg hi,if_neg hj,le_refl]
  have hp : ∀ i < 1, AffinePiece p.curve (knots i) (knots (i+1)) := by
    intro i hi
    have hi0 : i=0 := by omega
    subst i
    simpa only [knots,ite_true,zero_add,one_ne_zero,if_false] using hpiece
  have h := jointlyGaussian_polyline_arccos hrep hcrofton hregular hproj hrot hmax hlength
    g n p hvar knots hmono 1 (by simp [knots]) (by simp [knots]) hp hLNsource hLNmark
  rw [ENNReal.ofReal_mul (Paper35.gaussianRankCoefficient_nonneg (n+2))]
  simpa only [Finset.sum_range_one,knots,ite_true,zero_add,one_ne_zero,if_false] using h
end Paper35.GaussianLift
