import Paper35.GaussianLift
import Paper35.GaussianOneDimensional
import Paper35.RandomCount

noncomputable section
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Paper35.GaussianLift
open Source GaussianMarked

/-- The original weight and bias, extracted from an augmented parameter vector. -/
def splitCandidate {d : ℕ} (θ : Space (d+1)) : Candidate d :=
  (WithLp.toLp 2 (fun i => θ i.castSucc), θ (Fin.last d))

lemma inner_feature {d : ℕ} (θ : Space (d+1)) (x : Space d) :
    inner ℝ θ (feature x) = inner ℝ (splitCandidate θ).1 x+(splitCandidate θ).2 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_castSucc,
    feature, splitCandidate, WithLp.ofLp_toLp, star_trivial]
  simp [mul_comm]

lemma measurable_splitCandidate (d : ℕ) : Measurable (splitCandidate (d := d)) := by
  unfold splitCandidate
  apply Measurable.prodMk
  · exact (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
      (measurable_pi_iff.mpr (fun i => by fun_prop))
  · fun_prop

lemma measurable_source_switchCount {d K : ℕ} (p : Probe d)
    (hLN : VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d K) ℝ) :
    Measurable (fun θ : Fin K → Space (d+1) => switchCount (scores p θ) p.length) := by
  have H := RandomCount.measurable_affineSwitchCount p.curve p.length p.length_pos
    p.lipschitz.continuousOn hLN
  have hm : Measurable (fun θ : Fin K → Space (d+1) => fun j => splitCandidate (θ j)) :=
    measurable_pi_iff.mpr (fun j => (measurable_splitCandidate d).comp (measurable_pi_apply j))
  convert H.comp hm using 1
  funext θ
  congr 2
  funext j s
  exact inner_feature (θ j) (p.curve s)

/-- Theorem 2.8 in the actual iid law of arbitrary jointly Gaussian augmented
weight/bias vectors, including arbitrary means and singular covariance.
Only q_γᵀΩq_γ>0 is required on the source probe. -/
theorem jointlyGaussian_spherical_length (hrep : GaussianRepresentationLaw)
    (hcrofton : ClassicalCroftonLaw) (hregular : ClassicalCroftonRegularityLaw)
    (hproj : GaussianUnitProjectionLaw) (hrot : GaussianPairReconstructionLaw)
    (hmax : GaussianMaxIntegralLaw) (hlength : ACCurveLengthLaw)
    {d : ℕ} (g : Model (d+1)) (n : ℕ) (p : Probe d)
    (hvar : ∀ s ∈ Icc 0 p.length, 0 < covarianceForm g.covariance (feature (p.curve s)))
    (hLNsource : VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d (n+2)) ℝ)
    (hLNmark : VisibleCrossing.LusinNovikovInput (MarkSample (d+1) n) (CurveParameter p.length)) :
    expectedSwitchCount (g.sampleLaw (n+2)) (scores p) p.length =
      ENNReal.ofReal (gaussianRankCoefficient (n+2)) *
        eVariationOn (fun s => psi g.covariance (p.curve s)) (Icc 0 p.length) := by
  have hcount : AEMeasurable (fun θ : Fin (n+2) → Space (d+1) =>
      switchCount (scores p θ) p.length) (g.sampleLaw (n+2)) :=
    (measurable_source_switchCount p hLNsource).aemeasurable
  rw [g.sampleLaw_eq_map hrep (n+2)] at hcount ⊢
  unfold expectedSwitchCount
  have hmap : Measurable (fun Z : Fin (n+2) → Space (d+1) =>
      fun j => g.mean + rootMap g.covariance (Z j)) :=
    measurable_pi_iff.mpr (fun j => measurable_const.add
      ((rootMap g.covariance).continuous.measurable.comp (measurable_pi_apply j)))
  rw [lintegral_map' hcount hmap.aemeasurable]
  have heq : (fun Z : Fin (n+2) → Space (d+1) =>
      switchCount (scores p (fun j => g.mean+rootMap g.covariance (Z j))) p.length) =
      fun Z => switchCount (gaussianScores (fun s => psi g.covariance (p.curve s)) Z) p.length := by
    funext Z
    exact congrArg (fun S : Set ℝ => (S.encard : ℝ≥0∞)) (covariance_sample_switchSet g p hvar Z)
  rw [heq]
  exact gaussian_upper_envelope_all_dimensions hcrofton hregular hproj hrot hmax hlength
    (d+1) n (by omega) p.length p.length_pos _
      (psi_probe_absolutelyContinuous g.covariance g.covariance_psd p hvar)
      (fun s hs => psi_unit g.covariance g.covariance_psd _ (hvar s hs)) hLNmark

end Paper35.GaussianLift
