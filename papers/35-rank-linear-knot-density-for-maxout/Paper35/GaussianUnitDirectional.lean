import Paper35.GaussianUnitAdapter

/-!
# Actual GaussianUnit directional crossing bound

The normalized-lift speed retains the projected norm `‖A v‖ / σ` before
integrating. The resulting bound is the exact directional covariance kernel
needed for Corollary 8.3, under the original GaussianUnit sample law.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Paper35.GaussianUnitDirectional
open Source GaussianLift GaussianMarked GaussianAnisotropic GaussianWinner
variable {d : ℕ}

lemma normalizedVelocity_le_direction (A : Space d →L[ℝ] Space d)
    {σ : ℝ} (hσ : 0 < σ) (x v : Space d) :
    ‖Gaussian.normalizedVelocity (lift A σ x) (velocity A v)‖ ≤ ‖A v‖ / σ := by
  calc
    _ ≤ ‖velocity A v‖ / ‖lift A σ x‖ :=
      Gaussian.normalizedVelocity_norm_le _ _ (lift_ne_zero A hσ x)
    _ = ‖A v‖ / ‖lift A σ x‖ := by rw [norm_velocity]
    _ ≤ _ := div_le_div₀ (norm_nonneg _) le_rfl hσ (norm_lift_lower A hσ x)

/-- A pointwise directional speed bound on almost every parameter of the
original arclength probe, without any nondegeneracy of the weight covariance. -/
theorem sphericalLength_le_directional (A : Space d →L[ℝ] Space d)
    {σ : ℝ} (hσ : 0 < σ) (p : Probe d) :
    sphericalLength (fun t => GaussianSharpness.normalizedMap A σ (p.curve t)) p.length ≤
      ∫⁻ s in Icc 0 p.length, ENNReal.ofReal (‖A (deriv p.curve s)‖ / σ) := by
  have hd : ∀ᵐ s ∂volume, s ∈ Icc 0 p.length → DifferentiableAt ℝ p.curve s := by
    simpa only [ae_iff, Classical.not_imp] using
      Source.CrossingJacobian.nondifferentiable_null p
  have hdi : ∀ᵐ s ∂volume.restrict (Icc 0 p.length), DifferentiableAt ℝ p.curve s := by
    rwa [ae_restrict_iff' measurableSet_Icc]
  unfold sphericalLength
  apply lintegral_mono_ae
  filter_upwards [hdi] with s hs
  have hn := Gaussian.hasDerivAt_normalize (hasDerivAt_lift A σ hs.hasDerivAt)
    (lift_ne_zero A hσ _)
  simp only [GaussianSharpness.normalizedMap]
  rw [hn.deriv]
  exact ENNReal.ofReal_le_ofReal (normalizedVelocity_le_direction A hσ _ _)

lemma norm_rootMap_direction (m : GaussianUnit d) (v : Space d) :
    ‖rootMap m.covariance v‖ =
      Real.sqrt (Deep.covarianceForm m.covariance (fun i => v i) (fun i => v i)) := by
  rw [← GaussianUnitAdapter.covarianceForm_coordinates,
    ← norm_rootMap_sq _ m.covariance_psd, Real.sqrt_sq (norm_nonneg _)]

/-- The exact directional Gaussian count bound on the actual source sample
law; no operator-norm relaxation or additional Gaussian input is used. -/
theorem expectedCount_le_directional
    (hrep : GaussianRepresentationLaw)
    (hcrofton : ClassicalCroftonLaw) (hregular : ClassicalCroftonRegularityLaw)
    (hproj : GaussianUnitProjectionLaw) (hrot : GaussianPairReconstructionLaw)
    (hmax : GaussianMaxIntegralLaw) (m : GaussianUnit d) (hd : 1 ≤ d)
    (K : ℕ) (hK : 2 ≤ K) (p : Probe d)
    (hLNsource : VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d K) ℝ)
    (hLNmark : ∀ q : Probe d, VisibleCrossing.LusinNovikovInput
      (MarkSample (d+1) (K-2)) (CurveParameter q.length)) :
    expectedSwitchCount (m.sampleLaw K)
      (fun θ j s => GaussianUnit.scores m (fun i => p.curve s i) θ j) p.length ≤
      ∫⁻ s in Icc 0 p.length, ENNReal.ofReal (gaussianRankCoefficient K / m.biasSd *
        Real.sqrt (Deep.covarianceForm m.covariance
          (fun i => deriv p.curve s i) (fun i => deriv p.curve s i))) := by
  rw [GaussianUnitAdapter.expectedCount_eq m K p hLNsource,
    (GaussianUnitAdapter.independentModel m).expectedCount_eq_canonical hrep K p hLNsource]
  change GaussianSharpness.expectedCount (rootMap m.covariance) m.biasSd K p ≤ _
  rw [GaussianSharpness.countLengthIdentity_of_classicalInputs (rootMap m.covariance)
    m.biasSd_pos hd K hK hcrofton hregular hproj hrot hmax hLNmark p]
  calc
    _ ≤ ENNReal.ofReal (gaussianRankCoefficient K) *
        ∫⁻ s in Icc 0 p.length,
          ENNReal.ofReal (‖rootMap m.covariance (deriv p.curve s)‖ / m.biasSd) :=
      mul_le_mul_left' (sphericalLength_le_directional (rootMap m.covariance) m.biasSd_pos p) _
    _ = _ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro s
      rw [norm_rootMap_direction, ← ENNReal.ofReal_mul (gaussianRankCoefficient_nonneg K)]
      congr 1
      ring

end Paper35.GaussianUnitDirectional
