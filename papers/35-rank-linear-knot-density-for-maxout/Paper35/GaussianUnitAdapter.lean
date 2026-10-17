import Paper35.GaussianIndependent
import Paper35.GaussianWinner

/-!
# GaussianUnit source-law adapter

Finite-coordinate GaussianUnit weight and bias samples are measurably
transported to the Euclidean independent Gaussian model. Coordinate covariance,
projection laws, candidate and iid sample pushforwards, and the actual affine
scores are all identified. The final anisotropic expected-count bound therefore
applies to the original GaussianUnit sample law, with no extra distribution or
count-identity premise.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Paper35.GaussianUnitAdapter
open Source GaussianLift GaussianIndependent GaussianWinner GaussianMarked
variable {d : ℕ}

lemma covarianceForm_coordinates (C : Matrix (Fin d) (Fin d) ℝ) (v : Space d) :
    GaussianLift.covarianceForm C v = Deep.covarianceForm C (fun i => v i) (fun i => v i) := by
  simp [GaussianLift.covarianceForm, Deep.covarianceForm, Matrix.toEuclideanLin_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  rfl

lemma projected_score_coordinates (v : Space d) (w : Fin d → ℝ) :
    inner ℝ (WithLp.toLp 2 w) v = dotProduct (fun i => v i) w := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]

/-- A source GaussianUnit is the same actual centered Gaussian weight law,
transported through the Euclidean coordinate equivalence. -/
def independentModel (m : GaussianUnit d) : GaussianIndependent.Model d where
  weights :=
    { law := m.weightLaw.map (WithLp.toLp 2)
      probability := by
        letI := m.weight_probability
        exact Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 _).aemeasurable
      mean := 0
      covariance := m.covariance
      covariance_psd := m.covariance_psd
      projections := by
        intro v
        rw [Measure.map_map (by fun_prop) (WithLp.measurable_toLp 2 _)]
        have hf : ((fun θ : Space d => inner ℝ θ v) ∘ WithLp.toLp 2) =
            fun w : Fin d → ℝ => dotProduct (fun i => v i) w := by
          funext w
          exact projected_score_coordinates v w
        rw [hf, m.projected_law]
        rw [inner_zero_left, covarianceForm_coordinates]
        congr 1
        apply NNReal.eq
        simp only [Real.coe_toNNReal']
        exact (max_eq_left (by simpa only [Deep.covarianceForm] using m.covariance_psd.2 (fun i => v i))).symm }
  biasMean := 0
  biasStd := m.biasSd
  biasStd_pos := m.biasSd_pos

def candidateToSpace (θ : GaussianUnit.Candidate d) : Source.Candidate d :=
  (WithLp.toLp 2 θ.1, θ.2)

lemma measurable_candidateToSpace (d : ℕ) : Measurable (candidateToSpace (d := d)) :=
  ((WithLp.measurable_toLp 2 _).comp measurable_fst).prodMk measurable_snd

lemma candidateLaw_map (m : GaussianUnit d) :
    m.candidateLaw.map candidateToSpace = (independentModel m).joint := by
  letI := m.weight_probability
  change (m.weightLaw.prod (gaussianReal 0 ⟨m.biasSd^2, sq_nonneg _⟩)).map
      (Prod.map (WithLp.toLp 2) id) = _
  rw [← Measure.map_prod_map _ _ (WithLp.measurable_toLp 2 _) measurable_id, Measure.map_id]
  rfl

def sampleToSpace {K : ℕ} (θ : GaussianUnit.Sample d K) : Fin K → Source.Candidate d :=
  fun j => candidateToSpace (θ j)

lemma measurable_sampleToSpace (K : ℕ) : Measurable (sampleToSpace (d := d) (K := K)) :=
  measurable_pi_iff.mpr fun j => (measurable_candidateToSpace d).comp (measurable_pi_apply j)

lemma sampleLaw_map (m : GaussianUnit d) (K : ℕ) :
    (m.sampleLaw K).map sampleToSpace = (independentModel m).sampleLaw K := by
  have h := Measure.pi_map_pi (μ := fun _ : Fin K => m.candidateLaw)
    (f := fun _ => candidateToSpace (d := d))
    (fun _ => (measurable_candidateToSpace d).aemeasurable)
  simp_rw [candidateLaw_map] at h
  exact h

lemma scores_eq (m : GaussianUnit d) {K : ℕ} (p : Probe d)
    (θ : GaussianUnit.Sample d K) (j : Fin K) (s : ℝ) :
    GaussianUnit.scores m (fun i => p.curve s i) θ j =
      Source.WeightedModel.scores p (sampleToSpace θ) j s := by
  change dotProduct (θ j).1 (fun i => p.curve s i)+(θ j).2 =
    inner ℝ (WithLp.toLp 2 (θ j).1) (p.curve s)+(θ j).2
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

/-- Actual GaussianUnit switch counts under the original finite-coordinate
sample law equal those under its Euclidean source adapter. -/
theorem expectedCount_eq (m : GaussianUnit d) (K : ℕ) (p : Probe d)
    (hLN : VisibleCrossing.LusinNovikovInput (RandomCount.CodeParameter d K) ℝ) :
    expectedSwitchCount (m.sampleLaw K)
      (fun θ j s => GaussianUnit.scores m (fun i => p.curve s i) θ j) p.length =
      (independentModel m).expectedCount K p := by
  have hm := RandomCount.measurable_affineSwitchCount p.curve p.length p.length_pos
    p.lipschitz.continuousOn hLN
  unfold GaussianIndependent.Model.expectedCount expectedSwitchCount
  have hm' : Measurable (fun θ : Fin K → Source.Candidate d =>
      switchCount (Source.WeightedModel.scores p θ) p.length) := hm
  rw [← sampleLaw_map m K, lintegral_map hm' (measurable_sampleToSpace K)]
  apply lintegral_congr
  intro θ
  congr 1
  funext j s
  exact scores_eq m p θ j s

/-- The actual finite-coordinate GaussianUnit satisfies the anisotropic count
bound used by a deep layer, with its actual source sample law. -/
theorem expectedCount_le_anisotropic
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
        ENNReal.ofReal (gaussianRankCoefficient K *
          (Real.sqrt (covarianceMax m.covariance) / m.biasSd)) * ENNReal.ofReal p.length := by
  rw [expectedCount_eq m K p hLNsource,
    (independentModel m).expectedCount_eq_canonical hrep K p hLNsource]
  change GaussianSharpness.expectedCount (rootMap m.covariance) m.biasSd K p ≤ _
  rw [GaussianSharpness.countLengthIdentity_of_classicalInputs (rootMap m.covariance)
    m.biasSd_pos hd K hK hcrofton hregular hproj hrot hmax hLNmark p]
  calc
    _ ≤ ENNReal.ofReal (gaussianRankCoefficient K) *
        (ENNReal.ofReal (‖rootMap m.covariance‖ / m.biasSd) * ENNReal.ofReal p.length) :=
      mul_le_mul_left' (GaussianSharpness.sphericalLength_probe_le
        (rootMap m.covariance) m.biasSd_pos p) _
    _ = _ := by
      rw [norm_rootMap_eq_sqrt _ m.covariance_psd,
        ENNReal.ofReal_mul (gaussianRankCoefficient_nonneg K), mul_assoc]

end Paper35.GaussianUnitAdapter
