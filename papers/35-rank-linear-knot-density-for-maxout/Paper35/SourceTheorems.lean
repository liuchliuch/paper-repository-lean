import Paper35.DistributionFree
import Paper35.CovarianceSpectrum
import Paper35.IIDCovariance
import Paper35.RandomProbes
import Paper35.GaussianLaw

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Paper35.SourceTheorems
open Source Source.WeightedModel ClassicalInputs

/-- Source Theorem 2.3, equation (2.8), now with its internal covariance
estimate discharged by the complete distribution-free branch. -/
theorem theorem_2_3_spectral {d : ℕ} (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw)
    (m : WeightedModel d) (hW : MemLp (fun w => w) 2 m.tilted)
    (K : ℕ) (hK : 2 ≤ K) (p : Probe d) :
    m.expectedDensity K p ≤
      ((K : ℝ≥0∞)*m.average/ENNReal.ofReal (Real.sqrt 3)) *
        ENNReal.ofReal (Real.sqrt m.covarianceSpectralNorm) :=
  expectedDensity_le_spectral (DistributionFree.weighted_covariance hLN hUP) m hW K hK p

/-- Literal source (2.8), with the largest eigenvalue of the actual original
weight covariance matrix and the constant conditional-density envelope. -/
theorem theorem_2_3_lambdaMax {d : ℕ} (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw)
    (m : WeightedModel d) (B : ℝ≥0) (hb : ∀ᵐ w ∂m.weights, m.b₀ w = B)
    (hW : MemLp (fun w => w) 2 m.weights) (K : ℕ) (hK : 2 ≤ K) (p : Probe d) :
    m.expectedDensity K p ≤ ((K : ℝ≥0∞)*B/ENNReal.ofReal (Real.sqrt 3)) *
      ENNReal.ofReal (Real.sqrt (matrixLambdaMax m.covarianceMatrix)) :=
  expectedDensity_le_lambdaMax (DistributionFree.weighted_covariance hLN hUP)
    m B hb hW K hK p

/-- Corollary 2.5, first inequality in (2.9). This actually proves the
stronger independent/equal-variance coordinate result; iid coordinates with
a density are a special case. No particular uniform construction is assumed. -/
theorem corollary_2_5_upper {d : ℕ} (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw)
    (m : WeightedModel d) (B : ℝ≥0) (hb : ∀ᵐ w ∂m.weights, m.b₀ w = B)
    (hind : iIndepFun (fun (i : Fin d) (w : Space d) => w i) m.weights)
    (hW : ∀ i : Fin d, MemLp (fun w : Space d => w i) 2 m.weights)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (hvar : ∀ i : Fin d, variance (fun w : Space d => w i) m.weights = σ^2)
    (K : ℕ) (hK : 2 ≤ K) (p : Probe d) :
    m.expectedDensity K p ≤
      ((K : ℝ≥0∞)*(B : ℝ≥0∞)/ENNReal.ofReal (Real.sqrt 3))*ENNReal.ofReal σ :=
  expectedDensity_le_iid_coordinates (DistributionFree.weighted_covariance hLN hUP)
    m B hb hind hW σ hσ hvar K hK p

/-- Equations (2.10)--(2.11): the source-admissible uniform family achieves
the fixed-rank coefficient as a supremum. Its independence, identical
coordinate laws, bounded densities and variance are proved in Sharpness and
SharpnessLimit, and the upper bound for all admissible laws is above. -/
theorem corollary_2_5_sharp_family {d : ℕ}
    (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw)
    {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) (K : ℕ) (hK : 2 ≤ K) (i : Fin d) :
    (⨆ ε : {ε : ℝ // 0 < ε}, ENNReal.ofReal (Sharpness.centeredExpectedDensity
      (Sharpness.independentUniformModel (Sharpness.uniformWeights d (Real.sqrt 3*σ)) B hB)
        K i ε)) = ENNReal.ofReal ((K : ℝ)/Real.sqrt 3*B*σ) :=
  Sharpness.sharp_centered_supremum (DistributionFree.exactCrossing hLN hUP) hB hσ K hK i

/-- The universal rank-linear coefficient cannot be smaller than 2/sqrt(3),
using actual rank-two source counts on positive-length straight segments. -/
theorem corollary_2_5_universal_optimal {d : ℕ}
    (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw)
    {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) (i : Fin d) (C : ℝ)
    (hbound : ∀ ε : ℝ, 0 < ε → Sharpness.centeredExpectedDensity
      (Sharpness.independentUniformModel (Sharpness.uniformWeights d (Real.sqrt 3*σ)) B hB)
        2 i ε ≤ C*B*σ) : 2/Real.sqrt 3 ≤ C :=
  Sharpness.sharp_universal_rank_coefficient (DistributionFree.exactCrossing hLN hUP) hB hσ i C hbound

/-- Source (2.14), with the internal covariance theorem discharged. -/
theorem corollary_2_7_random {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw) (μ : Measure Ω) [SFinite μ]
    (m : WeightedModel d) (B : ℝ≥0) (hb : ∀ᵐ w ∂m.weights, m.b₀ w = B)
    (hW : MemLp (fun w => w) 2 m.weights) (K : ℕ) (hK : 2 ≤ K)
    (p : Ω → Probe d) (hL : Measurable (fun ω => (p ω).length))
    (hγ : Measurable (fun z : RandomCount.RandomProbeDomain p => (p z.1.1).curve z.1.2)) :
    (∫⁻ z : Ω × (Fin K → Candidate d),
      switchCount (scores (p z.1) z.2) (p z.1).length ∂μ.prod (m.iid K)) ≤
      ((K : ℝ≥0∞)*B/ENNReal.ofReal (Real.sqrt 3)) *
        ∫⁻ ω, (∫⁻ s in Icc 0 (p ω).length, RandomProbes.covarianceSpeed m (p ω) s) ∂μ :=
  RandomProbes.randomProbe_covariance_bound (DistributionFree.weighted_covariance hLN hUP)
    μ m B hb hW K hK p hL hγ (hLN _ _)

/-- Source (2.15), retaining arbitrary dependence between different units. -/
theorem corollary_2_7_parallel {d : ℕ} {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw) (μ : Measure Ω)
    (K : ι → ℕ) (m : ι → WeightedModel d) (B : ι → ℝ≥0)
    (hb : ∀ r, ∀ᵐ w ∂(m r).weights, (m r).b₀ w = B r)
    (hW : ∀ r, MemLp (fun w => w) 2 (m r).weights) (hK : ∀ r, 2 ≤ K r)
    (p : Probe d) (a : (r : ι) → Ω → Fin (K r) → Candidate d)
    (ha : ∀ r, Measurable (a r)) (hlaw : ∀ r, μ.map (a r) = (m r).iid (K r)) :
    (∫⁻ ω, Deep.jointSwitchCount K (fun r => scores p (a r ω)) p.length ∂μ) ≤
      (1/ENNReal.ofReal (Real.sqrt 3)) * ∫⁻ s in Icc 0 p.length,
        ∑ r, (K r : ℝ≥0∞)*B r*RandomProbes.covarianceSpeed (m r) p s :=
  RandomProbes.parallel_covariance_bound (DistributionFree.weighted_covariance hLN hUP)
    μ K m B hb hW hK p a ha hlaw (fun _ => hLN _ _)

end Paper35.SourceTheorems
