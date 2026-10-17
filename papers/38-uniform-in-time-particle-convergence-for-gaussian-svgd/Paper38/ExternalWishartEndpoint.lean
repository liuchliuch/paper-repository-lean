import Paper38.Sampling

/-! Precise retained external facts in Remark7.4. These are ordinary input
propositions, not proved declarations or new axioms. Bartlett/Wishart source:
Anderson [1], Lemma7.2.1, and the standard Wishart inverse-moment threshold;
the chi-square log-square fact is the ν=1 instance of (7.18)--(7.19).
The own rate proofs use the logarithmic moment inputs and never an inverse
covariance moment. This unused explanatory boundary is recorded separately. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Paper38.ExternalWishartEndpoint
open Model

def chiSquareOneLaw : Measure ℝ :=
  (gaussianReal 0 1).map (fun x : ℝ => x^2)

def EndpointFacts (d : ℕ) : Prop :=
  (1 ≤ d → (∫⁻ ω, ENNReal.ofReal ((Sampling.covariance d (d+1) ω)⁻¹).trace
    ∂Sampling.law d (d+1)) = ∞) ∧
  Integrable (fun x : ℝ => (Real.log x)^2) chiSquareOneLaw

end Paper38.ExternalWishartEndpoint
