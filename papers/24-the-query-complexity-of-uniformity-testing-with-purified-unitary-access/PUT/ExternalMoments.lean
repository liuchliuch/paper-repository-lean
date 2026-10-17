import PUT.DirichletMeasure

/-!
# Explicit external Dirichlet moment input

The sole external analytic input here is the standard joint moment law of
the Dirichlet distribution, for the actual normalized-independent-gamma
measure defined in `DirichletMeasure`.  No TV moment estimate, centered
moment bound, Holder inequality, or tail estimate is included in this input.

Precise standard references for this external analytic input:

* NIST Digital Library of Mathematical Functions, Section 5.14,
  equation (5.14.2), the multivariate beta simplex integral:
  https://dlmf.nist.gov/5.14.E2 . Shifting its positive parameters by the
  nonnegative integer powers and dividing by the unshifted normalizer gives
  the mixed moment formula.
* Anirban DasGupta, *Graduate Probability*, Section 1.23, Theorem 1.68,
  printed pp. 138-139 (author PDF pp. 127-128), identifies independent
  gamma variables divided by their sum with the Dirichlet density:
  https://www.stat.purdue.edu/~dasgupta/gradprob.pdf .

The mixed moment formula is
`E[∏ P_i^k_i] = Γ(∑ α_i)/Γ(∑ α_i+∑ k_i) * ∏ Γ(α_i+k_i)/Γ(α_i)`;
specializing `α_i = a` gives the quotient of rising factorials below.

This is a proposition supplied explicitly to derived theorems, not an axiom
or an asserted proof of the analytic moment law.
-/

noncomputable section
namespace PUT.External
open MeasureTheory

/-- Standard joint Dirichlet moments, with the source measure and actual
integrability preserved.  This is the only external input used by Lemma 2. -/
def DirichletJointMomentLaw : Prop :=
  ∀ (d : ℕ) (a : ℝ) (k : Fin d → ℕ), 2 ≤ d → 0 < a →
    Integrable (fun p : Fin d → ℝ => ∏ i, p i ^ k i) (dirichletMeasure d a) ∧
      (∫ p, (∏ i, p i ^ k i) ∂dirichletMeasure d a) = dirMoment a k

end PUT.External
