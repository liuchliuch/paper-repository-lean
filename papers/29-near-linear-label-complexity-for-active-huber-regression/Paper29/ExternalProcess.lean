import Paper29.ProcessTools

/-!
# Disclosed external generic-process input

The input below is the *general*, loss-independent, anchored symmetrization /
Bernoulli generic-chaining upper bound. Its source is Jambulapati–Lee–Liu–Sidford,
Sparsifying generalized linear models, arXiv:2311.18145v1, §1.6.2, Lemma1.14,
first inequality in (1.20), with the symmetrization citation to Talagrand(2014),
Lemma9.1.11; see also their cited Sparsifying sums of norms, Lemma2.6.

This file declares a Prop to be passed as an explicit theorem argument. It
introduces no axiom and provides no inhabitant. It is universal over arbitrary
bounded real function classes; no Huber shift, score estimate, centered transfer,
pilot guarantee or query-complexity conclusion is an input field.
-/
noncomputable section
open scoped BigOperators ENNReal
namespace Paper29.ExternalProcess
open ProcessTools

/-- An explicit version of the general first inequality of external (1.20).
`G ν` may be any verified upper bound for the actual conditional increment γ₂.
The universal constant includes the standard symmetrization factor. -/
def AnchoredChaining (C : ℝ) : Prop :=
  ∀ (n m : ℕ) (T : Type) (t₀ : T) (π : Fin n → ℝ) (f : Fin n → T → ℝ),
    0 < m → (∀ i, 0 < π i) → (∑ i, π i = 1) →
    (∀ i, f i t₀ = 0) →
    (∀ i, BddAbove (Set.range (fun t => |f i t|))) →
    ∀ G : (Fin m → Fin n) → ℝ, (∀ ν, 0 ≤ G ν) →
      (∀ ν, Chaining.gamma2 (sampleMetric π f ν) ≤ ENNReal.ofReal (G ν)) →
      Sampling.expectation π (errorSup (m := m) π f) ≤ C * Sampling.expectation π G

end Paper29.ExternalProcess
