import Paper38.Model
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Precisely isolated standard linear matrix-ODE inputs

These are named propositions supplied as explicit arguments, not axioms.
They quantify over an arbitrary continuous real matrix coefficient C and have
no Gaussian potential, particle law, minimizer, or source-paper conclusion.

Source: Gerald Teschl, Ordinary Differential Equations and Dynamical Systems,
AMS GSM 140 (2012), §3.4 Theorems 3.9--3.10 and Lemma 3.11, printed pp.81--83;
§3.7 Theorem 3.23, printed pp.99--100:
https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf

`StandardDecayingFundamentalMatrixTheorem` is the usual exponential-tail
corollary: Gronwall bounds L and L⁻¹ for an L¹ coefficient (Theorem 3.23,
also applied to the transpose inverse equation); integration of L'=CL then
bounds Linf-L(t) by the tail integral of the exponential envelope. Both L and
L⁻¹ have limits, whose products are I, so Linf is invertible. The final
convergence/tail corollary is not falsely attributed to a numbered statement
of the book; the argument above specifies the precise standard input used.
-/

namespace Paper38.LinearMatrixODE

open Paper38.Model Set Filter
open scoped Topology

/-- Global principal fundamental matrix for an arbitrary continuous coefficient. -/
def StandardFundamentalMatrixTheorem (d : ℕ) : Prop :=
  ∀ C : ℝ → Mat d, ContinuousOn C (Ici 0) →
    ∃ L : ℝ → Mat d, L 0 = 1 ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt L (C t * L t) (Ici 0) t) ∧
      (∀ t, 0 ≤ t → IsUnit (L t))

/-- Standard integrable/exponentially decaying linear-system corollary.
Frobenius squares fix the norm unambiguously. The tail constant is chosen before C, so it depends only on d, K and decay. -/
def StandardDecayingFundamentalMatrixTheorem (d : ℕ) : Prop :=
  ∀ (K decay : ℝ), 0 ≤ K → 0 < decay →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ C : ℝ → Mat d, ContinuousOn C (Ici 0) →
      (∀ t, 0 ≤ t → frobSq (C t) ≤ K ^ 2 * Real.exp (-2 * decay * t)) →
      ∃ (L : ℝ → Mat d) (Linf : Mat d),
        L 0 = 1 ∧
        (∀ t, 0 ≤ t → HasDerivWithinAt L (C t * L t) (Ici 0) t) ∧
        (∀ t, 0 ≤ t → IsUnit (L t)) ∧ IsUnit Linf ∧
        Tendsto L atTop (𝓝 Linf) ∧
        (∀ t, 0 ≤ t → frobSq (L t - Linf) ≤ M ^ 2 * Real.exp (-2 * decay * t))

end Paper38.LinearMatrixODE
