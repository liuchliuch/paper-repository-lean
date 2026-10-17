import PUT.FullQueryBound
import PUT.DirichletLemma
import PUT.ExternalAlgorithms
import PUT.CollisionTester
import PUT.AdaptiveModel
import PUT.AdaptiveTruncation

/-!
# Principal source statements on the actual constructed objects

Published standard inputs remain visible to the left of each implication.
All conclusions quantify the genuine continuous measures and full query
operators, rather than numerical surrogates for those objects.
-/
noncomputable section
open MeasureTheory
namespace Verification.Specification
open PUT PUT.FourierModel PUT.FourierPreparation

/-- Paper Lemma 2: the actual continuous Dirichlet event has the printed mass. -/
def SourceLemma2 : Prop :=
  PUT.External.DirichletJointMomentLaw →
    ∀ (d : ℕ) (a : ℝ), 2 ≤ d → 1 ≤ a →
      (1 / 144 : ℝ) ≤ (dirichletMeasure d a).real
        {p | 1 / (24 * Real.sqrt a) ≤ tvDist p (uniform d)}

/-- Paper Lemma 1: the constructed Fourier--Dirichlet adversary and the
actual complete reflection queries satisfy the printed operator-norm bound.
The block coordinates are related isometrically to the physical register. -/
def SourceLemma1 : Prop :=
  PUT.External.DirichletJointMomentLaw →
    ∀ (d M : ℕ) (a A : ℝ) (hd : 2 ≤ d) (ha : 0 < a) (hA : 1 ≤ A)
      (hM : 16 * A ^ 2 * LA A ≤ (M : ℝ)),
      let hd0 : 0 < d := by omega
      let hM0 : 0 < M := by exact_mod_cast M_pos_of_param A M hA hM
      ‖PUT.OperatorBridge.liftedAdversary
          (gamma (M := M) hd0 ha A) (PUT.FullQueryBound.gammaH hd0 ha A) ∘L
          PUT.OperatorBridge.reflectionBlock (V1 hd0 ha hM0).toContinuousLinearMap -
        PUT.OperatorBridge.reflectionBlock (V0 hd0 hM0).toContinuousLinearMap ∘L
          PUT.OperatorBridge.liftedAdversary
            (gamma (M := M) hd0 ha A) (PUT.FullQueryBound.gammaH hd0 ha A)‖ ≤
        20 * (Real.sqrt (1 + A / d) + A ^ (3 / 2 : ℝ) / (a * Real.sqrt d) +
          A / Real.sqrt (a * d))

/-- Paper Theorem 1 in the full controlled forward/inverse unitary circuit
model, relative to precisely disclosed standard external dependencies. The
success predicate quantifies every valid full unitary and finite garbage size. -/
def SourceTheorem1 : Prop :=
  PUT.External.DirichletJointMomentLaw →
    PUT.External.NinefoldAmplificationLaw → PUT.External.KutinCollisionLaw →
      ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (ε : ℝ),
        2 ≤ d → 0 < ε → ε < 1 / 2 →
          ∀ (C : PUT.SourceTargets.TesterFamily d) (Q : ℕ), C.Tests ε Q →
            c * min ((d : ℝ) ^ (1 / 3 : ℝ) * ε ^ (-4 / 3 : ℝ))
              (Real.sqrt d / ε) ≤ (Q : ℝ)

/-- Source Theorem 1 with adaptive measurements, branch-dependent query
directions and early termination, and with all standard inputs explicit. -/
def SourceAdaptiveTheorem1 : Prop :=
  PUT.External.DirichletJointMomentLaw →
    PUT.External.NinefoldAmplificationLaw → PUT.External.KutinCollisionLaw →
      PUT.External.AdaptiveNormalizationLaw →
        ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (ε : ℝ),
          2 ≤ d → 0 < ε → ε < 1 / 2 →
            ∀ (A : PUT.AdaptiveModel.AdaptiveTesterFamily d) (Q : ℕ),
              A.BoundedTests ε Q →
                c * min ((d : ℝ) ^ (1 / 3 : ℝ) * ε ^ (-4 / 3 : ℝ))
                  (Real.sqrt d / ε) ≤ (Q : ℝ)

/-- The full source worst-case convention requires the query budget only
on promised inputs. Intermediate measurements, branch-dependent directions,
early stopping and arbitrary off-promise behavior are retained. -/
def SourcePromiseTheorem1 : Prop :=
  PUT.External.DirichletJointMomentLaw →
    PUT.External.NinefoldAmplificationLaw → PUT.External.KutinCollisionLaw →
      PUT.External.AdaptiveNormalizationLaw →
        ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (ε : ℝ),
          2 ≤ d → 0 < ε → ε < 1 / 2 →
            ∀ (A : PUT.AdaptiveModel.AdaptiveTesterFamily d) (Q : ℕ),
              A.PromiseBoundedTests ε Q →
                c * min ((d : ℝ) ^ (1 / 3 : ℝ) * ε ^ (-4 / 3 : ℝ))
                  (Real.sqrt d / ε) ≤ (Q : ℝ)

end Verification.Specification
