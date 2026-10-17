import PUT.PhysicalOracles
import PUT.ExternalAlgorithms

/-!
# Actual tester correctness on the hard-prior oracle fields

The standard amplification input is applied once to the tester family.
Pointwise success on the genuine preparation oracles is then transferred
to the measurable null and alternative fields, on the actual simplex support.
No averaged-success or progress hypothesis is supplied externally.
-/
noncomputable section
namespace PUT.TesterPromises
open MeasureTheory QueryModel SourceTargets FourierModel PhysicalOracles

/-- A measurable hard-null oracle, with exactly the tester's physical registers. -/
def nullField {d M : ℕ} (C : TesterFamily d) (hd : 0 < d) (hM : 0 < M) :
    PointwiseUnitary (phaseMeasure d M) (TestSpace d M (C.workspace M)) :=
  (U0 hd hM).controlled.withWorkspace

/-- A measurable hard-alternative oracle, unitary on every ambient parameter. -/
def alternativeField {d M : ℕ} {a : ℝ} (C : TesterFamily d)
    (hd : 0 < d) (ha : 0 < a) (hM : 0 < M) :
    PointwiseUnitary (alternativeMeasure d M a) (TestSpace d M (C.workspace M)) :=
  (U1 hd ha hM).controlled.withWorkspace

@[simp] theorem nullField_unitary {d M : ℕ} (C : TesterFamily d)
    (hd : 0 < d) (hM : 0 < M) (θ : Torus d M) :
    (nullField C hd hM).unitary θ = C.oracle (nullOracle hd hM θ) := by
  change withWorkspace (controlled ((U0 hd hM).unitary θ)) = _
  rw [U0_unitary_nullOracle]
  rfl

/-- On every valid input, the entire unknown alternative unitary equals the
one to which the tester's universal correctness guarantee applies. -/
theorem alternativeField_unitary {d M : ℕ} {a : ℝ} (C : TesterFamily d)
    (hd : 0 < d) (ha : 0 < a) (hM : 0 < M) (p : Fin d → ℝ) (θ : Torus d M)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (alternativeField C hd ha hM).unitary (p,θ) =
      C.oracle (preparationOracle p θ hM hp hsum) := rfl

/-- The two pointwise implications supplied by ordinary independent-run
amplification; this interface contains no prior, TV, adversary or lower bound. -/
def AmplificationTransfer {d : ℕ} (C D : TesterFamily d) (Q : ℕ) : Prop :=
  ∀ (M : ℕ) (U : PreparationOracle d M),
    ((C.circuit M).rejectProbability (C.oracle U) Q ≤ 1 / 100 →
      (D.circuit M).rejectProbability (D.oracle U) (9 * Q) ≤
        TestingLowerBound.ninefoldError) ∧
    (99 / 100 ≤ (C.circuit M).rejectProbability (C.oracle U) Q →
      1 - TestingLowerBound.ninefoldError ≤
        (D.circuit M).rejectProbability (D.oracle U) (9 * Q))

theorem amplification_exists (hAmplify : External.NinefoldAmplificationLaw)
    {d : ℕ} (C : TesterFamily d) (Q : ℕ) :
    ∃ D : TesterFamily d, AmplificationTransfer C D Q := hAmplify d C Q

/-- Actual null-prior success, with the amplified tester's own workspace. -/
theorem null_success {d M : ℕ} {ε : ℝ} {Q : ℕ} {C D : TesterFamily d}
    (hC : C.Tests ε Q) (hAmp : AmplificationTransfer C D Q)
    (hd : 0 < d) (hM : 0 < M) :
    ∀ᵐ θ ∂phaseMeasure d M,
      (D.circuit M).rejectProbability ((nullField D hd hM).unitary θ) (9 * Q) ≤
        TestingLowerBound.ninefoldError := by
  exact Filter.Eventually.of_forall (fun θ => by
    rw [nullField_unitary]
    apply (hAmp M (nullOracle hd hM θ)).1
    apply (hC M (nullOracle hd hM θ)).1
    intro i
    rfl)

/-- Correctness is transferred only where the actual alternative prior has
valid probabilities. This is derived from normalized-Gamma simplex support. -/
theorem alternative_success {d M : ℕ} {a ε : ℝ} {Q : ℕ} {C D : TesterFamily d}
    (hC : C.Tests ε Q) (hAmp : AmplificationTransfer C D Q)
    (hd : 0 < d) (ha : 0 < a) (hM : 0 < M) :
    ∀ᵐ x ∂alternativeMeasure d M a,
      ε < tvDist x.1 (uniform d) →
        1 - TestingLowerBound.ninefoldError ≤
          (D.circuit M).rejectProbability ((alternativeField D hd ha hM).unitary x) (9 * Q) := by
  filter_upwards [alternative_ae_simplex (M := M) hd ha] with x hx
  intro hfar
  have hp : ∀ i, 0 ≤ x.1 i := fun i => (hx.1 i).le
  rw [show x = (x.1,x.2) from rfl, alternativeField_unitary D hd ha hM x.1 x.2 hp hx.2]
  apply (hAmp M (preparationOracle x.1 x.2 hM hp hx.2)).2
  exact (hC M (preparationOracle x.1 x.2 hM hp hx.2)).2 hfar

end PUT.TesterPromises
