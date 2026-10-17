import Paper26.A1LowerRisk
import Paper26.OperatorMeasureConstruction

/-!
# Appendix A.1 as an exact operator-POVM minimax value

Both the lower bound and its attainment now concern the same actual
`OperatorLearner` model.  All measurable outcome spaces are indexed in the
infimum, not just the covariant frame outcome space.  `RNFamily` abbreviates
the already-existing generic operator RN input at each outcome space; it adds
no statistical, posterior, risk, success, or algorithmic conclusion.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.A1MinimaxValue
open QuantumModel HaarFrames ContinuousPOVM CollectiveModel SymmetricSupport PureCovariant
  OperatorPOVMTransport OperatorMeasureConstruction A1LowerRisk

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The existing fixed-POVM RN representation, retained uniformly over all
outcome spaces and their arbitrary sigma algebras.  This is an abbreviation,
not an additional external theorem. -/
abbrev RNFamily (ι : Type u) [Fintype ι] [DecidableEq ι] (n : ℕ) : Prop :=
  ∀ (Ω : Type u) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    OperatorRadonNikodymInput (Fin n → ι) Ω

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}

/-- Set-integrating a dominated POVM preserves its actual expected loss,
even when the RN representation chosen afterwards has different densities. -/
theorem expectedRisk_toOperator (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (A : Learner ι Ω n) (ρ : Density ι) :
    operatorExpectedRisk R (toOperatorLearner A) ρ = PureCovariantRisk.expectedRisk A ρ := by
  change (∫⁻ y, chiR ρ (A.estimator.estimate y) ∂operatorOutcomeMeasure R
    (toOperatorPOVM A.measurement) (TensorCopies.density ρ n)) = _
  rw [← outcomeMeasure_eq_of_representation R (toOperatorPOVM A.measurement) A.measurement
    (represents A.measurement) (TensorCopies.density ρ n)]
  rfl

theorem worstRisk_toOperator (R : OperatorRadonNikodymInput (Fin n → ι) Ω)
    (A : Learner ι Ω n) : operatorWorstRisk R (toOperatorLearner A) = worstRisk A := by
  simp only [operatorWorstRisk, worstRisk, expectedRisk_toOperator]

/-- The infimum ranges over every measurable outcome space and every
operator-valued collective POVM with an unrestricted density estimator. -/
def minimaxRisk (R : RNFamily ι n) : ℝ≥0∞ :=
  ⨅ (Ω : Type u), ⨅ (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ⨅ A : OperatorLearner ι Ω n, operatorWorstRisk (R Ω m) A

theorem minimaxRisk_lower [Nonempty ι]
    (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) (P : SymmetricProjectorInput ι n)
    (Q : SymmetricProjectorInput ι (n + 1)) (R : RNFamily ι n) :
    ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) n) ≤ minimaxRisk R := by
  apply le_iInf
  intro Ω
  apply le_iInf
  intro m
  letI : MeasurableSpace Ω := m
  apply le_iInf
  intro A
  exact operatorWorstRisk_lower μ H P Q (R Ω m) A

/-- The normalized covariant experiment (or the constant experiment when
`d=1`) attains the value as an actual operator-valued POVM. -/
theorem exists_operator_attaining [Nonempty ι]
    (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) (P : SymmetricProjectorInput ι n)
    (Q : SymmetricProjectorInput ι (n + 1))
    (R : OperatorRadonNikodymInput (Fin n → ι) (Frame ι (Fin 1))) :
    ∃ A : OperatorLearner ι (Frame ι (Fin 1)) n,
      operatorWorstRisk R A = ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) n) := by
  obtain ⟨A, hA⟩ := exists_attaining μ H P Q
  exact ⟨toOperatorLearner A, (worstRisk_toOperator R A).trans hA⟩

/-- The exact minimax value, including zero copies and dimension one, with
the same actual operator-POVM model on both sides of the optimization. -/
theorem equation_50 [Nonempty ι]
    (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) (P : SymmetricProjectorInput ι n)
    (Q : SymmetricProjectorInput ι (n + 1)) (R : RNFamily ι n) :
    minimaxRisk R = ENNReal.ofReal
      ((Real.sqrt ((n : ℝ) + 1) + Fintype.card ι - 1) ^ 2 /
        ((n : ℝ) + Fintype.card ι) - 1) := by
  change minimaxRisk R = ENNReal.ofReal (PureMinimax.appendixARisk (ι := ι) n)
  apply le_antisymm _ (minimaxRisk_lower μ H P Q R)
  obtain ⟨A, hA⟩ := exists_operator_attaining μ H P Q (R (Frame ι (Fin 1)) inferInstance)
  calc
    _ ≤ operatorWorstRisk (R (Frame ι (Fin 1)) inferInstance) A := by
      unfold minimaxRisk
      exact iInf_le_of_le (Frame ι (Fin 1)) (iInf_le_of_le inferInstance (iInf_le _ A))
    _ = _ := hA

end Paper26.A1MinimaxValue
