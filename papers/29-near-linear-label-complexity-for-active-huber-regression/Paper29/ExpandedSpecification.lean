import Paper29.QueryModel
import Paper29.ExternalProcess
import Paper29.ExternalCovering
import Paper29.LewisInput

/-! Independent expanded contracts. This file does not import AllRadius,
FiniteScoreConstruction, UpperProof or CheckedExpanded. Every extra argument
is a separately named, precisely disclosed published general theorem input;
none is an own centered-transfer, pilot, score-existence or upper conclusion. -/
namespace Paper29.ExpandedSpecification

def theorem21 : Prop :=
  ∀ C Cₜ Cₑ : ℝ, 0 < C → 0 < Cₜ → 0 < Cₑ →
    ExternalProcess.AnchoredChaining C → WeightConstruction.RadiusLogNonexpansive →
    ExternalCovering.HuberPrimitive 4 Cₜ → ExternalCovering.PowerPrimitive Cₑ →
    ExternalCovering.LewisOneNormalization → QueryModel.UpperBoundStatement

def lemma34 : Prop :=
  ∀ Cₜ Cₑ : ℝ, 0 ≤ Cₜ → 0 ≤ Cₑ → WeightConstruction.RadiusLogNonexpansive →
    ExternalCovering.HuberPrimitive 4 Cₜ → ExternalCovering.PowerPrimitive Cₑ →
    ExternalCovering.LewisOneNormalization → Chaining.AllRadiusScoresStatement

end Paper29.ExpandedSpecification
