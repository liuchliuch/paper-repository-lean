import Paper35.ExactCrossing
import Paper35.VisibilityKernel
import Paper35.Covariance
import Paper35.SharpnessLimit

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Paper35.ClassicalInputs

/-- The published Lusin--Novikov theorem, uniformly over standard Borel
spaces, rather than any paper-specific count or relation. See Kechris,
Classical Descriptive Set Theory (1995), Theorem 18.10. -/
def LusinNovikovLaw : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y], VisibleCrossing.LusinNovikovInput X Y

/-- Borel projections are analytic and universally measurable: the completed
measurability statement is quantified over every sigma-finite Borel measure.
No zero-measure assertion or maxout relation is assumed. -/
def BorelProjectionLaw : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y],
      VisibleCrossing.BorelProjectionNullMeasurableInput X Y

end Paper35.ClassicalInputs

namespace Paper35.DistributionFree
open Source Source.WeightedModel ClassicalInputs

/-- Complete source (3.7), with every own stochastic/geometric step proved. -/
theorem exactCrossing {d : ℕ} (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw) :
    ExactCrossingClaim (d := d) :=
  Source.ExactCrossing.exactCrossingClaim (fun _ _ => hLN _ _) (fun _ => hUP _ _)

/-- Full weighted visibility bound (2.6), with actual source laws and no
moments needed. Extended values are preserved. -/
theorem weighted_visibility {d : ℕ} (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw) :
    WeightedVisibilityClaim (d := d) :=
  weightedVisibility_of_crossing_visibility (exactCrossing hLN hUP)
    (VisibilityKernel.visibilityLemmaClaim d)

/-- Full tilted-covariance consequence (2.7). -/
theorem weighted_covariance {d : ℕ} (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw) :
    WeightedCovarianceClaim (d := d) :=
  weightedCovariance_of_weightedVisibility (weighted_visibility hLN hUP)

/-- The heterogeneous crossing identity used by Theorem 2.6 is now a theorem,
not an unresolved internal premise. -/
theorem heterogeneous_crossing {d K : ℕ} (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw) :
    Heterogeneous.ExactCrossingClaim d K :=
  Source.ExactCrossing.heterogeneous_exactCrossingClaim (fun _ => hLN _ _) (fun _ => hUP _ _)

/-- The candidate-additive theorem (2.12), retaining only the classical
maximum-density normalization input in addition to generic descriptive set theory. -/
theorem heterogeneous_bound {d K : ℕ} (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw)
    (hmax : Heterogeneous.MaxDensityFormula) (m : Heterogeneous.Model d K)
    (hK : 2 ≤ K) (p : Probe d) :
    m.expectedCount p ≤ ∫⁻ s in Icc 0 p.length,
      ⨅ c : ℝ, ∑ i, (m.B i : ℝ≥0∞)*m.centeredMoment (deriv p.curve s) c i :=
  Heterogeneous.expectedCount_le_common_reference hmax (heterogeneous_crossing hLN hUP) m hK p

end Paper35.DistributionFree
