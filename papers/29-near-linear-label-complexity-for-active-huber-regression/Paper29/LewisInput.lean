import Paper29.Leverage
import Paper29.WeightLogMetric

/-! Disclosed external endpoint input: existence of exact l1 Lewis weights,
Cohen–Peng, STOC2015, l_p row sampling by Lewis weights, Definition2.2 and Corollary3.4 (Lewis fixed point).
The input is stated as its equivalent positive auxiliary-weight normalization.
It contains no score mass, covering assertion or Huber all-radius claim; all
of those are derived locally. It is an explicit theorem argument, not an axiom.
A deterministic finite approximate endpoint algorithm is a separate algorithmic
obligation and is not asserted by this existence-only input. -/
noncomputable section
namespace Paper29.ExternalCovering
open WeightConstruction

def LewisOneNormalization : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin d) ℝ), A.rank = d → (∀ i, A i ≠ 0) →
    ∃ w : PositiveWeights n, ∀ i,
      Leverage.radius A w i / Leverage.leverage A w i = 1

end Paper29.ExternalCovering
