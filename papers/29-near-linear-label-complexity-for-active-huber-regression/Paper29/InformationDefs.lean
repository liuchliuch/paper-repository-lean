import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.Pi

/-! Definitions only for the finite information-theory statements of P29. -/
noncomputable section
open scoped BigOperators

namespace Paper29.RateDistortion

abbrev Cube (r : ℕ) := Fin r → Bool

/-- An arbitrary joint law of the source word and the estimated word. -/
structure JointLaw (r : ℕ) where
  mass : Cube r → Cube r → ℝ
  nonneg : ∀ s t, 0 ≤ mass s t
  total : ∑ s, ∑ t, mass s t = 1

namespace JointLaw
variable {r : ℕ} (P : JointLaw r)

def source (s : Cube r) : ℝ := ∑ t, P.mass s t

def estimate (t : Cube r) : ℝ := ∑ s, P.mass s t

/-- Finite mutual information, with zero-mass summands interpreted as zero. -/
def mutualInformation : ℝ :=
  ∑ s, ∑ t, P.mass s t *
    (Real.log (P.mass s t) - Real.log (P.source s) - Real.log (P.estimate t))

/-- The negative conditional entropy, written directly in terms of joint masses. -/
def conditionalLogMass : ℝ :=
  ∑ s, ∑ t, P.mass s t * (Real.log (P.mass s t) - Real.log (P.estimate t))

end JointLaw

/-- Real-valued Hamming distance, the sum of mismatch indicators. -/
def hamming {r : ℕ} (s t : Cube r) : ℝ :=
  ∑ j, if s j = t j then 0 else 1

/-- Expected Hamming error under the given joint law. -/
def expectedHamming {r : ℕ} (P : JointLaw r) : ℝ :=
  ∑ s, ∑ t, P.mass s t * hamming s t

/-- A strictly positive product law around an arbitrary estimated word. -/
def errorChannel {r : ℕ} (δ : ℝ) (s t : Cube r) : ℝ :=
  ∏ j, if s j = t j then 1 - δ else δ

/-- The numerical rate-distortion constant, in nats. -/
def cRD : ℝ := Real.log 2 - Real.binEntropy (1 / 25)

end Paper29.RateDistortion
