import PUT.Basic
import PUT.QueryModel

/-!
# Operational model entry point

The operational definitions live in `PUT.QueryModel`: preparation oracles
contain their entire unitary action and normalized conditional garbage;
circuits evolve by actual forward/inverse oracle calls and fixed unitaries;
measurement probabilities follow the Born rule. Controlled access and finite
workspace are represented by genuine unitary lifts.

The former `Unit` tester, vacuous garbage condition, and `requiredQueries`
definition have been removed. No query lower bound is asserted by a definition.
-/

noncomputable section
namespace PUT.Model

abbrev PrepOracle (d M : ℕ) := QueryModel.PreparationOracle d M

def PrepOracle.prob {d M : ℕ} (U : PrepOracle d M) (i : Fin d) : ℝ :=
  U.probability i

def isUniform {d M : ℕ} (U : PrepOracle d M) : Prop :=
  ∀ i, U.probability i = (1 : ℝ) / d

def isFar {d M : ℕ} (U : PrepOracle d M) (ε : ℝ) : Prop :=
  ε < tvDist U.probability (uniform d)

end PUT.Model
