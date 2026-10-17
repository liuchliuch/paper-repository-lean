import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import GeometricMedianCoresets.Basic
import GeometricMedianCoresets.GeometricInequalities

/-!
# Simultaneous relative comparison (paper Proposition 2.4, Remark 2.5)

Deterministic skeleton of Proposition 2.4 is `prop24_deterministic` in
`GeometricInequalities`. This module records Remark 2.5 and supporting scalars.
-/

noncomputable section

namespace GeometricMedianCoresets

/-- Remark 2.5 (concrete obstruction). Population of `2m-1` zeroes and one
point at `R` has `OPT = R/(2m)`; missing the outlier yields comparison error
`R/m = 2 OPT`. -/
theorem remark_2_5_costs {m : ℕ} {R : ℝ}
    (hm : 2 ≤ m) (_hR : 0 < R) :
    2 * (R / (2 * m)) = R / m := by
  field_simp

/-- Numeric identity used in Lemma 2.6 (export). -/
theorem lemma26_gap (ε : ℝ) :
    (1 + 17 * ε) * (1 - ε) - (1 + 11 * ε + 2 * ε ^ 2) = ε * (5 - 19 * ε) :=
  lemma26_gap_identity ε

end GeometricMedianCoresets
