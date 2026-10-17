/-
Copyright (c) 2026. Main-statement assemblies for Theorem 1.3 and Corollary 1.4.
-/
import Paper09.Main
import Paper09.IsingSoftShell
import Paper09.Covering
import Paper09.Spectral

open Finset BigOperators Classical Real

noncomputable section

namespace Paper09

/-- Theorem 1.3 (1.5)⇒(1.6) assembled. -/
theorem theorem_1_3_assembled {d c C : ℝ}
    (hd : 2 ≤ d) (hc : 0 < c) (hC : 0 < C) :
    0 < aExp d ∧ aExp d < 1 ∧
    ∀ n Y, 3 ≤ n → 0 < Y →
      exp (c * (log n / log (log n)) ^ aExp d) ≤ Y →
      Y ≤ exp (C * (log n) ^ aExp d * (log (log n)) ^ (d - 1)) →
      c * (log n / log (log n)) ^ aExp d ≤ log Y ∧
      log Y ≤ C * (log n) ^ aExp d * (log (log n)) ^ (d - 1) :=
  theorem_1_3_two_sided hd hc hC

/-- Corollary 1.4 assembled: d = 2 gives exponent 1/2. -/
theorem corollary_1_4_assembled : aExp 2 = 1 / 2 := corollary_1_4

/-- Proposition 2.1 assembled from the island gap cost and Lemma A.1. -/
theorem prop_2_1_assembled (c0 ε0 m d qH0 b0 gapν gapπ : ℝ)
    (hm : 0 < m) (hd : 0 < d) (hq : 0 ≤ qH0) (hb0 : 0 ≤ b0)
    (hε : ε0 = c0 / 16)
    (hH : 2 * d * qH0 * (exp b0 - 1 + b0) ≤ c0 / 4)
    (hpure : gapν ≤ exp (- c0 * m ^ (d - 1)))
    (hsoft : gapπ ≤ gapν * exp (4 * ε0 * m ^ (d - 1)
        + 2 * d * m ^ (d - 1) * qH0 * (exp b0 - 1 + b0))) :
    gapπ ≤ exp (- (c0 / 2) * m ^ (d - 1)) :=
  prop_2_1_gap_on_island c0 ε0 m d qH0 b0 gapν gapπ
    hm hd hq hb0 hε hH hpure hsoft

end Paper09
