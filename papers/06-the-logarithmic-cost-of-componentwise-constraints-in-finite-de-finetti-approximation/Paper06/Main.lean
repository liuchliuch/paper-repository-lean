/-
Copyright (c) 2026. Production entry point for the eight non-exempt numbered results and
all proved supporting modules.  Full source-level theorems are in
Posterior, Results, FullLowerBound, IncidenceFull and FullCorollaries.
The declarations below retain the earlier auxiliary API for compatibility;
they are not substituted for the full source-level results.
-/
import Paper06.Basic
import Paper06.Constraints
import Paper06.Conditioning
import Paper06.MatchLaw
import Paper06.Incidence
import Paper06.Witness
import Paper06.LowerBound
import Paper06.Corollaries
import Paper06.ResponseTable

import Paper06.Results
import Paper06.FullCorollaries
import Paper06.VanishingFamily
import Paper06.MatchingSupport
import Paper06.ResidueExamples
import Paper06.EmpiricalExample
import Paper06.MatchingPairLaw
import Paper06.NonIIDMixtures
import Paper06.OptimalErrorLimit

open Real Set BigOperators
open scoped Classical

namespace Paper06

/-! ## Lemma 2.1 (Posterior preservation) — `lemma_2_1_linear` -/

theorem lemma_2_1 {α : Type*} [Fintype α]
    (Γ : LinΓ α) (η : ℝ)
    (P₂ : FinProb (α × α)) (P₁ : FinProb α)
    (hCP : CP2 Γ.f η P₂ P₁) :
    ∀ z : α, 0 < P₁.w z →
      Γ.f (fun a => P₂.w (z, a) / P₁.w z) = η :=
  lemma_2_1_linear Γ η P₂ P₁ hCP

/-! ## Proposition 2.2 — `prop_2_2_bound`, `Lbound` -/

theorem prop_2_2_nonneg (n k d : ℕ) (hd : 0 < d)
    (hk : 1 ≤ k) (hn : k < n) :
    0 ≤ (k * (k - 1) : ℝ) / (2 * (n - k + 1)) * log d :=
  prop_2_2_bound n k d hd hk hn

/-! ## Theorem 3.1 — `thm_3_1_constants`, `thm_3_1_lb_nonneg` -/

/-! ## Proposition 3.2 — `edgeW_nonneg`, `edgeW_symm` -/

theorem prop_3_2_nonneg {R : Type*} [Fintype R] [CommRing R]
    (z z' : R × R) : 0 ≤ edgeW (R := R) z z' :=
  edgeW_nonneg z z'

/-! ## Lemma 3.3 — `quadratic_root_bound_beta`, `betaR_le` -/

theorem lemma_3_3_form (I r : ℕ) (hr : 0 < r)
    (h : (I : ℝ) * I ≤ r * I + r * r * (r - 1)) :
    (I : ℝ) / (r * r) ≤ betaR r ∧ betaR r ≤ 3 / (2 * sqrt r) :=
  ⟨quadratic_root_bound_beta I r hr h,
    betaR_le r (by exact_mod_cast (Nat.succ_le_of_lt hr))⟩

/-! ## Proposition 3.4 — `dBer_ge_p_log`, `prop_3_4_constant_nonneg` -/

theorem prop_3_4_form (n k : ℕ) (β : ℝ)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hβ : 0 < β)
    (hβ1 : β < 3 / (4 * Real.exp 1 * (n - 1))) :
    0 ≤ (3 * (k : ℝ) * (k - 1) / (8 * (n - 1))) *
      log (3 / (4 * Real.exp 1 * (n - 1) * β)) :=
  prop_3_4_constant_nonneg n k β hn hk2 hβ hβ1

/-! ## Corollaries 3.5 and 3.6 — `cor_3_5_skeleton`, `cor_3_6_constants` -/

/-! ## Proposition 4.1 — `prop_4_1_Lbound_nonneg` -/

theorem prop_4_1_form (M k : ℕ) (hk : 1 ≤ k) (hM : k < M) :
    0 ≤ (k * (k - 1) : ℝ) / (2 * (M - k + 1)) :=
  prop_4_1_Lbound_nonneg M k hk hM

end Paper06
