import Paper25.Basic
import Paper25.Norms
import Paper25.Liouville
import Paper25.Filter
import Paper25.Bias
import Paper25.PhaseEst
import Paper25.Model
import Paper25.CPTP

/-!
# Numbered results of paper 25

This module re-exports the landed formalizations of the paper's numbered
results. See `coverage.json` for the per-result inventory and `STATEMENT_SPEC.md`
for the independent statement specification.

* Lemma 3 (CPTP Frobenius bound): `Paper25.lemma_3_cptp_frob_bound`
* Lemma 4 (scalar/sum form): `Paper25.nuclear_reg_sum_bound`
* Lemma 5 (analytic filter bounds): `Paper25.filter_range_bound`,
  `Paper25.filter_deriv_bound`, `Paper25.sin_pi_ge_two_mul`
* Theorem 1 (signed gap): `Paper25.theorem1_signed_gap`, `Paper25.bias_error_budget`
-/

noncomputable section

open scoped ComplexOrder ComplexConjugate

namespace Paper25

/-- Lemma 3, packaged. -/
theorem lemma_3 (d : ℕ) (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (h : IsCPTP S) : entryNormSq S ≤ (d : ℝ) ^ 2 :=
  lemma_3_cptp_frob_bound S h

/-- Lemma 4, scalar/sum form. -/
theorem lemma_4_sum {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, 0 < σ i) (lam : ℝ) (hlam : 0 < lam) :
    (∑ i, (lam ^ 2 / (σ i * (σ i ^ 2 + lam ^ 2)))) ≤ (lam / 2) * ∑ i, 1 / (σ i ^ 2) :=
  nuclear_reg_sum_bound σ hσ lam hlam

/-- Lemma 5, filter range. -/
theorem lemma_5_range (δ t : ℝ) (hδ : 0 < δ) : |filterFn δ t| ≤ 1 / 2 :=
  filter_range_bound δ t hδ

/-- Lemma 5, filter derivative. -/
theorem lemma_5_deriv (δ t : ℝ) (hδ : 0 < δ) :
    |δ * (δ ^ 2 - t ^ 2) / (t ^ 2 + δ ^ 2) ^ 2| ≤ 1 / δ :=
  filter_deriv_bound δ t hδ

/-- Theorem 1, signed gap. -/
theorem theorem_1_gap (lam K e a : ℝ)
    (hlam : 0 < lam) (hK : 1 ≤ K) (he : (1 / 3 : ℝ) ≤ |e|)
    (herr : |a - lam * e / Real.sqrt K| ≤ lam / (100 * K)) :
    (0 < e → lam / (4 * Real.sqrt K) ≤ a) ∧
    (e < 0 → a ≤ -lam / (4 * Real.sqrt K)) :=
  theorem1_signed_gap lam K e a hlam hK he herr

end Paper25
