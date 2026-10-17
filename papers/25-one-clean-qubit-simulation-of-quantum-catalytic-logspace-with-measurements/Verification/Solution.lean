import Paper25.Basic
import Paper25.Norms
import Paper25.Filter
import Paper25.Bias
import Paper25.CPTP
import Paper25.Restoration
import Paper25.Regularization
import Paper25.History
import Paper25.TraceReadout
import Paper25.Main

/-!
# Proofs of the separately reviewed paper statements

Does not import the challenge. Each declaration has the fixed interface of
`Verification/Challenge.lean` and is witnessed by a closed proof from the
mathematical library.
-/

noncomputable section

open scoped ComplexOrder ComplexConjugate

namespace Paper25.Challenge

/-- Scalar identity of Lemma 4. -/
theorem inv_sub_regularized (σ lam : ℝ) (hσ : 0 < σ) (hlam : 0 < lam) :
    1 / σ - σ / (σ ^ 2 + lam ^ 2) = lam ^ 2 / (σ * (σ ^ 2 + lam ^ 2)) :=
  Paper25.inv_sub_regularized σ lam hσ hlam

/-- Scalar inequality of Lemma 4. -/
theorem regularized_term_le (σ lam : ℝ) (hσ : 0 < σ) (hlam : 0 < lam) :
    lam ^ 2 / (σ * (σ ^ 2 + lam ^ 2)) ≤ lam / (2 * σ ^ 2) :=
  Paper25.regularized_term_le σ lam hσ hlam

/-- Sum form of the nuclear-norm regularization bound. -/
theorem nuclear_reg_sum_bound {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, 0 < σ i)
    (lam : ℝ) (hlam : 0 < lam) :
    (∑ i, (lam ^ 2 / (σ i * (σ i ^ 2 + lam ^ 2)))) ≤ (lam / 2) * ∑ i, 1 / (σ i ^ 2) :=
  Paper25.nuclear_reg_sum_bound σ hσ lam hlam

/-- Filter range bound `|δt/(t²+δ²)| ≤ 1/2`. -/
theorem filter_range_bound (δ t : ℝ) (hδ : 0 < δ) :
    |δ * t / (t ^ 2 + δ ^ 2)| ≤ 1 / 2 :=
  Paper25.filter_range_bound δ t hδ

/-- Filter derivative bound. -/
theorem filter_deriv_bound (δ t : ℝ) (hδ : 0 < δ) :
    |δ * (δ ^ 2 - t ^ 2) / (t ^ 2 + δ ^ 2) ^ 2| ≤ 1 / δ :=
  Paper25.filter_deriv_bound δ t hδ

/-- `2Δ ≤ |sin(πΔ)|` for `Δ ∈ [0, 1/2]`. -/
theorem sin_pi_ge_two_mul (Δ : ℝ) (h0 : 0 ≤ Δ) (h1 : Δ ≤ 1 / 2) :
    2 * Δ ≤ |Real.sin (Real.pi * Δ)| :=
  Paper25.sin_pi_ge_two_mul Δ h0 h1

/-- Parameter budget (22). -/
theorem bias_error_budget (J K : ℝ) (hJ : 1 ≤ J) (hK : 1 ≤ K) :
    (Paper25.biasLam J K ^ 2 / 2) * J ^ 2 * K ^ 2 + Paper25.biasEps J K
      ≤ Paper25.biasLam J K / (100 * K) :=
  Paper25.bias_error_budget J K hJ hK

/-- Weak form of (22). -/
theorem bias_eq22 (lam K e a : ℝ)
    (hlam : 0 < lam) (hK : 1 ≤ K)
    (herr : |a - lam * e / Real.sqrt K| ≤ lam / (100 * K)) :
    |a - lam * e / Real.sqrt K| ≤ lam / (100 * Real.sqrt K) :=
  Paper25.bias_eq22 lam K e a hlam hK herr

/-- Lemma 3 core. -/
theorem psd_trace_frob_bound_fin {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J.PosSemidef) (t : ℝ) (ht : Matrix.trace J = (t : ℂ)) :
    Paper25.frobNormSq J ≤ t ^ 2 :=
  Paper25.psd_trace_frob_bound_fin J hJ t ht

/-- Lemma 3 packaged. -/
theorem lemma_3_cptp_frob_bound {d : ℕ}
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (h : Paper25.IsCPTP S) :
    Paper25.entryNormSq S ≤ (d : ℝ) ^ 2 :=
  Paper25.lemma_3_cptp_frob_bound S h

/-- Lemma 4 singular-value form. -/
theorem lemma_4_singular_value_form {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, 0 < σ i)
    (lam : ℝ) (hlam : 0 < lam) :
    (∑ i, |1 / σ i - σ i / (σ i ^ 2 + lam ^ 2)|) ≤ (lam / 2) * ∑ i, 1 / (σ i ^ 2) :=
  Paper25.lemma_4_singular_value_form σ hσ lam hlam

/-- Equation (6) scalar form. -/
theorem history_frob_bound_scalar (J d : ℝ) :
    (J * J) * (d * d) = J ^ 2 * d ^ 2 :=
  Paper25.history_frob_bound_scalar J d

/-- Equation (10) scalar form. -/
theorem history_reg_error_scalar (lam J K D2 : ℝ) (hlam : 0 < lam) (hK : 0 < K)
    (hD2 : 0 < D2) (err : ℝ)
    (herr : err ≤ (lam / 2) * J ^ 2 * (K ^ 2 * D2 ^ 2) / D2 ^ 2) :
    err ≤ (lam / 2) * J ^ 2 * K ^ 2 :=
  Paper25.history_reg_error_scalar lam J K D2 hlam hK hD2 err herr

/-- Equation (20) normalized. -/
theorem equation_20_normalized {n : Type*} [Fintype n] [DecidableEq n] (k D2 : ℕ)
    (hD2 : 0 < D2) (P W : Matrix n n ℂ) :
    (2 * Matrix.trace (P * W)) / (2 ^ (k + 1) * D2 : ℂ)
      = Matrix.trace (P * W) / (2 ^ k * D2 : ℂ) :=
  Paper25.equation_20_normalized k D2 hD2 P W

/-- Equation (20) full. -/
theorem equation_20_full {n : Type*} [Fintype n] [DecidableEq n] (k D2 : ℕ)
    (hD2 : 0 < D2) (P W : Matrix n n ℂ) :
    (Matrix.trace W + Matrix.trace ((2 • P - 1) * W)) / (2 ^ (k + 1) * D2 : ℂ)
      = Matrix.trace (P * W) / (2 ^ k * D2 : ℂ) :=
  Paper25.equation_20_full k D2 hD2 P W

/-- Lemma 6 trace test. -/
theorem lemma_6_trace_test (N : ℕ) (hN : 0 < N) (V : Matrix (Fin N) (Fin N) ℂ) :
    ((1 / 2 : ℂ) * (Matrix.trace V.conjTranspose + Matrix.trace V) / N).re
      = (Matrix.trace V).re / N :=
  Paper25.lemma_6_trace_test N hN V

/-- Theorem 1 decision gap. -/
theorem theorem1_decision_gap (lam K e a : ℝ)
    (hlam : 0 < lam) (hK : 1 ≤ K) (he : (1 / 3 : ℝ) ≤ |e|)
    (herr : |a - lam * e / Real.sqrt K| ≤ lam / (100 * K)) :
    (0 < e → lam / (4 * Real.sqrt K) ≤ a) ∧
    (e < 0 → a ≤ -lam / (4 * Real.sqrt K)) :=
  Paper25.theorem1_decision_gap lam K e a hlam hK he herr

/-- Theorem 1 probability gap. -/
theorem theorem1_prob_gap (lam K a : ℝ) (k : ℕ)
    (hlam : 0 < lam) (hK : 0 < K)
    (ha : lam / (4 * Real.sqrt K) ≤ a) :
    (1 / 2 : ℝ) + lam / ((2 : ℝ) ^ (k + 3) * Real.sqrt K)
      ≤ 1 / 2 + a / (2 : ℝ) ^ (k + 1) :=
  Paper25.theorem1_prob_gap lam K a k hlam hK ha

/-- Gap survives gate synthesis. -/
theorem gap_survives_synthesis (gamma xi : ℝ)
    (h : 2 * xi ≤ gamma / 4) (hγ : 0 < gamma) :
    (1 / 2 : ℝ) + gamma - 2 * xi ≥ 1 / 2 + gamma / 2 :=
  Paper25.gap_survives_synthesis gamma xi h hγ

/-- Theorem 1 certificate existence. -/
theorem theorem1_certificate_exists (s c T k : ℕ) (_hc : 0 ≤ c)
    (hT : 1 ≤ T) (hs : 1 ≤ s) (hk : 0 ≤ k) :
    ∃ J K : ℝ, (1 ≤ J) ∧ (1 ≤ K) ∧
      (0 : ℝ) < Paper25.biasLam J K ∧
      (0 : ℝ) < Paper25.biasGamma (Paper25.biasLam J K) K k :=
  Paper25.theorem1_certificate_exists s c T k _hc hT hs hk

/-- Lemma 2 exact restoration (Liouville form). -/
theorem lemma_2_exact_restoration {m n : ℕ}
    {S : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} {ω η : Fin m → ℂ}
    (h : Paper25.ExactRestoration S ω η) :
    (∀ x : Fin n → ℂ, Matrix.mulVec S (Paper25.kronVec ω x) = Paper25.kronVec η x) ∧
    (∀ z : Fin m → ℂ,
      Matrix.trace (Paper25.kronRankOneId ω z * S) = (n : ℂ) * Paper25.cinner z η) :=
  Paper25.lemma_2_exact_restoration h

/-- Lemma 2 product form. -/
theorem lemma_2_product_form {k d : ℕ} (η : Matrix (Fin k) (Fin k) ℂ)
    (Ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ)
    (hbasis : ∀ i j : Fin d, Ψ (Paper25.basisMat i j) = Matrix.kronecker η (Paper25.basisMat i j))
    (X : Matrix (Fin d) (Fin d) ℂ) :
    Ψ X = Matrix.kronecker η X :=
  Paper25.lemma_2_product_form η Ψ hbasis X

end Paper25.Challenge
