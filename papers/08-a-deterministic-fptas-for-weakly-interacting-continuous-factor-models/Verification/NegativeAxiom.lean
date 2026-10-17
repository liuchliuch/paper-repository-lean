import Paper08.Paper

/-!
# Negative axiom control

Same statements as `Verification.Solution`, but the proofs go through an
illegal axiom so the official Comparator must reject the axiom audit.
-/

noncomputable section

axiom unauthorized_numeric : (2 : ℝ) = 3

open scoped Real BigOperators

namespace Paper08.Challenge

/-- Uses the illegal axiom `unauthorized_numeric` (2 = 3) to close the goal. -/
theorem lemma_2_2_kappa (R q h : ℝ) :
    2 * R * h * q / (2 * R - 1) = Paper08.Coeff.kappa R q * h := by
  have hbad : (2 : ℝ) = 3 := unauthorized_numeric
  have hfalse : False := by
    have : (2:ℝ) < 3 := by norm_num
    linarith
  exact hfalse.elim

theorem lemma_2_1_beta_gt_one (p : Paper08.FPTAS.Params) :
    1 < Paper08.FPTAS.beta p :=
  Paper08.FPTAS.beta_gt_one p

theorem lemma_2_3_multiplier_self {α : Type*} [DecidableEq α] (A : Finset α) :
    Paper08.Support.ieMultiplier A A = 1 :=
  Paper08.Support.ie_multiplier_self A

theorem lemma_2_3_binomial (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ)))
      = if n = 0 then 1 else 0 :=
  Paper08.Support.sum_choose_alternating n

theorem lemma_3_1_query_bound (J t r : ℕ) :
    (2 * t : ℝ) * (Nat.choose (J + t) t) * (2 : ℝ) ^ (r * J)
      ≤ (2 * t : ℝ) * (2 : ℝ) ^ ((r + 1) * J + t) :=
  Paper08.Quadrature.query_bound J t r

theorem lemma_3_1_truncation {J : ℕ} {B τ : ℝ} {t : ℕ}
    (hB : 0 < B) (hτ : 0 < τ)
    (hJ : Paper08.Quadrature.satisfies_level_choice J B τ t) :
    B * (2 : ℝ) ^ (-(J : ℝ) / 2) * Paper08.C0 ^ t ≤ τ / 2 :=
  Paper08.Quadrature.truncation_error_le hB hτ hJ

theorem lemma_3_2_sum_error {J : ℕ} {ζ : ℝ} (hζ : 0 ≤ ζ) :
    ζ + (∑ _ℓ ∈ Finset.range J, (2 * ζ : ℝ)) ≤ 2 * (J + 1 : ℝ) * ζ :=
  Paper08.Quadrature.sum_increment_error hζ

theorem theorem_1_2_accurate_exp {Zhat Z ε : ℝ}
    (h : Paper08.FPTAS.Accurate Zhat Z ε) :
    Real.exp (-ε) ≤ Zhat / Z ∧ Zhat / Z ≤ Real.exp ε :=
  Paper08.FPTAS.accurate_exp_form h

theorem corollary_1_3_log_bound : Real.log (3 / 2) < 5 / 12 :=
  Paper08.FPTAS.log_three_halves_lt

theorem corollary_1_3_eta_two {Δ : ℝ} (hΔ : 1 ≤ Δ) :
    (11 / 10 : ℝ) * 3 * Δ * Real.sqrt 2 * (Real.log (3 / 2) / (2 * Δ)) < 1 :=
  Paper08.FPTAS.eta_two_bound hΔ

theorem lemma_A_1_log_lipschitz {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| :=
  Paper08.log_abs_sub_le_abs_sub hx hy

theorem prop_B_1_bump {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    Paper08.Appendix.bump t ≤ 1 :=
  Paper08.Appendix.bump_le_one ht

end Paper08.Challenge
