import Paper08.Paper

/-!
# Negative type control

Same declaration names as `Verification.Solution`, but each statement has an
extra `False` premise so the official Comparator must reject the type mismatch.
-/

noncomputable section

open scoped Real BigOperators

namespace Paper08.Challenge

theorem lemma_2_1_beta_gt_one (p : Paper08.FPTAS.Params) (hfalse : False) :
    1 < Paper08.FPTAS.beta p :=
  hfalse.elim

theorem lemma_2_2_kappa (R q h : ℝ) (hfalse : False) :
    2 * R * h * q / (2 * R - 1) = Paper08.Coeff.kappa R q * h :=
  hfalse.elim

theorem lemma_2_3_multiplier_self {α : Type*} [DecidableEq α] (A : Finset α)
    (hfalse : False) : Paper08.Support.ieMultiplier A A = 1 :=
  hfalse.elim

theorem lemma_2_3_binomial (n : ℕ) (hfalse : False) :
    (∑ k ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ)))
      = if n = 0 then 1 else 0 :=
  hfalse.elim

theorem lemma_3_1_query_bound (J t r : ℕ) (hfalse : False) :
    (2 * t : ℝ) * (Nat.choose (J + t) t) * (2 : ℝ) ^ (r * J)
      ≤ (2 * t : ℝ) * (2 : ℝ) ^ ((r + 1) * J + t) :=
  hfalse.elim

theorem lemma_3_1_truncation {J : ℕ} {B τ : ℝ} {t : ℕ}
    (hB : 0 < B) (hτ : 0 < τ)
    (hJ : Paper08.Quadrature.satisfies_level_choice J B τ t) (hfalse : False) :
    B * (2 : ℝ) ^ (-(J : ℝ) / 2) * Paper08.C0 ^ t ≤ τ / 2 :=
  hfalse.elim

theorem lemma_3_2_sum_error {J : ℕ} {ζ : ℝ} (hζ : 0 ≤ ζ) (hfalse : False) :
    ζ + (∑ _ℓ ∈ Finset.range J, (2 * ζ : ℝ)) ≤ 2 * (J + 1 : ℝ) * ζ :=
  hfalse.elim

theorem theorem_1_2_accurate_exp {Zhat Z ε : ℝ}
    (h : Paper08.FPTAS.Accurate Zhat Z ε) (hfalse : False) :
    Real.exp (-ε) ≤ Zhat / Z ∧ Zhat / Z ≤ Real.exp ε :=
  hfalse.elim

theorem corollary_1_3_log_bound (hfalse : False) : Real.log (3 / 2) < 5 / 12 :=
  hfalse.elim

theorem corollary_1_3_eta_two {Δ : ℝ} (hΔ : 1 ≤ Δ) (hfalse : False) :
    (11 / 10 : ℝ) * 3 * Δ * Real.sqrt 2 * (Real.log (3 / 2) / (2 * Δ)) < 1 :=
  hfalse.elim

theorem lemma_A_1_log_lipschitz {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hfalse : False) : |Real.log x - Real.log y| ≤ |x - y| :=
  hfalse.elim

theorem prop_B_1_bump {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hfalse : False) :
    Paper08.Appendix.bump t ≤ 1 :=
  hfalse.elim

end Paper08.Challenge
