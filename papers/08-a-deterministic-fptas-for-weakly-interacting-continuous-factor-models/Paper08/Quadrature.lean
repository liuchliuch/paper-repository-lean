import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Paper08.Basic
import Paper08.QuadratureIntegral

/-!
# Lemma 3.1 — total-level quadrature
# Lemma 3.2 — sample perturbations

The imported `QuadratureIntegral` layer proves the actual scoped dyadic
product-integral tail and stored-sample perturbation estimates.  The present
file also supplies the query-count arithmetic and the level-choice budget.
Nat powers `(2:ℝ) ^ n` (`n : ℕ`) and real powers `(2:ℝ) ^ x` (`x : ℝ`) are
kept distinct throughout.
-/

noncomputable section

open scoped Real BigOperators

namespace Paper08
namespace Quadrature

/-! ## Combinatorial bounds (3.2) -/

/-- `binom(J+t,t) ≤ 2^{J+t}` — the second inequality in (3.2). -/
lemma binom_le_two_pow (J t : ℕ) :
    (Nat.choose (J + t) t : ℝ) ≤ (2 : ℝ) ^ (J + t) :=
  mod_cast Nat.choose_le_two_pow (J + t) t

/-- Combined query bound (3.2):
`2 t · binom(J+t,t) · 2^{rJ} ≤ 2 t · 2^{(r+1)J+t}`. -/
lemma query_bound (J t r : ℕ) :
    (2 * t : ℝ) * (Nat.choose (J + t) t) * (2 : ℝ) ^ (r * J)
      ≤ (2 * t : ℝ) * (2 : ℝ) ^ ((r + 1) * J + t) := by
  by_cases ht : t = 0
  · subst ht; simp
  · have h1 : (Nat.choose (J + t) t : ℝ) ≤ (2 : ℝ) ^ (J + t) := binom_le_two_pow J t
    have hpos : (0:ℝ) ≤ 2 * t := by positivity
    have hnn : (0:ℝ) ≤ (2:ℝ) ^ (r * J) := pow_nonneg (by norm_num) _
    calc (2 * t : ℝ) * (Nat.choose (J + t) t) * (2 : ℝ) ^ (r * J)
        ≤ (2 * t : ℝ) * (2 : ℝ) ^ (J + t) * (2 : ℝ) ^ (r * J) := by
          gcongr
      _ = (2 * t : ℝ) * ((2 : ℝ) ^ (J + t) * (2 : ℝ) ^ (r * J)) := by ring
      _ = (2 * t : ℝ) * (2 : ℝ) ^ ((J + t) + r * J) := by rw [pow_add]; ring
      _ = (2 * t : ℝ) * (2 : ℝ) ^ ((r + 1) * J + t) := by
          congr 2
          ring

/-! ## Truncation error (3.5) -/

/-- Choice of `J` in (3.1): `2^{J/2} ≥ 2 𝓑 C₀^t / τ`. -/
def satisfies_level_choice (J : ℕ) (B τ : ℝ) (t : ℕ) : Prop :=
  (2 : ℝ) ^ ((J : ℝ) / 2) ≥ 2 * B * C0 ^ t / τ

/-- Main error estimate (3.5): if `J` satisfies (3.1) then
`𝓑 · 2^{-J/2} · C₀^t ≤ τ/2`.  Algebraic content of (3.5). -/
lemma truncation_error_le {J : ℕ} {B τ : ℝ} {t : ℕ}
    (_hB : 0 < B) (hτ : 0 < τ)
    (hJ : satisfies_level_choice J B τ t) :
    B * (2 : ℝ) ^ (-(J : ℝ) / 2) * C0 ^ t ≤ τ / 2 := by
  unfold satisfies_level_choice at hJ
  have h2pos : (0 : ℝ) < 2 ^ ((J : ℝ) / 2) := by positivity
  have hdiv : 2 * B * C0 ^ t / τ ≤ (2 : ℝ) ^ ((J : ℝ) / 2) := hJ
  have hmul : 2 * B * C0 ^ t ≤ (2 : ℝ) ^ ((J : ℝ) / 2) * τ := by
    rwa [div_le_iff₀ hτ] at hdiv
  have hhalf : B * C0 ^ t ≤ (2 : ℝ) ^ ((J : ℝ) / 2) * τ / 2 := by linarith
  have hpow : (2 : ℝ) ^ (-(J : ℝ) / 2) = ((2 : ℝ) ^ ((J : ℝ) / 2))⁻¹ := by
    have h : (-(J:ℝ) / 2) = -((J:ℝ) / 2) := by ring
    rw [h, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  have hrew : B * (2 : ℝ) ^ (-(J : ℝ) / 2) * C0 ^ t
      = (B * C0 ^ t) * ((2 : ℝ) ^ ((J : ℝ) / 2))⁻¹ := by
    rw [hpow]; ring
  rw [hrew]
  have hstep : (B * C0 ^ t) * ((2 : ℝ) ^ ((J : ℝ) / 2))⁻¹
      ≤ ((2 : ℝ) ^ ((J : ℝ) / 2) * τ / 2) * ((2 : ℝ) ^ ((J : ℝ) / 2))⁻¹ :=
    mul_le_mul_of_nonneg_right hhalf (inv_nonneg.mpr (le_of_lt h2pos))
  have hcancel : ((2 : ℝ) ^ ((J : ℝ) / 2) * τ / 2) * ((2 : ℝ) ^ ((J : ℝ) / 2))⁻¹ = τ / 2 := by
    field_simp
  rw [hcancel] at hstep
  exact hstep

/-! ## Sample perturbations (Lemma 3.2) -/

/-- Partial sums of increment errors: `ζ + ∑_{ℓ<J} 2ζ ≤ 2(J+1) ζ`. -/
lemma sum_increment_error {J : ℕ} {ζ : ℝ} (_hζ : 0 ≤ ζ) :
    ζ + (∑ _ℓ ∈ Finset.range J, (2 * ζ : ℝ)) ≤ 2 * (J + 1 : ℝ) * ζ := by
  have hsum : (∑ _ℓ ∈ Finset.range J, (2 * ζ : ℝ)) = 2 * ζ * J := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hsum]
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ; simp; nlinarith
  · have hJ1 : (1:ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith

/-- Algebraic identity underlying the second inequality of (3.7). -/
lemma sample_perturbation_max {J t : ℕ} {B ζ : ℝ} :
    (2 * (J + 1 : ℝ) * (3 : ℝ) ^ (t - 1) * B) * (t : ℝ) * ζ
      = 2 * (t : ℝ) * (J + 1 : ℝ) * (3 : ℝ) ^ (t - 1) * B * ζ := by
  ring

/-- Elementary geometric-sum helper.  The sharp `2B` increment budget used
in the actual stability proof is established in `Perturbation.lean`. -/
lemma sum_dyadic_bound {J : ℕ} {B : ℝ} (hB : 0 ≤ B) :
    B + (∑ ℓ ∈ Finset.range J, B * (1 / 2 : ℝ) ^ ℓ) ≤ B + B * 2 := by
  have hsum : (∑ ℓ ∈ Finset.range J, (1 / 2 : ℝ) ^ ℓ) ≤ 2 := by
    have := sum_geometric_two_le J
    norm_num at this ⊢
    linarith
  have : (∑ ℓ ∈ Finset.range J, B * (1 / 2 : ℝ) ^ ℓ)
      = B * (∑ ℓ ∈ Finset.range J, (1 / 2 : ℝ) ^ ℓ) := by
    rw [Finset.mul_sum]
  rw [this]
  nlinarith

/-- `‖Δ_{i,0}‖ ≤ B` and `∑_{ℓ≥1} ‖Δ_{i,ℓ}‖ ≤ B` give the total budget `2 B`
used in Lemma 3.2; the product telescoping then produces `3^{t-1}`. -/
lemma budget_three (B : ℝ) : B + 2 * B = 3 * B := by ring

/-- Hypothesis form of Lemma 3.2. -/
def SampleHyp (J : ℕ) (ζ B : ℝ) : Prop :=
  2 * (J + 1 : ℝ) * ζ ≤ B

lemma sample_hyp_of_le {J : ℕ} {ζ B : ℝ} (h : 2 * (J + 1 : ℝ) * ζ ≤ B) :
    SampleHyp J ζ B := h

/-- The analytic conclusion of Lemma 3.1 with the paper's actual choice
(3.1): the integral of the product of the original scoped local functions is
within `τ/2` of their finite total-level dyadic rule. -/
theorem dyadic_quadrature_chosen_level {n t r J : ℕ} {τ : ℝ}
    (scopes : Fin t → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (f : (i : Fin t) → LocalFunc (scopes i).card) (A K : Fin t → ℝ)
    (hK : ∀ i, 0 ≤ K i) (hA : ∀ i, (f i).BoundBy (A i))
    (hf : ∀ i, (f i).LipLe (K i)) (hτ : 0 < τ)
    (hJ : satisfies_level_choice J (∏ i, Dyadic.budget r (A i) (K i)) τ t) :
    |Integral.cubeIntegral (fun x => ∏ i, Integral.pullback (scopes i) (f i) x) -
        totalLevelRule (scopedIncrement scopes f) J| ≤ τ / 2 := by
  apply (dyadic_quadrature_error scopes hscopes f A K hK hA hf).trans
  have hprod : 0 < ∏ i, Dyadic.budget r (A i) (K i) :=
    Finset.prod_pos fun i _ => Dyadic.budget_pos r (A i) (K i)
  convert truncation_error_le hprod hτ hJ using 1
  ring

end Quadrature
end Paper08
