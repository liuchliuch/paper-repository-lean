import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import GeometricMedianCoresets.Basic
import GeometricMedianCoresets.GeometricInequalities

/-!
# Stability from relative comparison (paper Lemma 2.6)

If a sample satisfies `|Δ_{P,Q}(x,y)| ≤ ε [F_P(x)+F_P(y)]` for all `x, y`
and `F_Q(μ) ≤ 10 OPT`, then `Q` is a stable `(ε, 17ε)`-coreset of `P`
for `0 < ε < 1/4`.
-/

noncomputable section

namespace GeometricMedianCoresets

/-- The one-sided cost domination step of equation (14). -/
theorem cost_upper_from_delta {ε fp opt fq fqμ : ℝ}
    (hε : 0 < ε) (hopt : opt ≤ fp)
    (hΔ : -ε * (fp + opt) ≤ (fp - opt) - (fq - fqμ))
    (href : fqμ ≤ 10 * opt) :
    fq ≤ (10 + 2 * ε) * fp := by
  have hdom : fq ≤ (1 + ε) * fp + (9 + ε) * opt := by linarith
  have hmul := mul_le_mul_of_nonneg_left hopt (by linarith : 0 ≤ 9 + ε)
  nlinarith

/-- Transfer inequality (15) in full scalar form. -/
theorem transfer_inequality
    {ε fp_x fp_y fq_x fq_y : ℝ}
    (hε : 0 < ε)
    (_hnonneg : 0 ≤ fp_x ∧ 0 ≤ fp_y ∧ 0 ≤ fq_x ∧ 0 ≤ fq_y)
    (hΔ : fp_x - fp_y ≤ (fq_x - fq_y) + ε * (fp_x + fp_y))
    (hcomp : fq_x ≤ (1 + ε) * fq_y)
    (hdom : fq_y ≤ (10 + 2 * ε) * fp_y) :
    (1 - ε) * fp_x ≤ (1 + 11 * ε + 2 * ε ^ 2) * fp_y := by
  have h1 : fp_x - fp_y ≤ ε * fq_y + ε * (fp_x + fp_y) := by
    have : fq_x - fq_y ≤ ε * fq_y := by nlinarith
    nlinarith
  nlinarith [h1, hdom]

/-- Lemma 2.6 (deterministic scalar form). -/
theorem lemma_2_6_core
    {ε fp_x fp_y fp_μ fq_x fq_y fq_μ : ℝ}
    (hε : 0 < ε) (hε' : ε < 1/4)
    (_hnonneg : 0 ≤ fp_x ∧ 0 ≤ fp_y ∧ 0 ≤ fp_μ ∧ 0 ≤ fq_x ∧ 0 ≤ fq_y ∧ 0 ≤ fq_μ)
    (_hopt_le_x : fp_μ ≤ fp_x) (hopt_le_y : fp_μ ≤ fp_y)
    (hΔxy : fp_x - fp_y - (fq_x - fq_y) ≤ ε * (fp_x + fp_y))
    (hΔyμ : fp_y - fp_μ - (fq_y - fq_μ) ≤ ε * (fp_y + fp_μ))
    (hΔyμ' : -ε * (fp_y + fp_μ) ≤ fp_y - fp_μ - (fq_y - fq_μ))
    (href : fq_μ ≤ 10 * fp_μ)
    (hcomp : fq_x ≤ (1 + ε) * fq_y) :
    fp_x ≤ (1 + 17 * ε) * fp_y := by
  -- One-sided domination at y (eq. 14)
  have hdom_pre : fq_y ≤ fp_y - fp_μ + fq_μ + ε * (fp_y + fp_μ) := by
    nlinarith [hΔyμ]
  have hdom_mid : fq_y ≤ (1 + ε) * fp_y + (9 + ε) * fp_μ := by
    nlinarith [hdom_pre, href]
  have hdom : fq_y ≤ (10 + 2 * ε) * fp_y := by
    nlinarith [hdom_mid, hopt_le_y, hε']
  have htransfer : (1 - ε) * fp_x ≤ (1 + 11 * ε + 2 * ε ^ 2) * fp_y := by
    refine transfer_inequality hε ?_ ?_ hcomp hdom
    · exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
    · nlinarith [hΔxy]
  have hε5 : ε < 5/19 := eps_lt_five_nineteenth hε hε'
  exact transfer_stability hε hε5 htransfer (by nlinarith)

/-- Lemma 2.6 packaged as a stable-coreset statement for a general `Dist`. -/
theorem lemma_2_6_stable {X : Type*} (D : Dist X) {n m : ℕ}
    (P : Dataset X n) (Q : Dataset X m)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    {μ : X} (hμ : D.IsGeometricMedian P μ)
    (hΔ : ∀ x y : X, |D.delta P Q x y| ≤ ε * (D.cost P x + D.cost P y))
    (href : D.cost Q μ ≤ 10 * D.cost P μ) :
    IsStableCoreset D P Q ε (17 * ε) := by
  intro x y hcomp
  have hΔxy_abs := hΔ x y
  have hΔyμ_abs := hΔ y μ
  -- Unfold delta to raw cost differences
  have hd_xy : D.delta P Q x y
      = (D.cost P x - D.cost P y) - (D.cost Q x - D.cost Q y) := rfl
  have hd_yμ : D.delta P Q y μ
      = (D.cost P y - D.cost P μ) - (D.cost Q y - D.cost Q μ) := rfl
  rw [hd_xy] at hΔxy_abs
  rw [hd_yμ] at hΔyμ_abs
  rw [abs_le] at hΔxy_abs hΔyμ_abs
  have hnn : 0 ≤ D.cost P x ∧ 0 ≤ D.cost P y ∧ 0 ≤ D.cost P μ
      ∧ 0 ≤ D.cost Q x ∧ 0 ≤ D.cost Q y ∧ 0 ≤ D.cost Q μ :=
    ⟨D.cost_nonneg P x, D.cost_nonneg P y, D.cost_nonneg P μ,
      D.cost_nonneg Q x, D.cost_nonneg Q y, D.cost_nonneg Q μ⟩
  have hΔyμ_lo : -ε * (D.cost P y + D.cost P μ)
      ≤ D.cost P y - D.cost P μ - (D.cost Q y - D.cost Q μ) := by
    have := hΔyμ_abs.1
    nlinarith
  have hcore := lemma_2_6_core hε hε' hnn (hμ x) (hμ y)
    hΔxy_abs.2 hΔyμ_abs.2 hΔyμ_lo href hcomp
  have : (1 + 17 * ε) = 1 + (17 * ε) := by ring
  rw [this]
  exact hcore

end GeometricMedianCoresets
