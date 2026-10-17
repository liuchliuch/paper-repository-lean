import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith

/-!
# Minimizer transport and stage contraction (paper Lemma 4.1)

These statements are formulated for an arbitrary normed additive group.  In
particular the transport argument does not require an inner product.  All
minimizers below are actual global minimizers of the stated functions.
-/

namespace P31

variable {E : Type*} [SeminormedAddCommGroup E]

/-- Adding a positive multiple of a radial power cannot move the new minimizer
farther from the center than an old minimizer.  This is the comparison of the
two genuine minimizing inequalities in the proof of Lemma 4.1. -/
theorem minimizer_transport
    (F : E → ℝ) (center oldMin newMin : E) (c p : ℝ)
    (hc : 0 < c) (hp : 0 < p)
    (hOld : ∀ y, F oldMin ≤ F y)
    (hNew : ∀ y,
      F newMin + c * ‖newMin - center‖ ^ p ≤
        F y + c * ‖y - center‖ ^ p) :
    ‖newMin - center‖ ≤ ‖oldMin - center‖ := by
  have hPower : c * ‖newMin - center‖ ^ p ≤ c * ‖oldMin - center‖ ^ p := by
    have h₁ := hOld newMin
    have h₂ := hNew oldMin
    linarith
  have h := (mul_le_mul_iff_right₀ hc).mp hPower
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp).mp h

/-- A radial growth inequality at an exact minimizer and an objective gap
certificate give the prescribed distance contraction.  For the paper, the
coefficient is `σ / p`, the growth inequality is the uniform convexity
consequence (2.2), and the gap certificate is (3.8). -/
theorem stage_contraction
    (F : E → ℝ) (x exactMin : E) (c p δ : ℝ)
    (hc : 0 < c) (hp : 0 < p) (hδ : 0 ≤ δ)
    (hGrowth : c * ‖x - exactMin‖ ^ p ≤ F x - F exactMin)
    (hGap : F x - F exactMin ≤ c * δ ^ p) :
    ‖x - exactMin‖ ≤ δ := by
  have hPower : ‖x - exactMin‖ ^ p ≤ δ ^ p :=
    (mul_le_mul_iff_right₀ hc).mp (hGrowth.trans hGap)
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) hδ hp).mp hPower

/-- One complete step of Lemma 4.1: the previous certified radius is a valid
warm start for the new exact minimizer, and the new objective gap contracts
the computed point.  `c` is the positive coefficient of the newly added atom;
`growth` is the positive coefficient in the full objective's growth bound. -/
theorem minimizer_transport_and_contraction
    (F : E → ℝ) (center oldMin newMin x : E)
    (c growth p previousRadius nextRadius : ℝ)
    (hc : 0 < c) (hgrowth : 0 < growth) (hp : 0 < p)
    (hNextRadius : 0 ≤ nextRadius)
    (hPrevious : ‖center - oldMin‖ ≤ previousRadius)
    (hOld : ∀ y, F oldMin ≤ F y)
    (hNew : ∀ y,
      F newMin + c * ‖newMin - center‖ ^ p ≤
        F y + c * ‖y - center‖ ^ p)
    (hGrowth : growth * ‖x - newMin‖ ^ p ≤
      (F x + c * ‖x - center‖ ^ p) -
        (F newMin + c * ‖newMin - center‖ ^ p))
    (hGap : (F x + c * ‖x - center‖ ^ p) -
        (F newMin + c * ‖newMin - center‖ ^ p) ≤
      growth * nextRadius ^ p) :
    ‖newMin - center‖ ≤ previousRadius ∧ ‖x - newMin‖ ≤ nextRadius := by
  constructor
  · exact (minimizer_transport F center oldMin newMin c p hc hp hOld hNew).trans
      (by simpa only [norm_sub_rev] using hPrevious)
  · exact stage_contraction
      (fun y => F y + c * ‖y - center‖ ^ p) x newMin
      growth p nextRadius hgrowth hp hNextRadius hGrowth hGap

/-- The complete finite sequence form of Lemma 4.1.  The objectives really are
successive additions of positive shifted powers, their stated exact points
really minimize them, and each computed point has the stage objective gap.
The growth bounds are the consequence (2.2) of uniform convexity. -/
theorem stagewise_transport_and_contraction
    (F : ℕ → E → ℝ) (x exactMin : ℕ → E)
    (coefficient growth δ : ℕ → ℝ) (p : ℝ) (S : ℕ)
    (hp : 0 < p)
    (hInitial : ‖x 0 - exactMin 0‖ ≤ δ 0)
    (hRadius : ∀ s, 1 ≤ s → s ≤ S → 0 ≤ δ s)
    (hCoefficient : ∀ s, 1 ≤ s → s ≤ S → 0 < coefficient s)
    (hGrowthCoefficient : ∀ s, 1 ≤ s → s ≤ S → 0 < growth s)
    (hMin : ∀ s, s ≤ S → ∀ y, F s (exactMin s) ≤ F s y)
    (hStep : ∀ s, 1 ≤ s → s ≤ S → ∀ y,
      F s y = F (s - 1) y + coefficient s * ‖y - x (s - 1)‖ ^ p)
    (hGrowth : ∀ s, 1 ≤ s → s ≤ S → ∀ y,
      growth s * ‖y - exactMin s‖ ^ p ≤ F s y - F s (exactMin s))
    (hGap : ∀ s, 1 ≤ s → s ≤ S →
      F s (x s) - F s (exactMin s) ≤ growth s * δ s ^ p) :
    ∀ s, 1 ≤ s → s ≤ S →
      ‖exactMin s - x (s - 1)‖ ≤ δ (s - 1) ∧
        ‖x s - exactMin s‖ ≤ δ s := by
  have hComputed : ∀ s, s ≤ S → ‖x s - exactMin s‖ ≤ δ s := by
    intro s hs
    cases s with
    | zero => exact hInitial
    | succ s =>
        exact stage_contraction (F (s + 1)) (x (s + 1)) (exactMin (s + 1))
          (growth (s + 1)) p (δ (s + 1)) (hGrowthCoefficient _ (by omega) hs)
          hp (hRadius _ (by omega) hs) (hGrowth _ (by omega) hs _) (hGap _ (by omega) hs)
  intro s hs hsS
  constructor
  · have hTransport := minimizer_transport (F (s - 1)) (x (s - 1))
      (exactMin (s - 1)) (exactMin s) (coefficient s) p
      (hCoefficient s hs hsS) hp (hMin (s - 1) (by omega))
      (by
        intro y
        simpa only [← hStep s hs hsS] using hMin s hsS y)
    exact hTransport.trans (by simpa only [norm_sub_rev] using hComputed (s - 1) (by omega))
  · exact hComputed s hsS

end P31
