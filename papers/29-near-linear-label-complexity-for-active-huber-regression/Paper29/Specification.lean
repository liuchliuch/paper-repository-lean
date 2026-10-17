import Paper29.Defs
import Paper29.InformationDefs

/-! Independently readable statements for the deterministic numbered results.
This module imports definitions only. It does not import their solutions. -/
noncomputable section
namespace Paper29.Specification

def Lemma31 : Prop :=
  (∀ s t : ℝ, psi (s + t) ≤ psi s + psi t) ∧
  (∀ s t : ℝ, |psi s - psi t| ≤ psi (s - t)) ∧
  (∀ s t : ℝ, |huber s - huber t| ≤
    Real.sqrt (huber (s - t)) * (Real.sqrt (huber s) + Real.sqrt (huber t))) ∧
  (∀ (n : ℕ) (w y z : Fin n → ℝ), (∀ i, 0 ≤ w i) →
    Real.sqrt (weightedHuber w (y + z)) ≤
      Real.sqrt (weightedHuber w y) + Real.sqrt (weightedHuber w z))

def Lemma38 : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ),
    16 < n → (∀ i, 0 ≤ w i) → (∑ i, w i) ≤ 2 * (n : ℝ) →
    (∀ h, 1 / 2 ≤ unshifted A h → unshifted A h ≤ 8 * (n : ℝ) ^ 3 →
      |weightedHuber w (A.mulVec h) - unshifted A h| ≤ (1 / 16) * unshifted A h) →
    ∀ h, |weightedHuber w (A.mulVec h) - unshifted A h| ≤ (1 / 8) * unshifted A h

def Lemma41 : Prop :=
  ∀ N γ : ℝ, 1 ≤ N → 0 < γ → γ ≤ 1 / 2 →
    (∀ t, majorityObjective N γ (majorityMinimizer γ) ≤ majorityObjective N γ t) ∧
    (∀ t, t ≤ 1 / 2 →
      2 * γ * N * ((1 + 4 * γ) / (1 + 2 * γ)) ≤
        majorityObjective N γ t - majorityObjective N γ (majorityMinimizer γ) ∧
      2 * γ * N ≤ 2 * γ * N * ((1 + 4 * γ) / (1 + 2 * γ))) ∧
    (∀ t, majorityObjective N (-γ) (1 - majorityMinimizer γ) ≤
      majorityObjective N (-γ) t) ∧
    (∀ t, 1 / 2 ≤ t →
      2 * γ * N * ((1 + 4 * γ) / (1 + 2 * γ)) ≤
        majorityObjective N (-γ) t - majorityObjective N (-γ) (1 - majorityMinimizer γ) ∧
      2 * γ * N ≤ 2 * γ * N * ((1 + 4 * γ) / (1 + 2 * γ)))

/-- Lemma4.2 on the exact finite joint law of the two binary words. -/
def Lemma42 : Prop :=
  ∀ (r : ℕ) (P : RateDistortion.JointLaw r),
    (∀ s, P.source s = ((2 : ℝ) ^ r)⁻¹) →
    RateDistortion.expectedHamming P < (0.04 : ℝ) * r →
    RateDistortion.cRD * r ≤ P.mutualInformation ∧ (0.525 : ℝ) < RateDistortion.cRD

/-- Stronger explicit form of Proposition 5.1: absolute constants and optimizers
for every natural multiplicity N≥1. The two scalar objectives are exactly the
N+1-row, one-dimensional instances specified in Appendix B. -/
def Proposition51 : Prop :=
  ∀ N : ℕ, 1 ≤ N →
  let m : ℝ := N
  let G₂ : ℝ → ℝ := fun x => m * x ^ 2 + m * (x - 4) ^ 2
  let Ψ₂ : ℝ → ℝ := fun x => m * huber x + huber (Real.sqrt m * (x - 4))
  let G₁ : ℝ → ℝ := fun x => m * |x| + |m * x / 2 - 1|
  let Ψ₁ : ℝ → ℝ := fun x => m * huber x + huber (m * x / 2 - 1)
  (∀ x, G₂ 2 ≤ G₂ x) ∧
  (∀ x, G₂ x = G₂ 2 ↔ x = 2) ∧
  (∀ x, Ψ₂ (1 / Real.sqrt m) ≤ Ψ₂ x) ∧
  Ψ₂ 2 = 3 * m / 2 + 2 * Real.sqrt m - 1 / 2 ∧
  Ψ₂ (1 / Real.sqrt m) = 4 * Real.sqrt m - 1 ∧
  (Real.sqrt (Real.sqrt m) / 2 ≤ Real.sqrt (Ψ₂ 2) / Real.sqrt (Ψ₂ (1 / Real.sqrt m)) ∧
    Real.sqrt (Ψ₂ 2) / Real.sqrt (Ψ₂ (1 / Real.sqrt m)) ≤ Real.sqrt (Real.sqrt m)) ∧
  (∀ x, G₁ 0 ≤ G₁ x) ∧
  (∀ x, G₁ x = G₁ 0 ↔ x = 0) ∧
  (∀ x, Ψ₁ (2 / (m + 4)) ≤ Ψ₁ x) ∧
  Ψ₁ 0 = 1 / 2 ∧ Ψ₁ (2 / (m + 4)) = 2 / (m + 4) ∧
  Real.sqrt (Ψ₁ 0) / Real.sqrt (Ψ₁ (2 / (m + 4))) = Real.sqrt ((m + 4) / 4) ∧
  (Real.sqrt m / 2 ≤ Real.sqrt (Ψ₁ 0) / Real.sqrt (Ψ₁ (2 / (m + 4))) ∧
    Real.sqrt (Ψ₁ 0) / Real.sqrt (Ψ₁ (2 / (m + 4))) ≤ 2 * Real.sqrt m)

end Paper29.Specification
