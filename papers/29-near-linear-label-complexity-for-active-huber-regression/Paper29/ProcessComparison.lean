import Paper29.IncrementMetric
import Paper29.HuberProcesses
import Paper29.ExternalProcess
import Mathlib.Tactic.FieldSimp

noncomputable section
open scoped BigOperators ENNReal
namespace Paper29.ProcessTools

/-- The design-only all-radius geometry used downstream of Lemma3.4. -/
def ScoreGeometry {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (τ : Fin n → ℝ) (G : ℝ) : Prop :=
  ∀ R : ℝ, 0 < R →
    Chaining.gamma2 (T := Ball A R) (fun h k => Chaining.huberMetric A τ h k) ≤
      ENNReal.ofReal (G * Real.sqrt R)

def alpha (C G T : ℝ) (m : ℕ) : ℝ := 2 * C * G * Real.sqrt (T / m)

theorem shifted_metric_le {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z τ π : Fin n → ℝ) (T : ℝ) (hT : 0 < T) (hτ : ∀ i, 0 < τ i)
    (hπ : ∀ i, 0 < π i) (hm : 0 < m) (hrel : ∀ i, τ i = T * π i)
    {R : ℝ} (hR : 0 ≤ R) (ν : Fin m → Fin n) (h k : Ball A R) :
    sampleMetric π (affineClass A z R) ν h k ≤
      ENNReal.ofReal (2 * Real.sqrt (T / m) * Real.sqrt (shiftedEnvelope A z π R ν)) *
        Chaining.huberMetric A τ h k := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let D : ℝ := (Chaining.huberMetric A τ h k).toReal
  let L : ℝ := shiftedEnvelope A z π R ν
  let c : ℝ := 2 * Real.sqrt (T / m) * Real.sqrt L
  have hL : 0 ≤ L := shiftedEnvelope_nonneg A z π (fun i => (hπ i).le) hR ν
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hD : 0 ≤ D := ENNReal.toReal_nonneg
  have hc2 : c ^ 2 = 4 * (T / m) * L := by
    dsimp [c]
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hT.le hmR.le), Real.sq_sqrt hL]
    ring
  have hh := le_supremum _ (sampledShifted_bdd A z π (fun i => (hπ i).le) hR ν) h
  have hk := le_supremum _ (sampledShifted_bdd A z π (fun i => (hπ i).le) hR ν) k
  change Sampling.sampledShifted π ν A z h ≤ L at hh
  change Sampling.sampledShifted π ν A z k ≤ L at hk
  have hs := shifted_metric_sq A z τ π T hτ hπ hm hrel ν h k
  have hprod := mul_le_mul_of_nonneg_left (add_le_add hh hk)
    (show 0 ≤ (2 * T / m) * D ^ 2 by positivity)
  have hsq : (∑ j, ((affineClass A z R (ν j) h - affineClass A z R (ν j) k) /
      ((m : ℝ) * π (ν j))) ^ 2) ≤ (c * D) ^ 2 := by
    change _ ≤ (2 * T / m) * D ^ 2 * _ at hs
    have he : (c * D) ^ 2 = (2 * T / m) * D ^ 2 * (L + L) := by
      rw [mul_pow, hc2]
      ring
    rw [he]
    exact hs.trans hprod
  have hreal : Real.sqrt (∑ j, ((affineClass A z R (ν j) h - affineClass A z R (ν j) k) /
      ((m : ℝ) * π (ν j))) ^ 2) ≤ c * D := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hc hD)).1
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact hsq
  calc
    _ ≤ ENNReal.ofReal (c * D) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal (huberMetric_ne_top A τ h k)]

/-- General external chaining is applied to the *actual* centered coefficients;
the Huber-specific metric comparison is the theorem above. -/
theorem affine_chaining_comparison {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z τ π : Fin n → ℝ) (T C G : ℝ) (hT : 0 < T) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (external : ExternalProcess.AnchoredChaining C)
    (hτ : ∀ i, 0 < τ i) (hπ : ∀ i, 0 < π i) (hsum : ∑ i, π i = 1)
    (hm : 0 < m) (hrel : ∀ i, τ i = T * π i) (cover : ScoreGeometry A τ G)
    {R : ℝ} (hR : 0 < R) :
    Sampling.expectation π (errorSup (m := m) π (affineClass A z R)) ≤
      alpha C G T m * Real.sqrt R *
        Sampling.expectation π (fun ν : Fin m → Fin n => Real.sqrt (shiftedEnvelope A z π R ν)) := by
  let Γ : (Fin m → Fin n) → ℝ := fun ν =>
    (2 * Real.sqrt (T / m) * Real.sqrt (shiftedEnvelope A z π R ν)) * (G * Real.sqrt R)
  have hΓ : ∀ ν, 0 ≤ Γ ν := by intro ν; dsimp [Γ]; positivity
  have hgamma (ν : Fin m → Fin n) :
      Chaining.gamma2 (sampleMetric π (affineClass A z R) ν) ≤ ENNReal.ofReal (Γ ν) := by
    have hc : 0 ≤ 2 * Real.sqrt (T / m) * Real.sqrt (shiftedEnvelope A z π R ν) := by positivity
    have hm := Chaining.gamma2_le_mul (sampleMetric π (affineClass A z R) ν)
      (fun h k : Ball A R => Chaining.huberMetric A τ h k)
      (ENNReal.ofReal (2 * Real.sqrt (T / m) * Real.sqrt (shiftedEnvelope A z π R ν)))
      ENNReal.ofReal_ne_top (shifted_metric_le A z τ π T hT hτ hπ hm hrel hR.le ν)
    have hg := mul_le_mul_left' (cover R hR)
      (ENNReal.ofReal (2 * Real.sqrt (T / m) * Real.sqrt (shiftedEnvelope A z π R ν)))
    exact (hm.trans hg).trans_eq (ENNReal.ofReal_mul hc).symm
  have hanchor : ∀ i, affineClass A z R i (zeroBall A hR.le) = 0 := by
    intro i
    simp [affineClass, zeroBall, Matrix.mulVec_zero]
  have he := external n m (Ball A R) (zeroBall A hR.le) π (affineClass A z R)
    hm hπ hsum hanchor (affineClass_bounded A z R) Γ hΓ hgamma
  have heq : Γ = fun ν => (2 * Real.sqrt (T / m) * G * Real.sqrt R) *
      Real.sqrt (shiftedEnvelope A z π R ν) := by funext ν; dsimp [Γ]; ring
  rw [heq, expectation_mul_const] at he
  unfold alpha
  nlinarith only [he]

end Paper29.ProcessTools
