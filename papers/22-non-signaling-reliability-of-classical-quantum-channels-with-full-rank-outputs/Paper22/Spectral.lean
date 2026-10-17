import Paper22.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Spectrum

/-!
# Spectral calculus for effects

Spectral inequalities used in effect completion: for an effect `T` (eigenvalues in `[0,1]`),
the operator `D = I - (I-T)^{1/2}` satisfies `0 ≤ D² ≤ D ≤ T`, and
`C = (I-T)^{1/2}` satisfies `C² = I - T`.
-/

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace Paper22

local instance matrixCStarAlgebra (n : ℕ) : CStarAlgebra (Matrix (Fin n) (Fin n) ℂ) where

/-- Continuous functional calculus square root of a PSD matrix. -/
def psdSqrt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  CFC.sqrt A

theorem psdSqrt_mul_self {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    psdSqrt A * psdSqrt A = A :=
  CFC.sqrt_mul_sqrt_self A hA.nonneg

theorem posSemidef_psdSqrt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    (psdSqrt A).PosSemidef :=
  (CFC.sqrt_nonneg A).posSemidef

/-- `C = (I-T)^{1/2}` for an effect-like `T`. -/
def effectSqrtC {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  psdSqrt (1 - T)

/-- `D = I - C`. -/
def effectD' {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 - effectSqrtC T

/-- The positive square root of the complement of an effect is positive. -/
theorem effectSqrtC_nonneg {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ effectSqrtC T := CFC.sqrt_nonneg _

/-- The square root of the complement squares to that complement. -/
theorem effectSqrtC_mul_self {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : IsEffect T) : effectSqrtC T * effectSqrtC T = 1 - T :=
  CFC.sqrt_mul_sqrt_self _ hT.one_sub_nonneg

/-- The square root of the complement is itself an effect. -/
theorem effectSqrtC_le_one {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : IsEffect T) : effectSqrtC T ≤ 1 := by
  simpa only [effectSqrtC, psdSqrt, CFC.sqrt_one] using
    CFC.sqrt_le_sqrt (1 - T) 1 (sub_le_self _ hT.nonneg)

/-- An effect is bounded above by its positive square root. -/
theorem le_psdSqrt_of_isEffect {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsEffect A) : A ≤ psdSqrt A := by
  have hs : A ^ 2 ≤ A := by
    simpa using CStarAlgebra.pow_antitone hA.nonneg hA.le_one (show 1 ≤ 2 by decide)
  simpa only [psdSqrt, CFC.sqrt_sq A hA.nonneg] using CFC.sqrt_le_sqrt (A ^ 2) A hs

/-- The complement of the square root is positive. -/
theorem effectD'_nonneg {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : IsEffect T) : 0 ≤ effectD' T := by
  exact sub_nonneg.mpr (effectSqrtC_le_one hT)

/-- Spectral comparison between the completion defect and the original effect. -/
theorem effectD'_le {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : IsEffect T) : effectD' T ≤ T := by
  have hc : IsEffect (1 - T) :=
    ⟨hT.one_sub_nonneg, sub_le_self _ hT.nonneg⟩
  have hs := sub_le_sub_left (le_psdSqrt_of_isEffect hc) (1 : Matrix (Fin n) (Fin n) ℂ)
  simpa only [effectD', effectSqrtC, sub_sub_cancel] using hs

/-- The defect is itself an effect. -/
theorem effectD'_isEffect {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : IsEffect T) : IsEffect (effectD' T) :=
  ⟨effectD'_nonneg hT, (effectD'_le hT).trans hT.le_one⟩

/-- The square of the positive completion defect is bounded by the defect. -/
theorem effectD'_mul_self_le {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : IsEffect T) : effectD' T * effectD' T ≤ effectD' T := by
  simpa only [pow_two, pow_one] using
    CStarAlgebra.pow_antitone (effectD'_isEffect hT).nonneg
      (effectD'_isEffect hT).le_one (show 1 ≤ 2 by decide)

/-- All spectral inequalities required in the effect-completion construction. -/
theorem effect_completion_spectral {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : IsEffect T) :
    0 ≤ effectSqrtC T ∧ effectSqrtC T ≤ 1 ∧
      effectSqrtC T * effectSqrtC T = 1 - T ∧
      0 ≤ effectD' T ∧ effectD' T ≤ T ∧
      effectD' T * effectD' T ≤ effectD' T :=
  ⟨effectSqrtC_nonneg T, effectSqrtC_le_one hT, effectSqrtC_mul_self hT,
    effectD'_nonneg hT, effectD'_le hT, effectD'_mul_self_le hT⟩

/-- Scalar spectral inequality: for `t ∈ [0,1]`, `0 ≤ 1 - √(1-t) ≤ t` and `(1-√(1-t))² ≤ 1-√(1-t)`. -/
theorem scalar_effect_ineq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ 1 - Real.sqrt (1 - t) ∧ 1 - Real.sqrt (1 - t) ≤ t ∧
      (1 - Real.sqrt (1 - t)) ^ 2 ≤ 1 - Real.sqrt (1 - t) := by
  have h1mt : 0 ≤ 1 - t := by linarith
  have hs : 0 ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (1 - t) ^ 2 = 1 - t := Real.sq_sqrt h1mt
  have hle : Real.sqrt (1 - t) ≤ 1 := by
    rw [Real.sqrt_le_iff]
    constructor <;> linarith
  have h0 : 0 ≤ 1 - Real.sqrt (1 - t) := by linarith
  have h1 : 1 - Real.sqrt (1 - t) ≤ t := by
    nlinarith [Real.sqrt_nonneg (1 - t), hs2, sq_nonneg (Real.sqrt (1 - t))]
  have h2 : (1 - Real.sqrt (1 - t)) ^ 2 ≤ 1 - Real.sqrt (1 - t) := by
    have : 0 ≤ 1 - Real.sqrt (1 - t) := h0
    nlinarith
  exact ⟨h0, h1, h2⟩

end Paper22

end
