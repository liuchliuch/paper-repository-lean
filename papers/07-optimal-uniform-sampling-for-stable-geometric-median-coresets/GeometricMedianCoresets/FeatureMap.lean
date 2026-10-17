import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import GeometricMedianCoresets.Basic

/-!
# Squared-Hilbert feature maps (paper §2, Lemma 2.1, eq. (3), (20))

A feature map `Φ : X → H` into a real Hilbert space is *squared-distance
preserving* for a distance `d` when `‖Φ x - Φ y‖^2 = d x y` for all `x y`.
-/

noncomputable section

open scoped BigOperators

namespace GeometricMedianCoresets

/-- Distance axioms together with a squared-distance feature map into a
real Hilbert space `H`. -/
structure SquaredFeature (X : Type*) where
  /-- Ambient Hilbert space of features. -/
  H : Type
  [normed : NormedAddCommGroup H]
  [hilbert : InnerProductSpace ℝ H]
  /-- Underlying distance on `X`. -/
  d : X → X → ℝ
  /-- Feature map. -/
  Φ : X → H
  /-- Squared Hilbert distance realizes `d` (eq. (3) / (20)). -/
  dist_sq : ∀ x y : X, ‖Φ x - Φ y‖ ^ 2 = d x y

attribute [instance] SquaredFeature.normed SquaredFeature.hilbert

namespace SquaredFeature

variable {X : Type*} (S : SquaredFeature X)

theorem d_nonneg (x y : X) : 0 ≤ S.d x y := by
  rw [← S.dist_sq x y]
  exact sq_nonneg _

theorem d_symm (x y : X) : S.d x y = S.d y x := by
  rw [← S.dist_sq x y, ← S.dist_sq y x]
  simp [norm_sub_rev]

theorem d_self (x : X) : S.d x x = 0 := by
  have h := S.dist_sq x x
  simp at h
  exact Eq.symm h

theorem norm_sub_sq_d (x y : X) : ‖S.Φ x - S.Φ y‖ ^ 2 = S.d x y :=
  S.dist_sq x y

end SquaredFeature

/-- A squared-feature map whose induced `d` is a genuine metric
(needed for the averaged triangle inequality in Proposition 2.4). -/
structure SquaredMetric (X : Type*) extends SquaredFeature X where
  triangle : ∀ x y z : X, d x y ≤ d x z + d z y

namespace SquaredMetric

variable {X : Type*} (S : SquaredMetric X)

def toDist : Dist X where
  d := S.d
  nonneg := S.d_nonneg
  symm := S.d_symm
  triangle := S.triangle

/-- Anchored feature `Φ(x) - Φ(μ)`. -/
def Φ₀ (μ : X) (x : X) : S.H := S.Φ x - S.Φ μ

theorem Φ₀_self (μ : X) : S.Φ₀ μ μ = 0 := by
  simp [Φ₀]

theorem Φ₀_norm_sq (μ x : X) : ‖S.Φ₀ μ x‖ ^ 2 = S.d x μ := by
  have h := S.dist_sq x μ
  have hrev : ‖S.Φ x - S.Φ μ‖ ^ 2 = S.d x μ := h
  have : ‖S.Φ x - S.Φ μ‖ = ‖S.Φ₀ μ x‖ := by simp [Φ₀]
  rw [← this]
  exact hrev

/-- Mean feature vector `v_A = (1/n) Σ Φ(p_i)` of an indexed dataset. -/
def v {n : ℕ} (A : Dataset X n) : S.H :=
  if h : n = 0 then 0 else (n : ℝ)⁻¹ • ∑ i, S.Φ (A i)

/-- Constant `b_A = (1/n) Σ ‖Φ(p_i)‖^2`. -/
def b {n : ℕ} (A : Dataset X n) : ℝ :=
  if h : n = 0 then 0 else (n : ℝ)⁻¹ * ∑ i, ‖S.Φ (A i)‖ ^ 2

end SquaredMetric

end GeometricMedianCoresets
