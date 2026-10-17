import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

/-!
# Independently reviewable statement model

This module imports only mathlib. It restates the finite dataset model,
costs, stable coresets, and squared-Hilbert features used by the paper
statements. Comparator checks that challenge and solution agree with these
types. This file is not regenerated from the proof library.
-/

noncomputable section

open scoped BigOperators

namespace GeometricMedianCoresets.Model

abbrev Dataset (X : Type*) (n : ℕ) := Fin n → X

structure Dist (X : Type*) where
  d : X → X → ℝ
  nonneg : ∀ x y, 0 ≤ d x y
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x y ≤ d x z + d z y

def Dist.cost {X : Type*} (D : Dist X) {n : ℕ} (A : Dataset X n) (z : X) : ℝ :=
  (∑ i, D.d z (A i)) / n

def Dist.delta {X : Type*} (D : Dist X) {n m : ℕ}
    (P : Dataset X n) (Q : Dataset X m) (x y : X) : ℝ :=
  (D.cost P x - D.cost P y) - (D.cost Q x - D.cost Q y)

def IsStableCoreset {X : Type*} (D : Dist X) {n m : ℕ}
    (P : Dataset X n) (Q : Dataset X m) (ε η : ℝ) : Prop :=
  ∀ x y : X, D.cost Q x ≤ (1 + ε) * D.cost Q y → D.cost P x ≤ (1 + η) * D.cost P y

def Dist.optimum {X : Type*} (D : Dist X) {n : ℕ} (P : Dataset X n) : ℝ :=
  sInf (Set.range (D.cost P))

def Dist.IsGeometricMedian {X : Type*} (D : Dist X) {n : ℕ}
    (P : Dataset X n) (μ : X) : Prop :=
  ∀ z : X, D.cost P μ ≤ D.cost P z

structure SquaredFeature (X : Type*) where
  H : Type
  [normed : NormedAddCommGroup H]
  [hilbert : InnerProductSpace ℝ H]
  d : X → X → ℝ
  Φ : X → H
  dist_sq : ∀ x y : X, ‖Φ x - Φ y‖ ^ 2 = d x y

attribute [instance] SquaredFeature.normed SquaredFeature.hilbert

structure SquaredMetric (X : Type*) extends SquaredFeature X where
  triangle : ∀ x y z : X, d x y ≤ d x z + d z y

namespace SquaredMetric

variable {X : Type*} (S : SquaredMetric X)

def v {n : ℕ} (A : Dataset X n) : S.H :=
  if n = 0 then 0 else (n : ℝ)⁻¹ • ∑ i, S.Φ (A i)

def b {n : ℕ} (A : Dataset X n) : ℝ :=
  if n = 0 then 0 else (n : ℝ)⁻¹ * ∑ i, ‖S.Φ (A i)‖ ^ 2

end SquaredMetric

end GeometricMedianCoresets.Model
