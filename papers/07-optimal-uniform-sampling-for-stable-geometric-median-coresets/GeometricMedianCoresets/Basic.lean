import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Datasets, costs, and stable coresets (paper §1.1)

An indexed finite dataset lives in a type `X` equipped with a nonnegative
distance `d`. The cost of a candidate centre `z` is the average distance to
the dataset. Definition 1.1 (stable coreset) is a simultaneous implication
over all candidate pairs.
-/

noncomputable section

open scoped BigOperators

namespace GeometricMedianCoresets

/-- An indexed dataset of `n` points. Repeated locations are allowed. -/
abbrev Dataset (X : Type*) (n : ℕ) := Fin n → X

/-- Distance axioms actually used by the Euclidean / negative-type arguments. -/
structure Dist (X : Type*) where
  d : X → X → ℝ
  nonneg : ∀ x y, 0 ≤ d x y
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x y ≤ d x z + d z y

/-- Average cost `F_A(z)` of an indexed dataset. -/
def Dist.cost {X : Type*} (D : Dist X) {n : ℕ} (A : Dataset X n) (z : X) : ℝ :=
  (∑ i, D.d z (A i)) / n

theorem Dist.cost_nonneg {X : Type*} (D : Dist X) {n : ℕ}
    (A : Dataset X n) (z : X) : 0 ≤ D.cost A z := by
  unfold Dist.cost
  apply div_nonneg
  · exact Finset.sum_nonneg fun i _ => D.nonneg z (A i)
  · exact Nat.cast_nonneg _

/-- Pairwise comparison error `Δ_{P,Q}(x,y)` (equation (4)). -/
def Dist.delta {X : Type*} (D : Dist X) {n m : ℕ}
    (P : Dataset X n) (Q : Dataset X m) (x y : X) : ℝ :=
  (D.cost P x - D.cost P y) - (D.cost Q x - D.cost Q y)

/-- Definition 1.1: `Q` is a stable `(ε, η)`-coreset of `P`. -/
def IsStableCoreset {X : Type*} (D : Dist X) {n m : ℕ}
    (P : Dataset X n) (Q : Dataset X m) (ε η : ℝ) : Prop :=
  ∀ x y : X, D.cost Q x ≤ (1 + ε) * D.cost Q y → D.cost P x ≤ (1 + η) * D.cost P y

/-- When the sample is the whole dataset and `ε ≤ η`, stability holds deterministically. -/
theorem stable_of_full_of_le {X : Type*} (D : Dist X) {n : ℕ}
    (P : Dataset X n) {ε η : ℝ} (hεη : ε ≤ η) :
    IsStableCoreset D P P ε η := by
  intro x y h
  have hε : (1 + ε) ≤ (1 + η) := by linarith
  have hy : 0 ≤ D.cost P y := D.cost_nonneg P y
  have hmul : (1 + ε) * D.cost P y ≤ (1 + η) * D.cost P y :=
    mul_le_mul_of_nonneg_right hε hy
  calc D.cost P x ≤ (1 + ε) * D.cost P y := h
    _ ≤ (1 + η) * D.cost P y := hmul

/-- Geometric median optimum `OPT = inf_z F_P(z)`. -/
def Dist.optimum {X : Type*} (D : Dist X) {n : ℕ} (P : Dataset X n) : ℝ :=
  sInf (Set.range (D.cost P))

theorem Dist.optimum_bddBelow {X : Type*} (D : Dist X) {n : ℕ}
    (P : Dataset X n) : BddBelow (Set.range (D.cost P)) := by
  refine ⟨0, ?_⟩
  intro r hr
  obtain ⟨w, rfl⟩ := Set.mem_range.mp hr
  exact D.cost_nonneg P w

theorem Dist.optimum_le_cost {X : Type*} (D : Dist X) {n : ℕ}
    (P : Dataset X n) (z : X) : D.optimum P ≤ D.cost P z :=
  csInf_le (D.optimum_bddBelow P) (Set.mem_range_self z)

/-- An attained population 1-median. -/
def Dist.IsGeometricMedian {X : Type*} (D : Dist X) {n : ℕ}
    (P : Dataset X n) (μ : X) : Prop :=
  ∀ z : X, D.cost P μ ≤ D.cost P z

/-- Triangle inequality averaged over the population: `d(x,y) ≤ F_P(x)+F_P(y)`. -/
theorem triangle_avg {X : Type*} (D : Dist X) {n : ℕ} (hn : 0 < n)
    (P : Dataset X n) (x y : X) :
    D.d x y ≤ D.cost P x + D.cost P y := by
  have h : ∀ i, D.d x y ≤ D.d x (P i) + D.d (P i) y :=
    fun i => D.triangle x y (P i)
  have hsum : (n : ℝ) * D.d x y ≤ (∑ i, D.d x (P i)) + ∑ i, D.d (P i) y := by
    calc (n : ℝ) * D.d x y
        = ∑ _i : Fin n, D.d x y := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i, (D.d x (P i) + D.d (P i) y) := Finset.sum_le_sum fun i _ => h i
      _ = (∑ i, D.d x (P i)) + ∑ i, D.d (P i) y := Finset.sum_add_distrib
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have havg : (n : ℝ) * D.d x y / n ≤ ((∑ i, D.d x (P i)) + ∑ i, D.d (P i) y) / n :=
    div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
  have hdiv : (n : ℝ) * D.d x y / n = D.d x y := by field_simp
  have hsplit : ((∑ i, D.d x (P i)) + ∑ i, D.d (P i) y) / n
      = (∑ i, D.d x (P i)) / n + (∑ i, D.d (P i) y) / n := by ring
  have hsym : ((∑ i, D.d (P i) y) / n) = D.cost P y := by
    unfold Dist.cost
    congr 1
    exact Finset.sum_congr rfl fun i _ => D.symm (P i) y
  rw [hdiv, hsplit, hsym] at havg
  exact havg

/-- Optimality of the infimum: `2·OPT ≤ F_P(x)+F_P(y)`. -/
theorem two_opt_le {X : Type*} (D : Dist X) {n : ℕ}
    (P : Dataset X n) (x y : X) :
    2 * D.optimum P ≤ D.cost P x + D.cost P y := by
  have hx := D.optimum_le_cost P x
  have hy := D.optimum_le_cost P y
  linarith

/-- If a geometric median is attained, its cost equals the optimum. -/
theorem cost_median_eq_optimum {X : Type*} (D : Dist X) {n : ℕ}
    (P : Dataset X n) (μ : X) (hμ : D.IsGeometricMedian P μ) :
    D.cost P μ = D.optimum P := by
  apply le_antisymm
  · refine le_csInf ?_ ?_
    · exact ⟨D.cost P μ, Set.mem_range_self μ⟩
    · intro r hr
      obtain ⟨w, rfl⟩ := Set.mem_range.mp hr
      exact hμ w
  · exact D.optimum_le_cost P μ

end GeometricMedianCoresets
