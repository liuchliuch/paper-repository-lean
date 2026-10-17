import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import GeometricMedianCoresets.Basic
import GeometricMedianCoresets.FeatureMap
import GeometricMedianCoresets.VarianceCount
import GeometricMedianCoresets.VarianceBinomial
import GeometricMedianCoresets.VarianceBound
import GeometricMedianCoresets.UniformProbability

/-!
# Anchored features and sample-cost mean (9/10 preparation)
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace GeometricMedianCoresets

def anchoredFeature {X : Type*} (S : SquaredMetric X) (μ : X) (p : X) : S.H :=
  S.Φ p - S.Φ μ

theorem anchoredFeature_norm_sq {X : Type*} (S : SquaredMetric X) (μ p : X) :
    ‖anchoredFeature S μ p‖ ^ 2 = S.d p μ := by
  unfold anchoredFeature
  have h := S.dist_sq p μ
  rw [← h]

theorem anchored_second_moment {X : Type*} (S : SquaredMetric X) {n : ℕ}
    (hn : 0 < n) (P : Dataset X n) (μ : X) :
    (1:ℝ) / n * ∑ i, ‖anchoredFeature S μ (P i)‖ ^ 2
      = S.toDist.cost P μ := by
  have h := fun i => anchoredFeature_norm_sq S μ (P i)
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  have hsym : ∀ i, S.d (P i) μ = S.toDist.d μ (P i) := fun i => S.d_symm (P i) μ
  rw [Finset.sum_congr rfl (fun i _ => hsym i)]
  unfold Dist.cost
  field_simp

theorem sum_sum_dist_eq {X : Type*} (D : Dist X) {n m : ℕ}
    (P : Dataset X n) (μ : X) (hm : 1 ≤ m) (hmn : m ≤ n) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ∑ i ∈ I, D.d (P i) μ)
      = (n - 1).choose (m - 1) * ∑ i, D.d (P i) μ := by
  classical
  have h : ∀ I : Finset (Fin n), (∑ i ∈ I, D.d (P i) μ)
      = ∑ i ∈ (Finset.univ : Finset (Fin n)),
          (if i ∈ I then D.d (P i) μ else 0) := by
    intro I
    have h' : (∑ i ∈ (Finset.univ : Finset (Fin n)),
          (if i ∈ I then D.d (P i) μ else 0)) = ∑ i ∈ I, D.d (P i) μ := by
      rw [← Finset.sum_filter]
      simp
    exact h'.symm
  rw [Finset.sum_congr rfl (fun I _ => h I), Finset.sum_comm]
  have h2 : ∀ i : Fin n,
      (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        (if i ∈ I then D.d (P i) μ else 0))
      = D.d (P i) μ
          * (((Finset.univ : Finset (Fin n)).powersetCard m).filter
              (fun s => i ∈ s)).card := by
    intro i
    rw [Finset.sum_ite]
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h2 i)]
  have hcount : ∀ i : Fin n,
      (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun s => i ∈ s)).card = (n - 1).choose (m - 1) := fun i =>
    VarianceCount.card_filter_mem n m i hm hmn
  rw [Finset.sum_congr rfl (fun i _ => by rw [hcount i])]
  have : (∑ x, D.d (P x) μ * ((n - 1).choose (m - 1) : ℝ))
      = ∑ x, ((n - 1).choose (m - 1) : ℝ) * D.d (P x) μ :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [this, ← Finset.mul_sum]



/-- Mean of sample cost at `μ` equals the population cost at `μ`. -/
theorem mean_sampleCost_eq {X : Type*} (D : Dist X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset X n) (μ : X) :
    FinitePopulation.uniformAvg (m := m) (fun I =>
      ((∑ i ∈ I, D.d (P i) μ) : ℝ) / m)
      = D.cost P μ := by
  unfold FinitePopulation.uniformAvg
  have hsum : (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      (∑ i ∈ I, D.d (P i) μ) / m)
      = (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
          ∑ i ∈ I, D.d (P i) μ) / m := by
    rw [Finset.sum_div]
  rw [hsum, sum_sum_dist_eq D P μ hm hmn]
  have h2 : ((n - 1).choose (m - 1) : ℝ) / (n.choose m : ℝ) = (m : ℝ) / n := by
    have h := VarianceBinomial.choose_mul_eq_choose_pred n m hm hmn
    have hcast : (n.choose m : ℝ) * m = ((n - 1).choose (m - 1) : ℝ) * n := by
      exact_mod_cast h
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hC : (n.choose m : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hmn).ne'
    field_simp at hcast ⊢
    nlinarith
  have ha : (n.choose m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hmn).ne'
  have hb : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hc : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h4 : (((n - 1).choose (m - 1) : ℝ) * ∑ i, D.d (P i) μ) * n
      = ((∑ i, D.d (P i) μ) * m) * (n.choose m : ℝ) := by
    have h2f : ((n - 1).choose (m - 1) : ℝ) * n = (n.choose m : ℝ) * m := by
      field_simp at h2
      nlinarith
    calc (((n - 1).choose (m - 1) : ℝ) * ∑ i, D.d (P i) μ) * n
          = (((n - 1).choose (m - 1) : ℝ) * n) * ∑ i, D.d (P i) μ := by ring
        _ = ((n.choose m : ℝ) * m) * ∑ i, D.d (P i) μ := by rw [h2f]
        _ = (∑ i, D.d (P i) μ) * m * (n.choose m : ℝ) := by ring
  have hsym : ∀ i, D.d (P i) μ = D.d μ (P i) := fun i => D.symm (P i) μ
  have hsumsym : ∑ i, D.d (P i) μ = ∑ i, D.d μ (P i) :=
    Finset.sum_congr rfl fun i _ => hsym i
  -- goal: (C1 * S) / m / C = (∑ i, D.d μ (P i)) / n
  have hgoal : (((n - 1).choose (m - 1) : ℝ) * ∑ i, D.d (P i) μ) / m / (n.choose m : ℝ)
      = (∑ i, D.d (P i) μ) / n := by
    have ha2 : (n.choose m : ℝ) ≠ 0 := ha
    have hb2 : (m:ℝ) ≠ 0 := hb
    have hc2 : (n:ℝ) ≠ 0 := hc
    field_simp
    nlinarith [h4]
  rw [hgoal, hsumsym]
  unfold Dist.cost
  ring

end GeometricMedianCoresets
