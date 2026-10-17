import GeometricMedianCoresets.MainUpper
import GeometricMedianCoresets.CostIdentity

/-! Enumerating actual sample indices preserves both the costs and feature means. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace GeometricMedianCoresets

/-- The indexed subdataset with exactly the indices in `I`. -/
def indexedSample {X : Type*} {n : ℕ} (P : Dataset X n) (I : Finset (Fin n)) :
    Dataset X I.card := fun j => P ((I.equivFin.symm j).val)

theorem sum_indexedSample {X M : Type*} [AddCommMonoid M] {n : ℕ}
    (P : Dataset X n) (I : Finset (Fin n)) (f : X → M) :
    ∑ j, f (indexedSample P I j) = ∑ i ∈ I, f (P i) := by
  classical
  exact (I.equivFin.symm.sum_comp (fun i : I => f (P i))).trans
    (Finset.sum_coe_sort I (fun i => f (P i)))

theorem cost_indexedSample {X : Type*} (D : Dist X) {n m : ℕ}
    (P : Dataset X n) (I : Finset (Fin n)) (hI : I.card = m) (z : X) :
    D.cost (indexedSample P I) z = sampleCostM D P z m I := by
  unfold Dist.cost sampleCostM
  rw [sum_indexedSample, hI]
  congr 1
  exact Finset.sum_congr rfl fun i _ => D.symm z (P i)

/-- Anchoring a squared feature map preserves its distances and triangle inequality. -/
def SquaredMetric.anchored {X : Type*} (S : SquaredMetric X) (μ : X) :
    SquaredMetric X where
  H := S.H
  d := S.d
  Φ := anchoredFeature S μ
  dist_sq x y := by
    have heq : anchoredFeature S μ x - anchoredFeature S μ y = S.Φ x - S.Φ y := by
      unfold anchoredFeature
      abel
    rw [heq, S.dist_sq]
  triangle := S.triangle

theorem SquaredMetric.anchored_toDist {X : Type*} (S : SquaredMetric X) (μ : X) :
    (S.anchored μ).toDist = S.toDist := rfl

theorem v_indexedSample {X : Type*} (S : SquaredMetric X) {n : ℕ}
    (P : Dataset X n) (I : Finset (Fin n)) :
    S.v (indexedSample P I) = FinitePopulation.sampleMean (fun i => S.Φ (P i)) I := by
  unfold SquaredMetric.v FinitePopulation.sampleMean
  rw [sum_indexedSample]
  rfl

theorem v_population {X : Type*} (S : SquaredMetric X) {n : ℕ} (P : Dataset X n) :
    S.v P = FinitePopulation.popMean (fun i => S.Φ (P i)) := rfl

/-- Equation (6) with the actual sample and the anchored empirical mean error. -/
theorem delta_indexedSample {X : Type*} (S : SquaredMetric X) {n : ℕ}
    (hn : 0 < n) (P : Dataset X n) (I : Finset (Fin n)) (hI : 0 < I.card)
    (μ x y : X) :
    S.toDist.delta P (indexedSample P I) x y =
      2 * ⟪S.Φ x - S.Φ y,
        FinitePopulation.sampleMean (fun i => anchoredFeature S μ (P i)) I -
        FinitePopulation.popMean (fun i => anchoredFeature S μ (P i))⟫ := by
  have hid := (S.anchored μ).delta_eq_inner hn.ne' hI.ne' P (indexedSample P I) x y
  rw [SquaredMetric.anchored_toDist, v_indexedSample, v_population] at hid
  have heq : (S.anchored μ).Φ x - (S.anchored μ).Φ y = S.Φ x - S.Φ y := by
    change (S.Φ x - S.Φ μ) - (S.Φ y - S.Φ μ) = _
    abel
  rw [heq] at hid
  exact hid

end GeometricMedianCoresets
