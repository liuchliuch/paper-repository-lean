import GeometricMedianCoresets.AsymptoticRate
import GeometricMedianCoresets.Remark25
import GeometricMedianCoresets.EuclideanMetric
import GeometricMedianCoresets.L1Metric
import GeometricMedianCoresets.NegativeType
import GeometricMedianCoresets.ApproximateReference
import GeometricMedianCoresets.VarianceComplete
import GeometricMedianCoresets.AppendixA
import Verification.Solution

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace GeometricMedianCoresets.Challenge

theorem gaussian_embedding {d : ℕ} (μ x y : Euclidean.Space d) :
    ‖Euclidean.feature μ x - Euclidean.feature μ y‖ ^ 2 = ‖x - y‖ :=
  Euclidean.feature_dist_sq μ x y

theorem euclidean_upper {d n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset (Euclidean.Space d) n) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    (hmsize : ⌈20 / (ε * ε)⌉₊ ≤ m) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset (normDist (Euclidean.Space d)) P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 :=
  Euclidean.thm_1_2_i hn hm hmn P hε hε' hmsize

theorem l1_upper {d n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset (L1.Space d) n) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    (hmsize : ⌈20 / (ε * ε)⌉₊ ≤ m) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset (normDist (L1.Space d)) P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 :=
  L1.uniform_stable_4_5 hn hm hmn P hε hε' hmsize

theorem negative_type_upper {X : Type*} (S : NegativeTypeMetric X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (P : Dataset X n)
    (μ : X) (hμ : S.toDist.IsGeometricMedian P μ)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) (hmsize : ⌈20 / (ε * ε)⌉₊ ≤ m) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset S.toDist P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 :=
  S.cor41_uniform_stable hn hm hmn P μ hμ hε hε' hmsize

theorem approximate_reference_upper {X : Type*} (S : SquaredMetric X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (P : Dataset X n) (μ : X)
    {ε δ : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) (hδ : 0 ≤ δ)
    (hδ' : δ < (5 - 19 * ε) / (9 + ε))
    (hμ : S.toDist.cost P μ ≤ (1 + δ) * S.toDist.optimum P)
    (hmsize : ⌈20 * (1 + δ) / (ε * ε)⌉₊ ≤ m) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset S.toDist P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 :=
  prop43_uniform_stable S hn hm hmn P μ hε hε' hδ hδ' hμ hmsize

theorem variance_identity_full {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n m : ℕ} (hn : 1 < n) (hm : 0 < m) (hmn : m ≤ n) (h : Fin n → H) :
    FinitePopulation.uniformAvg (m := m)
      (fun I => ‖FinitePopulation.sampleMean h I - FinitePopulation.popMean h‖ ^ 2) =
      ((n:ℝ) - m) / ((m:ℝ) * ((n:ℝ) - 1)) * ((1:ℝ) / n) *
        ∑ i, ‖h i - FinitePopulation.popMean h‖ ^ 2 :=
  FinitePopulation.variance_identity hn hm hmn h

theorem euclidean_comparison {d n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset (Euclidean.Space d) n) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => ∀ x y, |(normDist (Euclidean.Space d)).delta P (indexedSample P I) x y| ≤
        Real.sqrt (20 / m) * ((normDist (Euclidean.Space d)).cost P x +
          (normDist (Euclidean.Space d)).cost P y))).card / (n.choose m : ℝ) ≥ 9 / 10 :=
  Euclidean.prop24 hn hm hmn P

theorem appendix_comparison {d n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset (Euclidean.Space d) n) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => ∀ x y, |(normDist (Euclidean.Space d)).delta P (indexedSample P I) x y| ≤
        Real.sqrt (320 * Real.pi / m) * ((normDist (Euclidean.Space d)).cost P x +
          (normDist (Euclidean.Space d)).cost P y))).card / (n.choose m : ℝ) ≥ 9 / 10 :=
  Euclidean.propA1_comparison hn hm hmn P

theorem euclidean_lower {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/100) {m : ℕ} (hm : 0 < m)
    (hmsize : (m:ℝ) ≤ 1 / (24200 * ε ^ 2)) :
    ∃ (n : ℕ) (P : Dataset (Euclidean.Space 1) n), 0 < n ∧ m ≤ n ∧ Function.Injective P ∧
      ((((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun I => ¬ IsStableCoreset (normDist (Euclidean.Space 1)) P (indexedSample P I) ε (17 * ε))).card : ℝ) /
        (n.choose m : ℝ) ≥ 2/5 :=
  Euclidean.thm_1_2_ii hε hε' hm hmsize

theorem l1_lower {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/100) {m : ℕ} (hm : 0 < m)
    (hmsize : (m:ℝ) ≤ 1 / (24200 * ε ^ 2)) :
    ∃ (n : ℕ) (P : Dataset (L1.Space 1) n), 0 < n ∧ m ≤ n ∧ Function.Injective P ∧
      ((((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun I => ¬ IsStableCoreset (normDist (L1.Space 1)) P (indexedSample P I) ε (17 * ε))).card : ℝ) /
        (n.choose m : ℝ) ≥ 2/5 :=
  L1.lower_bound hε hε' hm hmsize

theorem euclidean_theta :
    Asymptotics.IsTheta (nhdsWithin (0:ℝ) (Set.Ioi 0)) (fun ε => (Euclidean.threshold ε : ℝ))
      (fun ε => 1 / ε ^ 2) :=
  Euclidean.sample_complexity_theta

theorem l1_theta :
    Asymptotics.IsTheta (nhdsWithin (0:ℝ) (Set.Ioi 0)) (fun ε => (L1.threshold ε : ℝ))
      (fun ε => 1 / ε ^ 2) :=
  L1.sample_complexity_theta

theorem appendix_stability {d n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset (Euclidean.Space d) n) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    (hmsize : ⌈320 * Real.pi / (ε * ε)⌉₊ ≤ m) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset (normDist (Euclidean.Space d)) P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4/5 :=
  Euclidean.propA1_stable hn hm hmn P hε hε' hmsize

theorem without_attainment {X : Type*} (S : SquaredMetric X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (P : Dataset X n)
    {ε δ : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) (hδ : 0 < δ) (hδ' : δ < 1/37)
    (hmsize : ⌈20 * (1 + δ) / (ε * ε)⌉₊ ≤ m) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset S.toDist P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4/5 :=
  uniform_stable_without_attainment S hn hm hmn P hε hε' hδ hδ' hmsize

theorem remark_half {m : ℕ} (hm : 2 ≤ m) :
    ((((Finset.univ : Finset (Fin (2*m))).powersetCard m).filter
      (fun I => (⟨0, by omega⟩ : Fin (2*m)) ∉ I)).card : ℝ) / ((2*m).choose m : ℝ) = 1/2 :=
  Remark25.miss_half hm

theorem remark_error {m : ℕ} (hm : 2 ≤ m) {R : ℝ} (hR : 0 < R)
    (I : Finset (Fin (2*m))) (hI : I.card = m)
    (hmiss : (⟨0, by omega⟩ : Fin (2*m)) ∉ I) {z : ℝ} (hz : R ≤ z) :
    |(normDist ℝ).delta (Remark25.population (by omega : 0 < 2*m) R)
      (indexedSample (Remark25.population (by omega : 0 < 2*m) R) I) z 0| = R / m :=
  Remark25.comparison_error hm hR I hI hmiss hz

end GeometricMedianCoresets.Challenge
