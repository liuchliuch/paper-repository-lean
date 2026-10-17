import GeometricMedianCoresets.EuclideanMetric
noncomputable section
attribute [local instance] Classical.propDecidable
namespace GeometricMedianCoresets.Challenge

/-- Negative fixture: an extra `False` premise must be rejected as a statement mismatch. -/
theorem euclidean_upper {d n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset (Euclidean.Space d) n) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    (hmsize : ⌈20 / (ε * ε)⌉₊ ≤ m) : False →
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset (normDist (Euclidean.Space d)) P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4/5 :=
  fun _ => Euclidean.thm_1_2_i hn hm hmn P hε hε' hmsize
end GeometricMedianCoresets.Challenge
