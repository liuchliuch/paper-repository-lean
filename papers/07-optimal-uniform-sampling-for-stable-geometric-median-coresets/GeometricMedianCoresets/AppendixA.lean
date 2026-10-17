import GeometricMedianCoresets.EuclideanMetric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The conclusions of Proposition A.1 follow from the stronger constant in Proposition 2.4.
This proves the stated result without duplicating its alternative martingale proof. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace GeometricMedianCoresets.Euclidean

/-- Proposition A.1, equation (21), as a corollary of the sharper comparison theorem. -/
theorem propA1_comparison {d n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset (Space d) n) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => ∀ x y, |(normDist (Space d)).delta P (indexedSample P I) x y| ≤
        Real.sqrt (320 * Real.pi / m) *
          ((normDist (Space d)).cost P x + (normDist (Space d)).cost P y))).card
      / (n.choose m : ℝ) ≥ 9 / 10 := by
  apply (prop24 hn hm hmn P).trans
  apply sample_fraction_mono
  intro I _ h x y
  apply (h x y).trans
  apply mul_le_mul_of_nonneg_right _
    (add_nonneg ((normDist _).cost_nonneg P x) ((normDist _).cost_nonneg P y))
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  linarith [Real.two_le_pi]

/-- The stability consequence of Proposition A.1, with its stated sample threshold. -/
theorem propA1_stable {d n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset (Space d) n) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    (hmsize : ⌈320 * Real.pi / (ε * ε)⌉₊ ≤ m) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset (normDist (Space d)) P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 := by
  apply thm_1_2_i hn hm hmn P hε hε'
  apply Nat.ceil_le.2
  apply le_trans _ (Nat.ceil_le.1 hmsize)
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [Real.two_le_pi]

end GeometricMedianCoresets.Euclidean
