import GeometricMedianCoresets.RealFeatureMap
import GeometricMedianCoresets.NormedMedian
import GeometricMedianCoresets.UniformComparison
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual squared-Hilbert representation and the upper bound in Corollary 4.2. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace GeometricMedianCoresets.L1

abbrev Space (d : ℕ) := PiLp 1 (fun _ : Fin d => ℝ)
abbrev FeatureSpace (d : ℕ) := PiLp 2 (fun _ : Fin d =>
  MeasureTheory.Lp ℝ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))

def feature {d : ℕ} (x : Space d) : FeatureSpace d :=
  WithLp.toLp 2 (fun j => RealFeature.ψ (x j))

/-- The coordinatewise indicator representation of the ℓ₁ metric. -/
theorem feature_dist_sq {d : ℕ} (x y : Space d) :
    ‖feature x - feature y‖ ^ 2 = ‖x - y‖ := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_eq_of_L1]
  apply Finset.sum_congr rfl
  intro j _
  change ‖RealFeature.ψ (x j) - RealFeature.ψ (y j)‖ ^ 2 = ‖x j - y j‖
  rw [RealFeature.norm_sub_sq, Real.norm_eq_abs]

def squaredMetric (d : ℕ) : SquaredMetric (Space d) where
  H := FeatureSpace d
  d x y := ‖x - y‖
  Φ := feature
  dist_sq := feature_dist_sq
  triangle x y z := by
    simpa only [sub_add_sub_cancel] using norm_add_le (x - z) (z - y)

/-- The upper-bound assertion in Corollary 4.2 with its exact constant and probability. -/
theorem uniform_stable_4_5 {d n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset (Space d) n) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    (hmsize : ⌈20 / (ε * ε)⌉₊ ≤ m) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset (normDist (Space d)) P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 := by
  obtain ⟨μ, hμ⟩ := exists_normed_geometricMedian hn P
  exact uniform_stable_4_5_ceil (squaredMetric d) hn hm hmn P μ hμ hε hε' hmsize

/-- Small datasets use all their points. -/
theorem uniform_stable_min {d n : ℕ} (hn : 0 < n) (P : Dataset (Space d) n)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) :
    let m := min n ⌈20 / (ε * ε)⌉₊
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset (normDist (Space d)) P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 := by
  obtain ⟨μ, hμ⟩ := exists_normed_geometricMedian hn P
  exact GeometricMedianCoresets.uniform_stable_min (squaredMetric d) hn P μ hμ hε hε'

end GeometricMedianCoresets.L1
