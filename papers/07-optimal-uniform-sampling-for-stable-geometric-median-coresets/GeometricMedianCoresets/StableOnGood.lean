import GeometricMedianCoresets.IndexedSample
import GeometricMedianCoresets.GeometricInequalities
import GeometricMedianCoresets.Stability
import Mathlib.Algebra.Order.Floor.Semiring

/-! All-pairs relative comparison and stability for actual uniform subdatasets. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators RealInnerProductSpace
namespace GeometricMedianCoresets

/-- `√(20/m) ≤ ε` at the sample threshold of Theorem 1.2. -/
theorem sqrt_20_div_le_eps {m ε : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (h : 20 / (ε * ε) ≤ m) :
    Real.sqrt (20 / m) ≤ ε := by
  apply (Real.sqrt_le_iff).2
  refine ⟨hε.le, ?_⟩
  have hh := (div_le_iff₀ (mul_pos hε hε)).1 h
  exact (div_le_iff₀ hm).2 (by nlinarith [hh])

/-- Cauchy--Schwarz applies simultaneously to every pair on one mean-error event. -/
theorem delta_le_meanError {X : Type*} (S : SquaredMetric X) {n : ℕ}
    (hn : 0 < n) (P : Dataset X n) (I : Finset (Fin n)) (hI : 0 < I.card)
    (μ x y : X) :
    |S.toDist.delta P (indexedSample P I) x y| ≤
      2 * Real.sqrt (S.d x y * meanError (fun i => anchoredFeature S μ (P i)) I) := by
  rw [delta_indexedSample S hn P I hI μ x y, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hcs := abs_real_inner_le_norm (S.Φ x - S.Φ y)
    (FinitePopulation.sampleMean (fun i => anchoredFeature S μ (P i)) I -
      FinitePopulation.popMean (fun i => anchoredFeature S μ (P i)))
  have hsqrt : Real.sqrt (S.d x y * meanError (fun i => anchoredFeature S μ (P i)) I) =
      ‖S.Φ x - S.Φ y‖ *
        ‖FinitePopulation.sampleMean (fun i => anchoredFeature S μ (P i)) I -
          FinitePopulation.popMean (fun i => anchoredFeature S μ (P i))‖ := by
    rw [← S.dist_sq, meanError, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [hsqrt]
  exact mul_le_mul_of_nonneg_left hcs (by norm_num)

/-- Proposition 2.4 on each actual sample satisfying the empirical-mean event. -/
theorem comparison_on_good_event {X : Type*} (S : SquaredMetric X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (P : Dataset X n) (I : Finset (Fin n))
    (hI : I.card = m) (μ : X) (hμ : S.toDist.IsGeometricMedian P μ)
    (hmean : meanError (fun i => anchoredFeature S μ (P i)) I
      ≤ 10 * ((1:ℝ) / m) * S.toDist.cost P μ) :
    ∀ x y, |S.toDist.delta P (indexedSample P I) x y| ≤
      Real.sqrt (20 / m) * (S.toDist.cost P x + S.toDist.cost P y) := by
  intro x y
  have hIp : 0 < I.card := by omega
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hmean' : meanError (fun i => anchoredFeature S μ (P i)) I
      ≤ 10 * S.toDist.cost P μ / m := by convert hmean using 1 <;> ring
  exact (delta_le_meanError S hn P I hIp μ x y).trans
    (prop24_deterministic hmr (S.toDist.cost_nonneg P μ) hmean' (sq_nonneg _)
      (triangle_avg S.toDist hn P x y) (by linarith [hμ x, hμ y])
      (add_nonneg (S.toDist.cost_nonneg P x) (S.toDist.cost_nonneg P y)) (S.d_nonneg x y))

/-- Genuine proper-sample form of stability on the two good events. -/
theorem stable_on_good_event {X : Type*} (S : SquaredMetric X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (P : Dataset X n) (I : Finset (Fin n))
    (hI : I.card = m) (μ : X) (hμ : S.toDist.IsGeometricMedian P μ)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) (hmsize : 20 / (ε * ε) ≤ m)
    (hmean : meanError (fun i => anchoredFeature S μ (P i)) I
      ≤ 10 * ((1:ℝ) / m) * S.toDist.cost P μ)
    (hcost : sampleCostM S.toDist P μ m I ≤ 10 * S.toDist.cost P μ) :
    IsStableCoreset S.toDist P (indexedSample P I) ε (17 * ε) := by
  apply lemma_2_6_stable S.toDist P (indexedSample P I) hε hε' hμ
  · intro x y
    exact (comparison_on_good_event S hn hm P I hI μ hμ hmean x y).trans
      (mul_le_mul_of_nonneg_right
        (sqrt_20_div_le_eps (by exact_mod_cast hm) hε hmsize)
        (add_nonneg (S.toDist.cost_nonneg P x) (S.toDist.cost_nonneg P y)))
  · rw [cost_indexedSample S.toDist P I hI]
    exact hcost

/-- Theorem 1.2(i) for squared-Hilbert metrics with an attained median;
no probability or comparison conclusion occurs among its hypotheses. -/
theorem uniform_stable_4_5 {X : Type*} (S : SquaredMetric X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (P : Dataset X n)
    (μ : X) (hμ : S.toDist.IsGeometricMedian P μ)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) (hmsize : 20 / (ε * ε) ≤ m) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset S.toDist P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 := by
  classical
  apply (two_good_4_5_opt S hn hm hmn P μ).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show
    ((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => meanError (fun i => anchoredFeature S μ (P i)) I
        ≤ 10 * ((1:ℝ) / m) * S.toDist.cost P μ ∧
        sampleCostM S.toDist P μ m I ≤ 10 * S.toDist.cost P μ) ⊆
    ((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset S.toDist P (indexedSample P I) ε (17 * ε)) from by
    intro I hi
    obtain ⟨hmem, hmean, hcost⟩ := Finset.mem_filter.1 hi
    exact Finset.mem_filter.2 ⟨hmem, stable_on_good_event S hn hm P I
      (Finset.mem_powersetCard.1 hmem).2 μ hμ hε hε' hmsize hmean hcost⟩)

/-- Nat-ceiling interface matching the paper's stated threshold. -/
theorem uniform_stable_4_5_ceil {X : Type*} (S : SquaredMetric X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (P : Dataset X n)
    (μ : X) (hμ : S.toDist.IsGeometricMedian P μ)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    (hmsize : ⌈20 / (ε * ε)⌉₊ ≤ m) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset S.toDist P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 :=
  uniform_stable_4_5 S hn hm hmn P μ hμ hε hε' (Nat.ceil_le.1 hmsize)

/-- The whole dataset is always stable at the required loss. -/
theorem thm_1_2_i_full {X : Type*} (S : SquaredMetric X) {n : ℕ}
    (P : Dataset X n) {ε : ℝ} (hε : 0 < ε) :
    IsStableCoreset S.toDist P P ε (17 * ε) :=
  stable_of_full_of_le S.toDist P (by linarith)

end GeometricMedianCoresets
