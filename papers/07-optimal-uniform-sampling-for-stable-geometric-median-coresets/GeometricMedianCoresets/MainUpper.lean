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
import GeometricMedianCoresets.CostIdentity
import GeometricMedianCoresets.VarianceCount
import GeometricMedianCoresets.VarianceBound
import GeometricMedianCoresets.VarianceBoundary
import GeometricMedianCoresets.GoodEvent
import GeometricMedianCoresets.FourFive
import GeometricMedianCoresets.MainProbability

/-!
# Anchored 9/10 events at OPT and sample-cost 9/10

`meanError_good_9_10_opt`: for anchored features `h_i = Φ(P_i)-Φ(μ)`,
the mean-error good event at threshold `10·OPT/m` has probability ≥ 9/10.

`sampleCost_good_9_10`: the sample-cost good event `F_Q(μ) ≤ 10·OPT`
has probability ≥ 9/10.
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace GeometricMedianCoresets

/-- Mean-error good fraction ≥ 9/10 at threshold `10·OPT/m`, using anchored features. -/
theorem meanError_good_9_10_opt {X : Type*} (S : SquaredMetric X)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset X n) (μ : X) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun I => meanError (fun i => anchoredFeature S μ (P i)) I
            ≤ 10 * ((1:ℝ) / m) * S.toDist.cost P μ)).card
      / (n.choose m : ℝ) ≥ 9 / 10 := by
  classical
  have hsec := anchored_second_moment S hn P μ
  -- 10 * (1/m) * (1/n) * ∑ ‖h_i‖² = 10 * (1/m) * F_P(μ)
  have hrew : 10 * (((1:ℝ) / m) * ((1:ℝ) / n) * ∑ i, ‖anchoredFeature S μ (P i)‖ ^ 2)
      = 10 * ((1:ℝ) / m) * S.toDist.cost P μ := by
    have h2 : ((1:ℝ) / n) * ∑ i, ‖anchoredFeature S μ (P i)‖ ^ 2
        = S.toDist.cost P μ := hsec
    have h3 : 10 * (((1:ℝ) / m) * ((1:ℝ) / n) * ∑ i, ‖anchoredFeature S μ (P i)‖ ^ 2)
        = 10 * ((1:ℝ) / m) * (((1:ℝ) / n) * ∑ i, ‖anchoredFeature S μ (P i)‖ ^ 2) := by
      ring
    rw [h3, h2]
  have hgood := meanError_good_9_10 (n := n) (m := m) hn hm hmn
    (fun i => anchoredFeature S μ (P i))
  -- hgood has the raw-second-moment threshold; convert via hrew
  have hfilter : ((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => meanError (fun i => anchoredFeature S μ (P i)) I
          ≤ 10 * (((1:ℝ) / m) * ((1:ℝ) / n) * ∑ i, ‖anchoredFeature S μ (P i)‖ ^ 2))
      = ((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun I => meanError (fun i => anchoredFeature S μ (P i)) I
            ≤ 10 * ((1:ℝ) / m) * S.toDist.cost P μ) := by
    rw [hrew]
  rw [hfilter] at hgood
  exact hgood

/-- Sample cost at `μ` as a function of the index set: `(∑ d)/m` on `m`-subsets. -/
noncomputable def sampleCostM {X : Type*} (D : Dist X) {n : ℕ}
    (P : Dataset X n) (μ : X) (m : ℕ) (I : Finset (Fin n)) : ℝ :=
  (∑ i ∈ I, D.d (P i) μ) / m

/-- Sample-cost good fraction ≥ 9/10 at threshold `10·F_P(μ)`. -/
theorem sampleCost_good_9_10 {X : Type*} (D : Dist X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset X n) (μ : X) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun I => sampleCostM D P μ m I ≤ 10 * D.cost P μ)).card
      / (n.choose m : ℝ) ≥ 9 / 10 := by
  classical
  set Ω : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard m
  have hΩ : Ω.card = n.choose m := VarianceCount.card_powersetCard n m
  have hΩnz : Ω.card ≠ 0 := by
    rw [hΩ]
    exact_mod_cast (Nat.choose_pos hmn).ne'
  have hf : ∀ I ∈ Ω, 0 ≤ sampleCostM D P μ m I := by
    intro I _hI
    unfold sampleCostM
    exact div_nonneg (Finset.sum_nonneg fun i _ => D.nonneg (P i) μ)
      (le_of_lt (by exact_mod_cast hm : (0:ℝ) < m))
  have havg : (∑ I ∈ Ω, sampleCostM D P μ m I) / Ω.card ≤ D.cost P μ := by
    have h1 : (∑ I ∈ Ω, sampleCostM D P μ m I) / Ω.card
        = FinitePopulation.uniformAvg (m := m)
            (fun I => ((∑ i ∈ I, D.d (P i) μ) : ℝ) / m) := by
      unfold FinitePopulation.uniformAvg sampleCostM
      rw [hΩ]
    rw [h1]
    exact le_of_eq (mean_sampleCost_eq D hn hm hmn P μ)
  have hB : 0 ≤ D.cost P μ := D.cost_nonneg P μ
  have hgood := FinitePopulation.good_fraction_9_10 Ω (sampleCostM D P μ m)
    (D.cost P μ) hΩnz hf havg hB
  rw [hΩ] at hgood
  exact hgood

/-- Both good events hold with probability ≥ 4/5, in OPT-normalized form. -/
theorem two_good_4_5_opt {X : Type*} (S : SquaredMetric X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset X n) (μ : X) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun I => meanError (fun i => anchoredFeature S μ (P i)) I
            ≤ 10 * ((1:ℝ) / m) * S.toDist.cost P μ
          ∧ sampleCostM S.toDist P μ m I ≤ 10 * S.toDist.cost P μ)).card
      / (n.choose m : ℝ) ≥ 4 / 5 := by
  classical
  set Ω : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard m
  have hΩ : Ω.card = n.choose m := VarianceCount.card_powersetCard n m
  have hΩnz : Ω.card ≠ 0 := by
    rw [hΩ]
    exact_mod_cast (Nat.choose_pos hmn).ne'
  have hE := meanError_good_9_10_opt S hn hm hmn P μ
  have hF := sampleCost_good_9_10 S.toDist hn hm hmn P μ
  have hEΩ : ((Ω.filter (fun I => meanError (fun i => anchoredFeature S μ (P i)) I
      ≤ 10 * ((1:ℝ) / m) * S.toDist.cost P μ)).card : ℝ) / Ω.card ≥ 9 / 10 := by
    rw [hΩ]
    exact hE
  have hFΩ : ((Ω.filter (fun I => sampleCostM S.toDist P μ m I
      ≤ 10 * S.toDist.cost P μ)).card : ℝ) / Ω.card ≥ 9 / 10 := by
    rw [hΩ]
    exact hF
  have hgood := two_good_4_5 Ω
    (fun I => meanError (fun i => anchoredFeature S μ (P i)) I
        ≤ 10 * ((1:ℝ) / m) * S.toDist.cost P μ)
    (fun I => sampleCostM S.toDist P μ m I ≤ 10 * S.toDist.cost P μ)
    hEΩ hFΩ hΩnz
  rw [hΩ] at hgood
  exact hgood

end GeometricMedianCoresets
