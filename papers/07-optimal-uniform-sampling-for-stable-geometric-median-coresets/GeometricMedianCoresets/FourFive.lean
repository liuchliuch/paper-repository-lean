import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import GeometricMedianCoresets.VarianceCount
import GeometricMedianCoresets.VarianceBound
import GeometricMedianCoresets.VarianceBoundary
import GeometricMedianCoresets.GoodEvent

/-!
# 9/10 and 4/5 finite good events
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace GeometricMedianCoresets

noncomputable def meanError {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (h : Fin n → H) (I : Finset (Fin n)) : ℝ :=
  ‖FinitePopulation.sampleMean h I - FinitePopulation.popMean h‖ ^ 2

theorem meanError_good_9_10 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (h : Fin n → H) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun I => meanError h I ≤ 10 * (((1:ℝ) / m) * ((1:ℝ) / n) * ∑ i, ‖h i‖ ^ 2))).card
      / (n.choose m : ℝ) ≥ 9 / 10 := by
  classical
  set Ω : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard m
  have hΩ : Ω.card = n.choose m := by
    exact VarianceCount.card_powersetCard n m
  have hΩnz : Ω.card ≠ 0 := by
    rw [hΩ]
    exact_mod_cast (Nat.choose_pos hmn).ne'
  have hf : ∀ I ∈ Ω, 0 ≤ meanError h I := by
    intro I _
    unfold meanError
    positivity
  have havg : (∑ I ∈ Ω, meanError h I) / Ω.card
      ≤ ((1:ℝ) / m) * ((1:ℝ) / n) * ∑ i, ‖h i‖ ^ 2 := by
    have h1 : (∑ I ∈ Ω, meanError h I) / Ω.card
        = FinitePopulation.uniformAvg (m := m) (meanError h) := by
      unfold FinitePopulation.uniformAvg
      rw [hΩ]
    rw [h1]
    exact FinitePopulation.variance_le_raw_sq hn hm hmn h
  have hB : 0 ≤ ((1:ℝ) / m) * ((1:ℝ) / n) * ∑ i, ‖h i‖ ^ 2 := by positivity
  have hgood := FinitePopulation.good_fraction_9_10 Ω (meanError h)
    (((1:ℝ) / m) * ((1:ℝ) / n) * ∑ i, ‖h i‖ ^ 2) hΩnz hf havg hB
  rw [hΩ] at hgood
  exact hgood

theorem card_intersect_ge {α : Type} (Ω : Finset α) (E F : α → Prop)
    [DecidablePred E] [DecidablePred F] :
    ((Ω.filter (fun I => E I ∧ F I)).card : ℝ)
      ≥ ((Ω.filter E).card : ℝ) + (Ω.filter F).card - Ω.card := by
  classical
  have hle : (Ω.filter (fun I => E I ∨ F I)).card ≤ Ω.card :=
    Finset.card_filter_le _ _
  have huf : Ω.filter E ∪ Ω.filter F = Ω.filter (fun I => E I ∨ F I) := by
    ext I
    simp [Finset.mem_union, Finset.mem_filter, and_or_left]
  have hif : Ω.filter E ∩ Ω.filter F = Ω.filter (fun I => E I ∧ F I) := by
    ext I
    simp [Finset.mem_inter, Finset.mem_filter, and_left_comm, and_assoc]
  have hci : (Ω.filter E ∩ Ω.filter F).card
      = (Ω.filter E).card + (Ω.filter F).card
        - (Ω.filter E ∪ Ω.filter F).card := Finset.card_inter _ _
  rw [hif, huf] at hci
  have hsub : (Ω.filter (fun I => E I ∨ F I)).card
      ≤ (Ω.filter E).card + (Ω.filter F).card :=
    Finset.card_union_le (Ω.filter E) (Ω.filter F) |> fun h => by
      rw [huf] at h
      exact h
  have hcast : (((Ω.filter E).card + (Ω.filter F).card
      - (Ω.filter (fun I => E I ∨ F I)).card : ℕ) : ℝ)
      = ((Ω.filter E).card : ℝ) + (Ω.filter F).card
        - ((Ω.filter (fun I => E I ∨ F I)).card : ℝ) := by
    rw [Nat.cast_sub hsub, Nat.cast_add]
  have hIEr : ((Ω.filter (fun I => E I ∧ F I)).card : ℝ)
      = (((Ω.filter E).card + (Ω.filter F).card
        - (Ω.filter (fun I => E I ∨ F I)).card : ℕ) : ℝ) := by
    exact_mod_cast hci
  rw [hIEr, hcast]
  have hler : ((Ω.filter (fun I => E I ∨ F I)).card : ℝ) ≤ Ω.card := by
    exact_mod_cast hle
  nlinarith

/-- Two 9/10-good events intersect on a 4/5-good event. -/
theorem two_good_4_5 {α : Type} (Ω : Finset α)
    (E F : α → Prop) [DecidablePred E] [DecidablePred F]
    (hE : ((Ω.filter E).card : ℝ) / Ω.card ≥ 9 / 10)
    (hF : ((Ω.filter F).card : ℝ) / Ω.card ≥ 9 / 10)
    (hΩ : Ω.card ≠ 0) :
    ((Ω.filter (fun I => E I ∧ F I)).card : ℝ) / Ω.card ≥ 4 / 5 := by
  classical
  have hge := card_intersect_ge Ω E F
  have hgood : ((Ω.filter (fun I => E I ∧ F I)).card : ℝ) / Ω.card
      ≥ ((Ω.filter E).card : ℝ) / Ω.card
        + ((Ω.filter F).card : ℝ) / Ω.card - 1 := by
    have h1 : ((Ω.filter E).card : ℝ) + (Ω.filter F).card - Ω.card
        ≤ (Ω.filter (fun I => E I ∧ F I)).card := hge
    have hC : (0:ℝ) < Ω.card := by exact_mod_cast (Nat.pos_of_ne_zero hΩ)
    have h2 : (((Ω.filter E).card : ℝ) + (Ω.filter F).card - Ω.card) / Ω.card
        = ((Ω.filter E).card : ℝ) / Ω.card
          + ((Ω.filter F).card : ℝ) / Ω.card - 1 := by
      field_simp
    have h3 : (((Ω.filter E).card : ℝ) + (Ω.filter F).card - Ω.card) / Ω.card
        ≤ ((Ω.filter (fun I => E I ∧ F I)).card : ℝ) / Ω.card := by
      exact div_le_div_of_nonneg_right h1 (le_of_lt hC)
    nlinarith [h2, h3]
  nlinarith [hE, hF, hgood]

end GeometricMedianCoresets
