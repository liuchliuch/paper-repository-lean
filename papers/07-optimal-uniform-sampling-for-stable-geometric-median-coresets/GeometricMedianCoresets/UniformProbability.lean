import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import GeometricMedianCoresets.VarianceIdentity

/-!
# Finite uniform Markov and union bound
-/

noncomputable section

open scoped BigOperators

namespace GeometricMedianCoresets
namespace FinitePopulation

theorem markov_count {n m : ℕ} (a : ℝ) (_ha : 0 < a)
    (f : (Finset (Fin n)) → ℝ) (hf : ∀ I, 0 ≤ f I) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun I => a < f I)).card * a
      ≤ ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m, f I := by
  classical
  have hle : ∀ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      (if a < f I then (a:ℝ) else 0) ≤ f I := by
    intro I _
    by_cases hh : a < f I
    · simp [hh]
      exact le_of_lt hh
    · simp [hh]
      exact hf I
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_ite] at hsum
  simp at hsum
  have h2 : (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m with a < f I, a)
      = (((Finset.univ : Finset (Fin n)).powersetCard m).filter
          (fun I => a < f I)).card * a := by
    rw [Finset.sum_const, nsmul_eq_mul]
  linarith

theorem markov_avg {n m : ℕ} (a : ℝ) (ha : 0 < a)
    (f : (Finset (Fin n)) → ℝ) (hf : ∀ I, 0 ≤ f I) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun I => a < f I)).card / (n.choose m : ℝ)
      ≤ uniformAvg (m := m) f / a := by
  have hcount := markov_count (n := n) (m := m) a ha f hf
  have hdiv : (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => a < f I)).card
      ≤ (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m, f I) / a := by
    rw [le_div_iff₀ ha]
    exact hcount
  have hC : 0 ≤ (n.choose m : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hmul : (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => a < f I)).card * (n.choose m : ℝ)⁻¹
      ≤ (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m, f I) / a
        * (n.choose m : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right hdiv hC
  have h1 : (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => a < f I)).card / (n.choose m : ℝ)
      = (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun I => a < f I)).card * (n.choose m : ℝ)⁻¹ := by
    field_simp
  have h2 : (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m, f I) / a
      * (n.choose m : ℝ)⁻¹
      = (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m, f I)
          / (n.choose m : ℝ) / a := by
    field_simp
  have hgoal : (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => a < f I)).card / (n.choose m : ℝ)
      ≤ (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m, f I)
          / (n.choose m : ℝ) / a := by
    rw [h1]
    exact hmul.trans (le_of_eq h2)
  unfold uniformAvg
  exact hgoal

theorem card_union_le {n m : ℕ} (E F : (Finset (Fin n)) → Prop) [DecidablePred E]
    [DecidablePred F] :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun I => E I ∨ F I)).card
      ≤ (((Finset.univ : Finset (Fin n)).powersetCard m).filter E).card
        + (((Finset.univ : Finset (Fin n)).powersetCard m).filter F).card := by
  have h : ((Finset.univ : Finset (Fin n)).powersetCard m).filter (fun I => E I ∨ F I)
      ⊆ ((Finset.univ : Finset (Fin n)).powersetCard m).filter E
        ∪ ((Finset.univ : Finset (Fin n)).powersetCard m).filter F := by
    intro I hI
    simp only [Finset.mem_filter, Finset.mem_union] at hI ⊢
    rcases hI.2 with h | h
    · exact Or.inl ⟨hI.1, h⟩
    · exact Or.inr ⟨hI.1, h⟩
  exact le_trans (Finset.card_le_card h) (Finset.card_union_le _ _)

end FinitePopulation
end GeometricMedianCoresets
