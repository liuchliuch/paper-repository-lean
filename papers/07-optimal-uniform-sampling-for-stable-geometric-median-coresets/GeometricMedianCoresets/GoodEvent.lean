import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Finite good-event lemma (9/10 from Markov)

If `f ≥ 0` on a finite set `Ω` and the average of `f` is at most `B`, then
the fraction of `I ∈ Ω` with `f I ≤ 10 B` is at least `9/10`.
When `B = 0` the good event is all of `Ω`.
-/

noncomputable section

open scoped BigOperators

namespace GeometricMedianCoresets
namespace FinitePopulation

theorem sum_nonneg' {α : Type} (Ω : Finset α) (f : α → ℝ)
    (hf : ∀ I, I ∈ Ω → 0 ≤ f I) : 0 ≤ ∑ x ∈ Ω, f x := by
  apply Finset.sum_induction
  · intro a b ha hb
    exact add_nonneg ha hb
  · exact le_refl 0
  · intro x hx
    exact hf x hx

theorem sum_zero_nonneg {α : Type} [DecidableEq α] (Ω : Finset α) (f : α → ℝ)
    (hf : ∀ I, I ∈ Ω → 0 ≤ f I)
    (hsum : (∑ x ∈ Ω, f x) = 0) :
    ∀ I, I ∈ Ω → f I = 0 := by
  intro I hI
  have hsplit : (∑ x ∈ Ω, f x) = f I + ∑ x ∈ Ω.erase I, f x := by
    conv_lhs => rw [← Finset.insert_erase hI]
    rw [Finset.sum_insert (Finset.notMem_erase I Ω)]
  have hnn : 0 ≤ ∑ x ∈ Ω.erase I, f x :=
    sum_nonneg' _ _ fun x hx => hf x (Finset.mem_of_mem_erase hx)
  have hInn : 0 ≤ f I := hf I hI
  linarith

theorem card_split {α : Type} (Ω : Finset α) (f : α → ℝ) (a : ℝ) :
    (Ω.filter (fun I => f I ≤ a)).card + (Ω.filter (fun I => a < f I)).card
      = Ω.card := by
  classical
  have hdisj : Disjoint (Ω.filter (fun I => f I ≤ a)) (Ω.filter (fun I => a < f I)) := by
    rw [Finset.disjoint_left]
    intro I h1 h2
    exact absurd (Finset.mem_filter.1 h1).2 (not_le.mpr (Finset.mem_filter.1 h2).2)
  have hunion : Ω.filter (fun I => f I ≤ a) ∪ Ω.filter (fun I => a < f I) = Ω := by
    ext I
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      rcases h with h | h
      · exact h.1
      · exact h.1
    · intro hI
      by_cases hh : f I ≤ a
      · exact Or.inl ⟨hI, hh⟩
      · exact Or.inr ⟨hI, by linarith⟩
  have hcard : (Ω.filter (fun I => f I ≤ a) ∪ Ω.filter (fun I => a < f I)).card
      = (Ω.filter (fun I => f I ≤ a)).card + (Ω.filter (fun I => a < f I)).card :=
    Finset.card_union_of_disjoint hdisj
  rw [← hcard, hunion]

/-- Markov count: `#{a < f} · a ≤ ∑ f` for nonnegative `f`. -/
theorem markov_count_gen {α : Type} (Ω : Finset α) (a : ℝ) (ha : 0 < a)
    (f : α → ℝ) (hf : ∀ I, I ∈ Ω → 0 ≤ f I) :
    (Ω.filter (fun I => a < f I)).card * a ≤ ∑ I ∈ Ω, f I := by
  classical
  have hle : ∀ I ∈ Ω, (if a < f I then (a:ℝ) else 0) ≤ f I := by
    intro I hI
    by_cases hh : a < f I
    · simp [hh]
      exact le_of_lt hh
    · simp [hh]
      exact hf I hI
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_ite] at hsum
  simp at hsum
  have h2 : (∑ I ∈ Ω with a < f I, a)
      = (Ω.filter (fun I => a < f I)).card * a := by
    rw [Finset.sum_const, nsmul_eq_mul]
  linarith

/-- Combined 9/10 good fraction, with the `B = 0` branch included. -/
theorem good_fraction_9_10 {α : Type} [DecidableEq α] (Ω : Finset α)
    (f : α → ℝ) (B : ℝ) (hΩ : Ω.card ≠ 0)
    (hf : ∀ I ∈ Ω, 0 ≤ f I)
    (havg : (∑ I ∈ Ω, f I) / Ω.card ≤ B)
    (hB : 0 ≤ B) :
    ((Ω.filter (fun I => f I ≤ 10 * B)).card : ℝ) / Ω.card ≥ 9 / 10 := by
  by_cases hB0 : B = 0
  · subst hB0
    have hsum : (∑ I ∈ Ω, f I) = 0 := by
      have hnn := sum_nonneg' Ω f (fun I hI => hf I hI)
      have hdiv : ∑ I ∈ Ω, f I ≤ 0 := by
        have hpos : (0:ℝ) < Ω.card := by
          exact_mod_cast (Nat.pos_of_ne_zero hΩ)
        have : (∑ I ∈ Ω, f I) ≤ 0 * (Ω.card : ℝ) := (div_le_iff₀ hpos).mp havg
        nlinarith
      linarith
    have hall : ∀ I ∈ Ω, f I = 0 := sum_zero_nonneg Ω f hf hsum
    have hfilter : Ω.filter (fun I => f I ≤ 10 * (0:ℝ)) = Ω := by
      ext I
      simp only [Finset.mem_filter]
      constructor
      · intro h
        exact h.1
      · intro hI
        refine ⟨hI, ?_⟩
        rw [hall I hI]
        norm_num
    rw [hfilter]
    have : (Ω.card : ℝ) / Ω.card = 1 := by
      field_simp
    rw [this]
    norm_num
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have hcard : (Ω.card : ℝ) ≠ 0 := by exact_mod_cast hΩ
    have hmarkov := markov_count_gen Ω (10 * B) (by positivity) f hf
    have hdiv : (Ω.filter (fun I => 10 * B < f I)).card
        ≤ (∑ I ∈ Ω, f I) / (10 * B) := by
      rw [le_div_iff₀ (by positivity)]
      exact hmarkov
    have hbad : ((Ω.filter (fun I => 10 * B < f I)).card : ℝ) / Ω.card ≤ 1 / 10 := by
      have h1 : (∑ I ∈ Ω, f I) / (Ω.card : ℝ) / (10 * B) ≤ B / (10 * B) := by
        exact div_le_div_of_nonneg_right havg (by positivity)
      have h2 : B / (10 * B) = (1:ℝ) / 10 := by
        have hne : B ≠ 0 := ne_of_gt hBpos
        field_simp
      have h3 : ((Ω.filter (fun I => 10 * B < f I)).card : ℝ) / Ω.card
          ≤ (∑ I ∈ Ω, f I) / (Ω.card : ℝ) / (10 * B) := by
        have hC : 0 ≤ (Ω.card : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
        have hmul := mul_le_mul_of_nonneg_right hdiv hC
        have h4 : (Ω.filter (fun I => 10 * B < f I)).card / (Ω.card : ℝ)
            = (Ω.filter (fun I => 10 * B < f I)).card * (Ω.card : ℝ)⁻¹ := by
          field_simp
        have h5 : (∑ I ∈ Ω, f I) / (10 * B) * (Ω.card : ℝ)⁻¹
            = (∑ I ∈ Ω, f I) / (Ω.card : ℝ) / (10 * B) := by
          field_simp
        rw [h4, ← h5]
        exact hmul
      linarith
    have hsplit := card_split Ω f (10 * B)
    have hgood : ((Ω.filter (fun I => f I ≤ 10 * B)).card : ℝ) / Ω.card
        = 1 - ((Ω.filter (fun I => 10 * B < f I)).card : ℝ) / Ω.card := by
      have hcast := congrArg (fun (x : ℕ) => (x : ℝ) / Ω.card) hsplit
      simp only [Nat.cast_add] at hcast
      have h3 : ((Ω.filter (fun I => f I ≤ 10 * B)).card
            + (Ω.filter (fun I => 10 * B < f I)).card : ℝ)
          / Ω.card = 1 := by
        have : ((Ω.filter (fun I => f I ≤ 10 * B)).card
            + (Ω.filter (fun I => 10 * B < f I)).card : ℝ) = Ω.card := by
          exact_mod_cast hsplit
        rw [this]
        field_simp
      field_simp at h3 ⊢
      nlinarith
    rw [hgood]
    nlinarith

end FinitePopulation
end GeometricMedianCoresets
