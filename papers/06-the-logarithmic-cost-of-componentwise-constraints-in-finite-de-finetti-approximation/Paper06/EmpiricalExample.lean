/-
The empirical-repair example in Section 2: a sample of distinct symbols
has empirical relative entropy log(d/n) from the uniform alphabet law.
-/
import Paper06.Sampling

open Real BigOperators
open scoped Classical

namespace Paper06.EmpiricalExample

/-- The actual uniform probability law on a nonempty finite alphabet. -/
noncomputable def uniformLaw (α : Type*) [Fintype α] (hα : 0 < Fintype.card α) :
    FinProb α where
  w _ := 1 / (Fintype.card α : ℝ)
  nonneg _ := by positivity
  sum_eq_one := by
    have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hα)
    simp [Finset.sum_const, nsmul_eq_mul, hc]

@[simp] theorem uniformLaw_w {α : Type*} [Fintype α]
    (hα : 0 < Fintype.card α) (a : α) :
    (uniformLaw α hα).w a = 1 / (Fintype.card α : ℝ) := rfl

/-- A nonempty sample certifies nonemptiness of the alphabet. -/
theorem sample_card_pos {α : Type*} [Fintype α] (n : ℕ) (hn : 0 < n)
    (sample : Fin n → α) : 0 < Fintype.card α :=
  Fintype.card_pos_iff.mpr ⟨sample ⟨0,hn⟩⟩

/-- Empirical law: choose a sample index uniformly and return its observed symbol. -/
noncomputable def empiricalLaw {α : Type*} [Fintype α]
    (n : ℕ) (hn : 0 < n) (sample : Fin n → α) : FinProb α :=
  FinProb.map (uniformLaw (Fin n) (by simpa using hn)) sample

/-- Distinct observed symbols each receive mass exactly `1/n`. -/
theorem empiricalLaw_w_sample {α : Type*} [Fintype α]
    (n : ℕ) (hn : 0 < n) (sample : Fin n → α) (hs : Function.Injective sample)
    (i : Fin n) : (empiricalLaw n hn sample).w (sample i) = 1 / (n : ℝ) := by
  simp only [empiricalLaw, FinProb.map_w, hs.eq_iff]
  simp

/-- Symbols absent from the sample have zero empirical mass. -/
theorem empiricalLaw_w_outside {α : Type*} [Fintype α]
    (n : ℕ) (hn : 0 < n) (sample : Fin n → α) (a : α)
    (ha : a ∉ Set.range sample) : (empiricalLaw n hn sample).w a = 0 := by
  have he : ∀ i, sample i ≠ a := fun i h => ha ⟨i,h⟩
  simp only [empiricalLaw, FinProb.map_w, he, if_false, Finset.sum_const_zero]

/-- The empirical weights are derived from the injective sample pushforward. -/
theorem empiricalLaw_w {α : Type*} [Fintype α]
    (n : ℕ) (hn : 0 < n) (sample : Fin n → α) (hs : Function.Injective sample) (a : α) :
    (empiricalLaw n hn sample).w a = if a ∈ Set.range sample then 1 / (n : ℝ) else 0 := by
  by_cases ha : a ∈ Set.range sample
  · rw [if_pos ha]
    obtain ⟨i,rfl⟩ := ha
    exact empiricalLaw_w_sample n hn sample hs i
  · rw [if_neg ha]
    exact empiricalLaw_w_outside n hn sample a ha

/-- An injective sample automatically satisfies the example's `d ≥ n` hypothesis. -/
theorem sample_size_le_card {α : Type*} [Fintype α]
    (n : ℕ) (sample : Fin n → α) (hs : Function.Injective sample) :
    n ≤ Fintype.card α := by
  simpa using Fintype.card_le_of_injective sample hs

/-- The uniform reference law has full support, so this KL value is always finite. -/
theorem empiricalLaw_supports_uniform {α : Type*} [Fintype α]
    (n : ℕ) (hn : 0 < n) (sample : Fin n → α) :
    FinProb.Supports (empiricalLaw n hn sample)
      (uniformLaw α (sample_card_pos n hn sample)) := by
  intro a ha
  have hc : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast (sample_card_pos n hn sample)
  have hu : 0 < (uniformLaw α (sample_card_pos n hn sample)).w a := by
    rw [uniformLaw_w]
    positivity
  exact False.elim ((ne_of_gt hu) ha)

/-- The numerical repair cost is computed by summing the actual empirical law. -/
theorem empirical_repair_klPos {α : Type*} [Fintype α]
    (n : ℕ) (hn : 0 < n) (sample : Fin n → α) (hs : Function.Injective sample) :
    FinProb.klPos (empiricalLaw n hn sample)
      (uniformLaw α (sample_card_pos n hn sample)) =
        Real.log ((Fintype.card α : ℝ) / n) := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hdr : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sample_card_pos n hn sample))
  have hratio : (1 / (n : ℝ)) / (1 / (Fintype.card α : ℝ)) =
      (Fintype.card α : ℝ) / n := by field_simp
  have hpoint (a : α) :
      (empiricalLaw n hn sample).w a *
          Real.log ((empiricalLaw n hn sample).w a /
            (uniformLaw α (sample_card_pos n hn sample)).w a) =
        (empiricalLaw n hn sample).w a * Real.log ((Fintype.card α : ℝ) / n) := by
    by_cases ha : a ∈ Set.range sample
    · rw [empiricalLaw_w n hn sample hs a, if_pos ha, uniformLaw_w, hratio]
    · rw [empiricalLaw_w_outside n hn sample a ha, zero_mul, zero_mul]
  unfold FinProb.klPos
  rw [Finset.sum_congr rfl (fun a _ => hpoint a), ← Finset.sum_mul,
    (empiricalLaw n hn sample).sum_eq_one, one_mul]

/-- **Section 2 empirical-repair example**, in support-safe extended relative entropy. -/
theorem empirical_repair_kl {α : Type*} [Fintype α]
    (n : ℕ) (hn : 0 < n) (sample : Fin n → α) (hs : Function.Injective sample) :
    FinProb.kl (empiricalLaw n hn sample)
      (uniformLaw α (sample_card_pos n hn sample)) =
        (Real.log ((Fintype.card α : ℝ) / n) : EReal) := by
  rw [FinProb.kl_of_support (empiricalLaw_supports_uniform n hn sample),
    empirical_repair_klPos n hn sample hs]

/-- Any empirical law on fewer than `r` observations misses a symbol of an `r`-symbol alphabet. -/
theorem empiricalLaw_ne_uniform_of_size_lt {α : Type*} [Fintype α]
    (n : ℕ) (hn : 0 < n) (sample : Fin n → α) (hsize : n < Fintype.card α) :
    empiricalLaw n hn sample ≠ uniformLaw α (sample_card_pos n hn sample) := by
  have hns : ¬ Function.Surjective sample := by
    intro hsurj
    have hc := Fintype.card_le_of_surjective sample hsurj
    simp only [Fintype.card_fin] at hc
    omega
  change ¬ ∀ a : α, ∃ i : Fin n, sample i = a at hns
  push_neg at hns
  obtain ⟨a,ha⟩ := hns
  have hout : a ∉ Set.range sample := by
    rintro ⟨i,hi⟩
    exact ha i hi
  intro heq
  have hw := congrArg (fun p : FinProb α => p.w a) heq
  dsimp only at hw
  rw [empiricalLaw_w_outside n hn sample a hout, uniformLaw_w] at hw
  have hc : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast (sample_card_pos n hn sample)
  have hu : (0 : ℝ) < 1 / (Fintype.card α : ℝ) := by positivity
  linarith

end Paper06.EmpiricalExample
