import Paper06.IncidenceFull
import Paper06.Divergence
import Paper06.Mixtures
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Finset.Powerset

open Real Set BigOperators
open scoped Classical

namespace Paper06

/-- Independent, possibly different, one-coordinate laws. -/
noncomputable def independentFinProb {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (q : I → FinProb A) : FinProb (I → A) where
  w := channelLambda q
  nonneg := channelLambda_nonneg q
  sum_eq_one := channelLambda_sum q

/-- The factorisation identity for independent coordinates. -/
theorem channelLambda_product_expect {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (q : I → FinProb A) (h : I → A → ℝ) :
    ∑ z : I → A, channelLambda q z * (∏ i, h i (z i)) =
      ∏ i, ∑ a, (q i).w a * h i a := by
  classical
  simp only [channelLambda, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : I) (a : A) => (q i).w a * h i a)).symm

/-- Independence of two distinct coordinates, proved from the complete product mass. -/
theorem channelLambda_joint {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (q : I → FinProb A) {i j : I} (hij : i ≠ j) (a b : A) :
    (∑ z : I → A, channelLambda q z *
      ((if z i = a then 1 else 0) * (if z j = b then 1 else 0))) =
      (q i).w a * (q j).w b := by
  classical
  have hp (z : I → A) :
      ((if z i = a then (1 : ℝ) else 0) * (if z j = b then 1 else 0)) =
      ∏ l : I, ((if l = i then (if z l = a then 1 else 0) else 1) *
        (if l = j then (if z l = b then 1 else 0) else 1)) := by
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
  simp_rw [hp]
  rw [channelLambda_product_expect q (fun (l : I) (c : A) =>
    ((if l = i then (if c = a then 1 else 0) else 1) *
     (if l = j then (if c = b then 1 else 0) else 1)))]
  have hrow (l : I) :
      (∑ c : A, (q l).w c *
        ((if l = i then (if c = a then 1 else 0) else 1) *
         (if l = j then (if c = b then 1 else 0) else 1))) =
      (if l = i then (q i).w a else 1) * (if l = j then (q j).w b else 1) := by
    by_cases hli : l = i
    · subst l
      simp [hij]
    · by_cases hlj : l = j
      · subst l
        simp [Ne.symm hij]
      · simp [hli, hlj, (q l).sum_eq_one]
  simp_rw [hrow]
  rw [Finset.prod_mul_distrib]
  simp

/-- Any statistic of two distinct independent coordinates has the product-law expectation. -/
theorem channelLambda_pair_expect {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (q : I → FinProb A) {i j : I} (hij : i ≠ j) (h : A → A → ℝ) :
    ∑ z : I → A, channelLambda q z * h (z i) (z j) =
      ∑ a : A, ∑ b : A, (q i).w a * (q j).w b * h a b := by
  classical
  calc
    _ = ∑ z : I → A, ∑ a : A, ∑ b : A,
        channelLambda q z * ((if z i = a then 1 else 0) *
          (if z j = b then 1 else 0)) * h a b := by
      apply Finset.sum_congr rfl
      intro z hz
      simp
    _ = ∑ a : A, ∑ b : A, ∑ z : I → A,
        channelLambda q z * ((if z i = a then 1 else 0) *
          (if z j = b then 1 else 0)) * h a b := by
      simpa only [Fintype.sum_prod_type] using
        (Finset.sum_comm (s := (Finset.univ : Finset (I → A)))
          (t := (Finset.univ : Finset (A × A)))
          (f := fun z p => channelLambda q z * ((if z i = p.1 then 1 else 0) *
            (if z j = p.2 then 1 else 0)) * h p.1 p.2))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [← Finset.sum_mul, channelLambda_joint q hij]

/-- The CHSH winning relation on two coordinates. -/
def pairWin {F : Type*} [Field F] {k : ℕ} (z : Fin k → F × F) (i j : Fin k) : Prop :=
  (z i).2 + (z j).2 = (z i).1 * (z j).1

/-- The event that at least one unordered pair wins. -/
noncomputable def somePairWins {F : Type*} [Field F] {k : ℕ}
    (z : Fin k → F × F) : Bool := decide (∃ i j : Fin k, i < j ∧ pairWin z i j)

/-- Distinct coordinates of the full independent experiment have exactly their product win law. -/
theorem independent_pairWin {F : Type*} [Fintype F] [Field F] {k : ℕ}
    (q : Fin k → FinProb (F × F)) {i j : Fin k} (hij : i ≠ j) :
    (∑ z : Fin k → F × F, if pairWin z i j then (independentFinProb q).w z else 0) =
      productWin (q i) (q j) := by
  classical
  have h := channelLambda_pair_expect q hij
    (fun a b => if a.2 + b.2 = a.1 * b.1 then (1 : ℝ) else 0)
  simpa only [pairWin, independentFinProb, mul_ite, mul_one, mul_zero,
    productWin, prod_w, Fintype.sum_prod_type] using h

/-- Ordered representatives `i<j` of unordered pairs. -/
noncomputable def ascendingPairs (k : ℕ) : Finset (Fin k × Fin k) :=
  Finset.univ.filter fun p => p.1 < p.2

/-- There are at most `choose k 2` increasing pairs, by injection into two-element subsets. -/
theorem ascendingPairs_card_le (k : ℕ) : (ascendingPairs k).card ≤ k.choose 2 := by
  classical
  have h : (ascendingPairs k).card ≤ ((Finset.univ : Finset (Fin k)).powersetCard 2).card := by
    apply Finset.card_le_card_of_injOn (fun p : Fin k × Fin k => {p.1, p.2})
    · intro p hp
      have hlt := (Finset.mem_filter.mp hp).2
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hlt.ne⟩
    · intro p hp p' hp' he
      dsimp only at he
      have hlt := (Finset.mem_filter.mp hp).2
      have hlt' := (Finset.mem_filter.mp hp').2
      have h1 : p.1 = p'.1 ∨ p.1 = p'.2 := by
        have hm : p.1 ∈ ({p'.1, p'.2} : Finset (Fin k)) := by rw [← he]; simp
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
      have h2 : p.2 = p'.1 ∨ p.2 = p'.2 := by
        have hm : p.2 ∈ ({p'.1, p'.2} : Finset (Fin k)) := by rw [← he]; simp
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact (hlt.ne (h1.trans h2.symm)).elim
      · exact Prod.ext h1 h2
      · exfalso
        rw [h1, h2] at hlt
        exact (lt_asymm hlt hlt').elim
      · exact (hlt.ne (h1.trans h2.symm)).elim
  simpa using h

/-- Union bound for arbitrary independent feasible factors, without identical-distribution assumptions. -/
theorem independent_somePairWins_le {F : Type*} [Fintype F] [Field F] {k : ℕ}
    (q : Fin k → FinProb (F × F)) (hq : ∀ i, UniformInput (q i)) :
    (FinProb.map (independentFinProb q) somePairWins).w true ≤ (k.choose 2 : ℝ) * omegaR F := by
  classical
  have hp (z : Fin k → F × F) :
      (if somePairWins z = true then (independentFinProb q).w z else 0) ≤
        ∑ p ∈ ascendingPairs k, if pairWin z p.1 p.2 then (independentFinProb q).w z else 0 := by
    by_cases hz : ∃ i j : Fin k, i < j ∧ pairWin z i j
    · obtain ⟨i, j, hij, hwin⟩ := hz
      simp only [somePairWins, decide_eq_true_eq] at *
      rw [if_pos ⟨i, j, hij, hwin⟩]
      have hmem : (i, j) ∈ ascendingPairs k := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
      have hs := Finset.single_le_sum (s := ascendingPairs k)
        (f := fun p => if pairWin z p.1 p.2 then (independentFinProb q).w z else 0)
        (fun p hp => by dsimp only; split_ifs; exact (independentFinProb q).nonneg _; exact le_rfl) hmem
      simpa only [hwin, ↓reduceIte] using hs
    · simp only [somePairWins, decide_eq_true_eq, hz, ↓reduceIte]
      exact Finset.sum_nonneg (fun p hp => by split_ifs; exact (independentFinProb q).nonneg _; exact le_rfl)
  have hbound : (∑ z : Fin k → F × F,
      if somePairWins z = true then (independentFinProb q).w z else 0) ≤
      (k.choose 2 : ℝ) * omegaR F := by
    calc
      _ ≤ ∑ z : Fin k → F × F, ∑ p ∈ ascendingPairs k,
          if pairWin z p.1 p.2 then (independentFinProb q).w z else 0 :=
        Finset.sum_le_sum fun z hz => hp z
      _ = ∑ p ∈ ascendingPairs k, ∑ z : Fin k → F × F,
          if pairWin z p.1 p.2 then (independentFinProb q).w z else 0 := Finset.sum_comm
      _ ≤ ∑ p ∈ ascendingPairs k, omegaR F := by
        apply Finset.sum_le_sum
        intro p hp
        rw [independent_pairWin q (Finset.mem_filter.mp hp).2.ne]
        exact feasible_product_win_le_omega (q p.1) (q p.2) (hq _) (hq _)
      _ = ((ascendingPairs k).card : ℝ) * omegaR F := by simp
      _ ≤ (k.choose 2 : ℝ) * omegaR F :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast ascendingPairs_card_le k) omegaR_nonneg
  calc
    _ = (∑ z : Fin k → F × F,
        if somePairWins z = true then (independentFinProb q).w z else 0) := by
      rw [FinProb.map_w]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases h : somePairWins z = true <;> simp [h]
    _ ≤ _ := hbound

/-- The identical-factor case of the general independent experiment. -/
theorem independentFinProb_const {A : Type*} [Fintype A] (k : ℕ) (q : FinProb A) :
    independentFinProb (fun _ : Fin k => q) = productFinProb k q := by
  apply FinProb.ext
  intro z
  rfl

/-- The product-law event estimate in the paper, for every feasible one-site law. -/
theorem feasible_product_somePairWins_le {F : Type*} [Fintype F] [Field F]
    (k : ℕ) (q : FinProb (F × F)) (hq : UniformInput q) :
    (FinProb.map (productFinProb k q) somePairWins).w true ≤
      ((k : ℝ) * (k - 1) / 2) * omegaR F := by
  have h := independent_somePairWins_le (fun _ : Fin k => q) (fun _ => hq)
  rw [independentFinProb_const, Nat.cast_choose_two] at h
  exact h

/-- Finite-law event notation agrees with the Bool pushforward used in the witness. -/
theorem event_somePairWins_eq_map {F : Type*} [Fintype F] [Field F] {k : ℕ}
    (p : FinProb (Fin k → F × F)) :
    FinProb.event p (fun z => somePairWins z = true) = (FinProb.map p somePairWins).w true := by
  rfl

/-- The event upper bound for every Borel probability measure on the feasible slice.
There is no assumption on the number of mixture components. -/
theorem feasible_mixture_somePairWins_le {F : Type*} [Fintype F] [Field F]
    (S : Set (FinProb (F × F))) (hS : ∀ q ∈ S, UniformInput q)
    (μ : MeasureTheory.Measure S) [MeasureTheory.IsProbabilityMeasure μ] (k : ℕ) :
    (FinProb.map (FinProb.feasibleProductMixture S μ k) somePairWins).w true ≤
      ((k : ℝ) * (k - 1) / 2) * omegaR F := by
  rw [← event_somePairWins_eq_map]
  apply FinProb.feasibleProductMixture_event_le
  intro q
  rw [event_somePairWins_eq_map]
  exact feasible_product_somePairWins_le k q.val (hS q.val q.property)

/-- In particular, the literal uniform-input slice has the event bound for all μ. -/
theorem uniformInput_mixture_somePairWins_le {F : Type*} [Fintype F] [Field F]
    (μ : MeasureTheory.Measure {q : FinProb (F × F) | UniformInput q})
    [MeasureTheory.IsProbabilityMeasure μ] (k : ℕ) :
    (FinProb.map (FinProb.feasibleProductMixture {q : FinProb (F × F) | UniformInput q} μ k)
      somePairWins).w true ≤ ((k : ℝ) * (k - 1) / 2) * omegaR F :=
  feasible_mixture_somePairWins_le _ (fun _ hq => hq) μ k

end Paper06
