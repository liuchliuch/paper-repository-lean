import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Inclusion counts for uniform `m`-subsets (Lemma 2.3 preparation)

Let `Ω = (univ : Finset (Fin n)).powersetCard m`. Then

* `# {I ∈ Ω | i ∉ I} = C(n-1, m)`
* `# {I ∈ Ω | i ∈ I} = C(n-1, m-1)`  for `1 ≤ m ≤ n`
-/

noncomputable section

open scoped BigOperators

namespace GeometricMedianCoresets
namespace VarianceCount

/-- Subsets of size `m` of `Fin n` that avoid a fixed point `i` are exactly
the `m`-subsets of `Fin n \ {i}`. -/
theorem filter_not_mem_eq_powersetCard_erase (n m : ℕ) (i : Fin n) :
    ((Finset.univ : Finset (Fin n)).powersetCard m).filter (fun s => i ∉ s)
      = ((Finset.univ : Finset (Fin n)).erase i).powersetCard m := by
  ext s
  constructor
  · intro hs
    have h1 : s ∈ (Finset.univ : Finset (Fin n)).powersetCard m :=
      (Finset.mem_filter.1 hs).1
    have h2 : i ∉ s := (Finset.mem_filter.1 hs).2
    have hsub : s ⊆ (Finset.univ : Finset (Fin n)).erase i := by
      intro x hx
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ x⟩
      intro hxi
      exact h2 (hxi ▸ hx)
    exact Finset.mem_powersetCard.2 ⟨hsub, (Finset.mem_powersetCard.1 h1).2⟩
  · intro hs
    have h1 : s ⊆ (Finset.univ : Finset (Fin n)).erase i ∧ s.card = m :=
      Finset.mem_powersetCard.1 hs
    refine Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨?_, h1.2⟩, ?_⟩
    · intro x hx
      exact Finset.mem_univ x
    · intro hi
      have : i ∈ (Finset.univ : Finset (Fin n)).erase i := h1.1 hi
      simp at this

/-- Count of `m`-subsets of `Fin n` avoiding `i`. -/
theorem card_filter_not_mem (n m : ℕ) (i : Fin n) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun s => i ∉ s)).card = (n - 1).choose m := by
  rw [filter_not_mem_eq_powersetCard_erase, Finset.card_powersetCard]
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hcard : ((Finset.univ : Finset (Fin n)).erase i).card = n - 1 := by
    rw [Finset.card_erase_of_mem hi, Finset.card_univ, Fintype.card_fin]
  rw [hcard]

/-- Total count of `m`-subsets. -/
theorem card_powersetCard (n m : ℕ) :
    ((Finset.univ : Finset (Fin n)).powersetCard m).card = n.choose m := by
  simp [Finset.card_powersetCard]

/-- Pascal identity. -/
theorem choose_eq_add (n m : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
    n.choose m = (n - 1).choose (m - 1) + (n - 1).choose m := by
  rcases m with _ | m'
  · exact absurd hm (by simp)
  · have h1 : n - 1 + 1 = n := by omega
    have h2 : (m' + 1) - 1 = m' := by omega
    have h3 : Nat.choose (n - 1 + 1) (m' + 1)
        = Nat.choose (n - 1) m' + Nat.choose (n - 1) (m' + 1) :=
      Nat.choose_succ_succ (n - 1) m'
    rw [h1] at h3
    rw [h2]
    exact h3

/-- Count of `m`-subsets containing a fixed `i`. -/
theorem card_filter_mem (n m : ℕ) (i : Fin n)
    (hm : 0 < m) (hmn : m ≤ n) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun s => i ∈ s)).card = (n - 1).choose (m - 1) := by
  classical
  set Ω : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard m
  set A : Finset (Finset (Fin n)) := Ω.filter (fun s => i ∈ s)
  set B : Finset (Finset (Fin n)) := Ω.filter (fun s => i ∉ s)
  have hunion : A ∪ B = Ω := by
    ext s
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      rcases h with h | h
      · exact h.1
      · exact h.1
    · intro hs
      by_cases hi : i ∈ s
      · exact Or.inl ⟨hs, hi⟩
      · exact Or.inr ⟨hs, hi⟩
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro s hs₁ hs₂
    exact (Finset.mem_filter.1 hs₂).2 ((Finset.mem_filter.1 hs₁).2)
  have hcard : A.card + B.card = Ω.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hΩ : Ω.card = n.choose m := by
    simp [Ω, Finset.card_powersetCard]
  have hB : B.card = (n - 1).choose m := by
    have := card_filter_not_mem n m i
    simpa [B, Ω] using this
  have hA : A.card = (n - 1).choose (m - 1) := by
    have hpascal := choose_eq_add n m hm hmn
    omega
  simpa [A] using hA



/-- Cardinality of `univ` with two distinct points erased. -/
theorem card_erase_erase (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (((Finset.univ : Finset (Fin n)).erase i).erase j).card = n - 2 := by
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i :=
    Finset.mem_erase_of_ne_of_mem (Ne.symm hij) (Finset.mem_univ j)
  rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hi,
    Finset.card_univ, Fintype.card_fin]
  omega

/-- Reinsertion identity: a set containing `i ≠ j` is recovered by erasing both
and inserting them back. -/
theorem eq_insert_insert_erase {n : ℕ} (s : Finset (Fin n))
    (i j : Fin n) (_hij : i ≠ j) (hi : i ∈ s) (hj : j ∈ s) :
    s = insert i (insert j ((s.erase i).erase j)) := by
  ext x
  constructor
  · intro hx
    by_cases hx1 : x = i
    · rw [hx1]
      exact Finset.mem_insert_self i _
    · by_cases hx2 : x = j
      · rw [hx2]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self j _)
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_insert_of_mem
        refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, hx⟩⟩
        · intro h; exact hx2 h
        · intro h; exact hx1 h
  · intro hx
    by_cases hx1 : x = i
    · rw [hx1]; exact hi
    · by_cases hx2 : x = j
      · rw [hx2]; exact hj
      · have hx' := hx
        rw [Finset.mem_insert] at hx'
        rcases hx' with h | h
        · exact absurd h hx1
        · rw [Finset.mem_insert] at h
          rcases h with h | h
          · exact absurd h hx2
          · exact (Finset.mem_erase.1 (Finset.mem_erase.1 h).2).2

/-- Erase-then-insert cancels for distinct points outside the rest. -/
theorem erase_insert_erase_insert {n : ℕ} (i j : Fin n) (t : Finset (Fin n))
    (hij : i ≠ j) (hi : i ∉ t) (hj : j ∉ t) :
    ((insert i (insert j t)).erase i).erase j = t := by
  have h1 : (insert i (insert j t)).erase i = insert j t := by
    rw [Finset.erase_insert]
    intro h
    rw [Finset.mem_insert] at h
    rcases h with h | h
    · exact hij h
    · exact hi h
  rw [h1, Finset.erase_insert]
  intro h; exact hj h

/-- Cardinality after erasing two members. -/
theorem card_erase_erase_mem {n : ℕ} (s : Finset (Fin n)) (i j : Fin n) (hij : i ≠ j)
    (hi : i ∈ s) (hj : j ∈ s) :
    ((s.erase i).erase j).card = s.card - 2 := by
  have hj' : j ∈ s.erase i := Finset.mem_erase_of_ne_of_mem hij.symm hj
  rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi]
  omega

/-- Cardinality after inserting two new points. -/
theorem card_insert_insert {n : ℕ} (t : Finset (Fin n)) (i j : Fin n) (hij : i ≠ j)
    (hi : i ∉ t) (hj : j ∉ t) :
    (insert i (insert j t)).card = t.card + 2 := by
  have hi2 : i ∉ insert j t := by
    intro h
    rw [Finset.mem_insert] at h
    rcases h with h | h
    · exact hij h
    · exact hi h
  rw [Finset.card_insert_of_notMem hi2, Finset.card_insert_of_notMem hj]

/-- Two-element inclusion count. -/
theorem card_filter_mem_mem (n m : ℕ) (i j : Fin n) (hij : i ≠ j)
    (hm : 2 ≤ m) (hmn : m ≤ n) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun s => i ∈ s ∧ j ∈ s)).card = (n - 2).choose (m - 2) := by
  classical
  set Ω : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard m
  set F : Finset (Finset (Fin n)) := Ω.filter (fun s => i ∈ s ∧ j ∈ s)
  set G : Finset (Finset (Fin n)) :=
    (((Finset.univ : Finset (Fin n)).erase i).erase j).powersetCard (m - 2)
  let e : Finset (Fin n) → Finset (Fin n) := fun s => (s.erase i).erase j
  let e_inv : Finset (Fin n) → Finset (Fin n) := fun t => insert i (insert j t)
  have hleft : Set.LeftInvOn e_inv e F := by
    intro s hs
    have h1 : i ∈ s ∧ j ∈ s := (Finset.mem_filter.1 hs).2
    exact (eq_insert_insert_erase s i j hij h1.1 h1.2).symm
  have hright : Set.RightInvOn e_inv e G := by
    intro t ht
    have h1 : t ⊆ ((Finset.univ : Finset (Fin n)).erase i).erase j ∧ t.card = m - 2 :=
      Finset.mem_powersetCard.1 ht
    have hnotin_i : i ∉ t := fun hin => absurd (h1.1 hin) (by simp)
    have hnotin_j : j ∉ t := fun hin => absurd (h1.1 hin) (by simp)
    exact erase_insert_erase_insert i j t hij hnotin_i hnotin_j
  have hmapF : Set.MapsTo e F G := by
    intro s hs
    have h1 : s ∈ Ω ∧ i ∈ s ∧ j ∈ s := Finset.mem_filter.1 hs
    have h2 : s ⊆ (Finset.univ : Finset (Fin n)) ∧ s.card = m :=
      Finset.mem_powersetCard.1 h1.1
    refine Finset.mem_powersetCard.2 ⟨?_, ?_⟩
    · intro x hx
      have hx1 := Finset.mem_erase.1 hx
      have hx2 := Finset.mem_erase.1 hx1.2
      refine Finset.mem_erase.2 ⟨hx1.1, Finset.mem_erase.2 ⟨hx2.1, Finset.mem_univ x⟩⟩
    · have hcard : ((s.erase i).erase j).card = s.card - 2 :=
        card_erase_erase_mem s i j hij h1.2.1 h1.2.2
      rw [hcard, h2.2]
  have hmapG : Set.MapsTo e_inv G F := by
    intro t ht
    have h1 : t ⊆ ((Finset.univ : Finset (Fin n)).erase i).erase j ∧ t.card = m - 2 :=
      Finset.mem_powersetCard.1 ht
    have hnotin_i : i ∉ t := fun hin => absurd (h1.1 hin) (by simp)
    have hnotin_j : j ∉ t := fun hin => absurd (h1.1 hin) (by simp)
    have hi : i ∈ insert i (insert j t) := Finset.mem_insert_self i _
    have hj : j ∈ insert i (insert j t) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_self j t)
    have hcard : (insert i (insert j t)).card = t.card + 2 :=
      card_insert_insert t i j hij hnotin_i hnotin_j
    refine Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨?_, ?_⟩, hi, hj⟩
    · intro x _hx
      exact Finset.mem_univ x
    · rw [hcard, h1.2]
      omega
  have hcard : F.card = G.card :=
    Finset.card_nbij' e e_inv hmapF hmapG hleft hright
  rw [hcard]
  change G.card = (n - 2).choose (m - 2)
  have hG : G = (((Finset.univ : Finset (Fin n)).erase i).erase j).powersetCard (m - 2) := rfl
  rw [hG, Finset.card_powersetCard, card_erase_erase n i j hij]

end VarianceCount
end GeometricMedianCoresets
