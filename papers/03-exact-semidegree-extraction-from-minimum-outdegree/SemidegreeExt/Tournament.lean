import SemidegreeExt.Peeling
import SemidegreeExt.Identities
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Order.Interval.Finset.Fin

/-!
# Unmarked-direction transitive tournament (paper §2)

The unmarked possible direction on each pair forms a transitive tournament
with outdegrees `0,1,...,n-1`. It is **not** required to be a subdigraph of `G`.
-/

open Finset Digraph Nat
open Classical

namespace SemidegreeExt

variable {n : ℕ} {G : Digraph (Fin n)} {c : ℕ}

/-- Unmarked possible direction on a pair, determined by the earlier-deleted
endpoint's type in the peel order `L`. -/
def unmarkedAdj (G : Digraph (Fin n)) (c : ℕ) (L : List (Fin n)) (x y : Fin n) : Prop :=
  (L.idxOf x < L.idxOf y ∧ ¬ typeOOf G c L x) ∨
    (L.idxOf y < L.idxOf x ∧ typeOOf G c L y)

/-- The unmarked tournament on `Fin n`. -/
def unmarkedT (G : Digraph (Fin n)) (c : ℕ) (L : List (Fin n)) : Digraph (Fin n) where
  Adj := unmarkedAdj G c L

lemma unmarkedT_adj (G : Digraph (Fin n)) (c : ℕ) (L : List (Fin n)) (x y : Fin n) :
    (unmarkedT G c L).Adj x y ↔ unmarkedAdj G c L x y :=
  Iff.rfl

/-- For distinct vertices, exactly one of the two unmarked directions holds. -/
lemma unmarkedT_exactly_one {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    (hcomplete : L.toFinset = univ) (hnd : L.Nodup)
    {x y : Fin n} (hxy : x ≠ y) :
    (unmarkedAdj G c L x y ∧ ¬ unmarkedAdj G c L y x) ∨
      (¬ unmarkedAdj G c L x y ∧ unmarkedAdj G c L y x) := by
  unfold unmarkedAdj
  by_cases hlt : L.idxOf x < L.idxOf y
  · have hgt : ¬ L.idxOf y < L.idxOf x := fun h => (lt_asymm hlt) h
    by_cases hto : typeOOf G c L x
    · right
      constructor
      · intro h
        rcases h with ⟨_, hnot⟩ | ⟨hgt', _⟩
        · exact absurd hto hnot
        · exact absurd hgt' (lt_asymm hlt)
      · exact Or.inr ⟨hlt, hto⟩
    · left
      constructor
      · exact Or.inl ⟨hlt, hto⟩
      · intro h
        rcases h with ⟨hgt', _⟩ | ⟨_, hty'⟩
        · exact absurd hgt' (lt_asymm hlt)
        · exact absurd hty' hto
  · by_cases hgt : L.idxOf y < L.idxOf x
    · by_cases hty : typeOOf G c L y
      · left
        constructor
        · exact Or.inr ⟨hgt, hty⟩
        · intro h
          rcases h with ⟨hgt', hnot⟩ | ⟨hlt', _⟩
          · exact absurd hty hnot
          · exact absurd hlt' (lt_asymm hgt)
      · right
        constructor
        · intro h
          rcases h with ⟨hlt', _⟩ | ⟨hgt', hty'⟩
          · exact absurd hlt' (lt_asymm hgt)
          · exact absurd hty' hty
        · exact Or.inl ⟨hgt, hty⟩
    · -- idxOf x = idxOf y contradicts x ≠ y for a complete nodup list
      have heq : L.idxOf x = L.idxOf y := by omega
      have hx : x ∈ L := by
        have : x ∈ L.toFinset := by
          rw [hcomplete]
          exact mem_univ x
        exact List.mem_toFinset.1 this
      have hy : y ∈ L := by
        have : y ∈ L.toFinset := by
          rw [hcomplete]
          exact mem_univ y
        exact List.mem_toFinset.1 this
      exact absurd ((List.idxOf_inj hx hy).mp heq) hxy

/-- Type-I vertices deleted strictly before `v`. -/
noncomputable def countIBefore (G : Digraph (Fin n)) (c : ℕ) (L : List (Fin n)) (v : Fin n) : ℕ :=
  (univ.filter fun u => ¬ typeOOf G c L u ∧ L.idxOf u < L.idxOf v).card

/-- Type-O vertices deleted strictly after `v`. -/
noncomputable def countOAfter (G : Digraph (Fin n)) (c : ℕ) (L : List (Fin n)) (v : Fin n) : ℕ :=
  (univ.filter fun u => typeOOf G c L u ∧ L.idxOf v < L.idxOf u).card

/-- Total number of type-I vertices. -/
noncomputable def countAllI (G : Digraph (Fin n)) (c : ℕ) (L : List (Fin n)) : ℕ :=
  (univ.filter fun u => ¬ typeOOf G c L u).card

/-- Placement rank in the unmarked transitive tournament.
Final order: type-I vertices in increasing `idxOf`, then type-O in decreasing `idxOf`. -/
noncomputable def placeRank (G : Digraph (Fin n)) (c : ℕ) (L : List (Fin n)) (v : Fin n) : ℕ :=
  if typeOOf G c L v then
    countAllI G c L + countOAfter G c L v
  else
    countIBefore G c L v

/-- Helper: `s ⊂ t` from subset and a point in `t` not in `s`. -/
lemma ssubset_of_subset_and_notMem {α : Type*} {s t : Finset α}
    (hsub : s ⊆ t) {a : α} (hat : a ∈ t) (has : a ∉ s) : s ⊂ t :=
  Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun he => has (by rw [he]; exact hat)⟩

/-- Among type-I vertices, `countIBefore` is strictly monotone in `idxOf`. -/
lemma countIBefore_lt_iff {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    (hcomplete : L.toFinset = univ) (hnd : L.Nodup)
    {x y : Fin n} (hx : ¬ typeOOf G c L x) (hy : ¬ typeOOf G c L y)
    (hxy : x ≠ y) :
    countIBefore G c L x < countIBefore G c L y ↔ L.idxOf x < L.idxOf y := by
  have hidx_ne : L.idxOf x ≠ L.idxOf y := by
    intro heq
    have hmem (v : Fin n) : v ∈ L := by
      have : v ∈ L.toFinset := by
        rw [hcomplete]
        exact mem_univ v
      exact List.mem_toFinset.1 this
    exact hxy ((List.idxOf_inj (hmem x) (hmem y)).mp heq)
  have hlt_or : L.idxOf x < L.idxOf y ∨ L.idxOf y < L.idxOf x := by omega
  unfold countIBefore
  set s := univ.filter fun u => ¬ typeOOf G c L u ∧ L.idxOf u < L.idxOf x
  set t := univ.filter fun u => ¬ typeOOf G c L u ∧ L.idxOf u < L.idxOf y
  constructor
  · intro h
    rcases hlt_or with hlt | hgt
    · exact hlt
    · -- hgt : idx y < idx x; then t ⊆ s and y ∈ s \ t
      have hsub : t ⊆ s := by
        intro u hu
        simp only [s, t, mem_filter, mem_univ, true_and] at hu ⊢
        exact ⟨hu.1, by omega⟩
      have hys : y ∈ s := by
        simp only [s, mem_filter, mem_univ, true_and]
        exact ⟨hy, hgt⟩
      have hyt : y ∉ t := by
        intro hy'
        simp only [t, mem_filter, mem_univ, true_and] at hy'
        omega
      have hss : t ⊂ s := ssubset_of_subset_and_notMem hsub hys hyt
      have hlt' : t.card < s.card := Finset.card_lt_card hss
      omega
  · intro hlt
    have hsub : s ⊆ t := by
      intro u hu
      simp only [s, t, mem_filter, mem_univ, true_and] at hu ⊢
      exact ⟨hu.1, by omega⟩
    have hxt : x ∈ t := by
      simp only [t, mem_filter, mem_univ, true_and]
      exact ⟨hx, hlt⟩
    have hxs : x ∉ s := by
      intro hx'
      simp only [s, mem_filter, mem_univ, true_and] at hx'
      omega
    have hss : s ⊂ t := ssubset_of_subset_and_notMem hsub hxt hxs
    exact Finset.card_lt_card hss

/-- Among type-O vertices, `countOAfter` is strictly monotone in reverse `idxOf`. -/
lemma countOAfter_lt_iff {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    (hcomplete : L.toFinset = univ) (hnd : L.Nodup)
    {x y : Fin n} (hx : typeOOf G c L x) (hy : typeOOf G c L y)
    (hxy : x ≠ y) :
    countOAfter G c L x < countOAfter G c L y ↔ L.idxOf y < L.idxOf x := by
  have hidx_ne : L.idxOf x ≠ L.idxOf y := by
    intro heq
    have hmem (v : Fin n) : v ∈ L := by
      have : v ∈ L.toFinset := by
        rw [hcomplete]
        exact mem_univ v
      exact List.mem_toFinset.1 this
    exact hxy ((List.idxOf_inj (hmem x) (hmem y)).mp heq)
  have hlt_or : L.idxOf x < L.idxOf y ∨ L.idxOf y < L.idxOf x := by omega
  unfold countOAfter
  set s := univ.filter fun u => typeOOf G c L u ∧ L.idxOf x < L.idxOf u
  set t := univ.filter fun u => typeOOf G c L u ∧ L.idxOf y < L.idxOf u
  constructor
  · intro h
    rcases hlt_or with hgt | hlt
    · -- hgt : idx x < idx y; then t ⊆ s? wait idx x < idx y means s ⊇ t
      -- s = {O | idx x < idx u}, t = {O | idx y < idx u}
      -- if idx x < idx y then t ⊆ s; witness x ∈ s \ t? x is O, idx x < idx x false so x ∉ s
      -- witness y ∈ t? idx y < idx y false. Use: any u with idx x < idx u ≤ idx y.
      -- Simpler: if idx x < idx y then s ⊇ t and s ≠ t so #s > #t, contradicting h.
      have hsub : t ⊆ s := by
        intro u hu
        simp only [s, t, mem_filter, mem_univ, true_and] at hu ⊢
        exact ⟨hu.1, by omega⟩
      have hyt : y ∈ s := by
        simp only [s, mem_filter, mem_univ, true_and]
        exact ⟨hy, hgt⟩
      have hys : y ∉ t := by
        intro hy'
        simp only [t, mem_filter, mem_univ, true_and] at hy'
        omega
      have hss : t ⊂ s := ssubset_of_subset_and_notMem hsub hyt hys
      have hlt' : t.card < s.card := Finset.card_lt_card hss
      omega
    · exact hlt
  · intro hlt
    -- hlt : idx y < idx x; witness x ∈ t \ s
    have hsub : s ⊆ t := by
      intro u hu
      simp only [s, t, mem_filter, mem_univ, true_and] at hu ⊢
      exact ⟨hu.1, by omega⟩
    have hxt : x ∈ t := by
      simp only [t, mem_filter, mem_univ, true_and]
      exact ⟨hx, hlt⟩
    have hxs : x ∉ s := by
      intro hx'
      simp only [s, mem_filter, mem_univ, true_and] at hx'
      omega
    have hss : s ⊂ t := ssubset_of_subset_and_notMem hsub hxt hxs
    exact Finset.card_lt_card hss

/-- Unmarked direction is exactly "smaller placement rank". -/
lemma unmarkedAdj_iff_placeRank_lt {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    (hcomplete : L.toFinset = univ) (hnd : L.Nodup)
    {x y : Fin n} (hxy : x ≠ y) :
    unmarkedAdj G c L x y ↔ placeRank G c L x < placeRank G c L y := by
  have hidx_ne : L.idxOf x ≠ L.idxOf y := by
    intro heq
    have hmem (v : Fin n) : v ∈ L := by
      have : v ∈ L.toFinset := by
        rw [hcomplete]
        exact mem_univ v
      exact List.mem_toFinset.1 this
    exact hxy ((List.idxOf_inj (hmem x) (hmem y)).mp heq)
  have hlt_or : L.idxOf x < L.idxOf y ∨ L.idxOf y < L.idxOf x := by omega
  unfold unmarkedAdj placeRank
  by_cases hto : typeOOf G c L x
  · by_cases hty : typeOOf G c L y
    · rw [if_pos hto, if_pos hty]
      have hiff := countOAfter_lt_iff hcomplete hnd hto hty hxy
      constructor
      · rintro (⟨_, hnot⟩ | ⟨hgt, _⟩)
        · exact absurd hto hnot
        · exact (add_lt_add_iff_left _).2 (hiff.2 hgt)
      · intro h
        exact Or.inr ⟨hiff.1 ((add_lt_add_iff_left _).1 h), hty⟩
    · rw [if_pos hto, if_neg hty]
      constructor
      · rintro (⟨_, hnot⟩ | ⟨_, hty'⟩)
        · exact absurd hto hnot
        · exact absurd hty' hty
      · intro h
        have h1 : countIBefore G c L y < countAllI G c L := by
          unfold countIBefore countAllI
          have hsub : (univ.filter fun u => ¬ typeOOf G c L u ∧ L.idxOf u < L.idxOf y)
              ⊆ (univ.filter fun u => ¬ typeOOf G c L u) := by
            intro u hu
            simp only [mem_filter, mem_univ, true_and] at hu ⊢
            exact hu.1
          have hyt : y ∈ univ.filter fun u => ¬ typeOOf G c L u := by
            simp only [mem_filter, mem_univ, true_and]
            exact hty
          have hys : y ∉ (univ.filter fun u => ¬ typeOOf G c L u ∧ L.idxOf u < L.idxOf y) := by
            intro hy'
            simp only [mem_filter, mem_univ, true_and] at hy'
            omega
          exact Finset.card_lt_card (ssubset_of_subset_and_notMem hsub hyt hys)
        have h2 : countAllI G c L ≤ countAllI G c L + countOAfter G c L x :=
          Nat.le_add_right _ _
        omega
  · by_cases hty : typeOOf G c L y
    · rw [if_neg hto, if_pos hty]
      constructor
      · intro _
        have h1 : countIBefore G c L x < countAllI G c L := by
          unfold countIBefore countAllI
          have hsub : (univ.filter fun u => ¬ typeOOf G c L u ∧ L.idxOf u < L.idxOf x)
              ⊆ (univ.filter fun u => ¬ typeOOf G c L u) := by
            intro u hu
            simp only [mem_filter, mem_univ, true_and] at hu ⊢
            exact hu.1
          have hxs : x ∈ univ.filter fun u => ¬ typeOOf G c L u := by
            simp only [mem_filter, mem_univ, true_and]
            exact hto
          have hxt : x ∉ (univ.filter fun u => ¬ typeOOf G c L u ∧ L.idxOf u < L.idxOf x) := by
            intro hx'
            simp only [mem_filter, mem_univ, true_and] at hx'
            omega
          exact Finset.card_lt_card (ssubset_of_subset_and_notMem hsub hxs hxt)
        have h2 : countAllI G c L ≤ countAllI G c L + countOAfter G c L y :=
          Nat.le_add_right _ _
        omega
      · intro _
        rcases hlt_or with h | h
        · exact Or.inl ⟨h, hto⟩
        · exact Or.inr ⟨h, hty⟩
    · rw [if_neg hto, if_neg hty]
      have hiff := countIBefore_lt_iff hcomplete hnd hto hty hxy
      constructor
      · rintro (⟨hlt, _⟩ | ⟨_, hty'⟩)
        · exact hiff.2 hlt
        · exact absurd hty' hty
      · intro h
        exact Or.inl ⟨hiff.1 h, hto⟩

/-- `placeRank` is injective on `Fin n` for a complete nodup peel order. -/
lemma placeRank_inj {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    (hcomplete : L.toFinset = univ) (hnd : L.Nodup) :
    Function.Injective (placeRank G c L) := by
  intro x y h
  by_contra hxy
  have hiff_xy := unmarkedAdj_iff_placeRank_lt (G := G) (c := c) (L := L) hcomplete hnd hxy
  have hiff_yx := unmarkedAdj_iff_placeRank_lt (G := G) (c := c) (L := L) hcomplete hnd (Ne.symm hxy)
  -- exactly one of unmarkedAdj x y / y x holds; ranks differ one way
  have hex := unmarkedT_exactly_one (G := G) (c := c) (L := L) hcomplete hnd hxy
  rcases hex with ⟨hu, hnu⟩ | ⟨hnu, hu⟩
  · exact absurd (hiff_xy.1 hu) (by omega)
  · exact absurd (hiff_yx.1 hu) (by omega)

/-- Placement rank is strictly below `n`. -/
lemma placeRank_lt_n {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    (v : Fin n) : placeRank G c L v < n := by
  have hn : 0 < n := Fin.pos v
  unfold placeRank countAllI countOAfter countIBefore
  by_cases hto : typeOOf G c L v
  · rw [if_pos hto]
    have hdisj : Disjoint (univ.filter fun u => ¬ typeOOf G c L u)
        (univ.filter fun u => typeOOf G c L u ∧ L.idxOf v < L.idxOf u) := by
      rw [disjoint_left]
      intro u hu hv
      exact (Finset.mem_filter.1 hu).2 ((Finset.mem_filter.1 hv).2.1)
    have hnot : v ∉ (univ.filter fun u => ¬ typeOOf G c L u)
        ∪ (univ.filter fun u => typeOOf G c L u ∧ L.idxOf v < L.idxOf u) := by
      intro hu
      rcases Finset.mem_union.1 hu with hu | hu
      · exact (Finset.mem_filter.1 hu).2 hto
      · have hidx := (Finset.mem_filter.1 hu).2.2
        omega
    have hsub : ((univ.filter fun u => ¬ typeOOf G c L u)
        ∪ (univ.filter fun u => typeOOf G c L u ∧ L.idxOf v < L.idxOf u))
        ⊆ univ.erase v := by
      intro u hu
      refine Finset.mem_erase.2 ⟨?_, mem_univ u⟩
      intro he
      exact hnot (he ▸ hu)
    have hcard : ((univ.filter fun u => ¬ typeOOf G c L u)
        ∪ (univ.filter fun u => typeOOf G c L u ∧ L.idxOf v < L.idxOf u)).card
        = (univ.filter fun u => ¬ typeOOf G c L u).card
          + (univ.filter fun u => typeOOf G c L u ∧ L.idxOf v < L.idxOf u).card := by
      have h := Finset.card_union_add_card_inter
        (univ.filter fun u => ¬ typeOOf G c L u)
        (univ.filter fun u => typeOOf G c L u ∧ L.idxOf v < L.idxOf u)
      have hdisj' := Finset.disjoint_iff_inter_eq_empty.1 hdisj
      rw [hdisj', Finset.card_empty, add_zero] at h
      exact h
    have hle : ((univ.filter fun u => ¬ typeOOf G c L u)
        ∪ (univ.filter fun u => typeOOf G c L u ∧ L.idxOf v < L.idxOf u)).card ≤ n - 1 := by
      refine le_trans (card_le_card hsub) ?_
      rw [Finset.card_erase_of_mem (mem_univ v), Finset.card_univ, Fintype.card_fin]
    rw [← hcard]
    omega
  · rw [if_neg hto]
    have hnot : v ∉ (univ.filter fun u => ¬ typeOOf G c L u ∧ L.idxOf u < L.idxOf v) := by
      intro hu
      have hidx := (Finset.mem_filter.1 hu).2.2
      omega
    have hsub : (univ.filter fun u => ¬ typeOOf G c L u ∧ L.idxOf u < L.idxOf v)
        ⊆ univ.erase v := by
      intro u hu
      refine Finset.mem_erase.2 ⟨?_, mem_univ u⟩
      intro he
      exact hnot (he ▸ hu)
    have hle : (univ.filter fun u => ¬ typeOOf G c L u ∧ L.idxOf u < L.idxOf v).card
        ≤ n - 1 := by
      refine le_trans (card_le_card hsub) ?_
      rw [Finset.card_erase_of_mem (mem_univ v), Finset.card_univ, Fintype.card_fin]
    omega

/-- Rank as an element of `Fin n`. -/
noncomputable def rankFin (G : Digraph (Fin n)) (c : ℕ) (L : List (Fin n)) (v : Fin n) :
    Fin n :=
  ⟨placeRank G c L v, placeRank_lt_n v⟩

lemma rankFin_injective {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    (hcomplete : L.toFinset = univ) (hnd : L.Nodup) :
    Function.Injective (rankFin G c L) := by
  intro x y h
  have h1 : placeRank G c L x = placeRank G c L y := by
    simpa [rankFin] using congrArg Fin.val h
  exact placeRank_inj (G := G) (c := c) (L := L) hcomplete hnd h1

/-- Rank is a permutation of `Fin n`. -/
lemma rankFin_bijective {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    (hcomplete : L.toFinset = univ) (hnd : L.Nodup) :
    Function.Bijective (rankFin G c L) := by
  refine ⟨rankFin_injective hcomplete hnd, ?_⟩
  exact Finite.surjective_of_injective (rankFin_injective hcomplete hnd)

/-- Outdegree of `v` in the unmarked tournament is `n-1-placeRank v`. -/
lemma unmarked_outDeg_eq (G : Digraph (Fin n)) (c : ℕ) (L : List (Fin n))
    (hcomplete : L.toFinset = univ) (hnd : L.Nodup) (hlen : L.length = n) (v : Fin n) :
    (univ.filter fun u => unmarkedAdj G c L v u).card
      = n - 1 - placeRank G c L v := by
  classical
  have hfilter : (univ.filter fun u => unmarkedAdj G c L v u).card
      = (univ.filter fun u => placeRank G c L v < placeRank G c L u).card := by
    refine le_antisymm ?_ ?_
    · refine card_le_card fun u hu => ?_
      simp only [mem_filter, mem_univ, true_and] at hu ⊢
      by_cases huu : u = v
      · subst huu
        unfold unmarkedAdj at hu
        rcases hu with h | h <;> omega
      · exact (unmarkedAdj_iff_placeRank_lt (G := G) (c := c) (L := L)
          (x := v) (y := u) hcomplete hnd (Ne.symm huu)).1 hu
    · refine card_le_card fun u hu => ?_
      simp only [mem_filter, mem_univ, true_and] at hu ⊢
      by_cases huu : u = v
      · subst huu
        omega
      · exact (unmarkedAdj_iff_placeRank_lt (G := G) (c := c) (L := L)
          (x := v) (y := u) hcomplete hnd (Ne.symm huu)).2 hu
  rw [hfilter]
  -- switch to rankFin comparison
  have hfilter2 : (univ.filter fun u : Fin n => placeRank G c L v < placeRank G c L u).card
      = (univ.filter fun u : Fin n => rankFin G c L v < rankFin G c L u).card := by
    refine le_antisymm ?_ ?_
    · refine card_le_card fun u hu => ?_
      simp only [mem_filter, mem_univ, true_and] at hu ⊢
      exact Fin.lt_iff_val_lt_val.2 (by
        show (rankFin G c L v : ℕ) < (rankFin G c L u : ℕ)
        simpa [rankFin] using hu)
    · refine card_le_card fun u hu => ?_
      simp only [mem_filter, mem_univ, true_and] at hu ⊢
      have hval := Fin.lt_iff_val_lt_val.1 hu
      simpa [rankFin] using hval
  rw [hfilter2]
  have hbij : (univ.filter fun u : Fin n => rankFin G c L v < rankFin G c L u).card
      = (Finset.Ioi (rankFin G c L v)).card := by
    refine Finset.card_bij (fun u _ => rankFin G c L u) ?_ ?_ ?_
    · intro u hu
      simp only [mem_filter, mem_univ, true_and, Finset.mem_Ioi] at hu ⊢
      exact hu
    · intro u₁ _ u₂ _ h
      exact rankFin_injective (G := G) (c := c) (L := L) hcomplete hnd h
    · intro k hk
      obtain ⟨u, hu⟩ := (rankFin_bijective (G := G) (c := c) (L := L) hcomplete hnd).2 k
      refine ⟨u, ?_, hu⟩
      simp only [mem_filter, mem_univ, true_and]
      have hlt : rankFin G c L v < rankFin G c L u := by
        rw [hu]
        exact Finset.mem_Ioi.1 hk
      have hval := Fin.lt_iff_val_lt_val.1 hlt
      show (rankFin G c L v).val < (rankFin G c L u).val
      exact hval
  rw [hbij, Fin.card_Ioi]
  simp only [rankFin]

/-- `(v,u)` is a marked arc of `L` exactly when the marked direction applies. -/
lemma mem_marked_pair_iff {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    {v u : Fin n} (hadj : G.Adj v u) :
    (v, u) ∈ markedOfList G c L ↔
      (L.idxOf v < L.idxOf u ∧ typeOOf G c L v) ∨
        (L.idxOf u < L.idxOf v ∧ ¬ typeOOf G c L u) := by
  simp only [markedOfList, mem_filter, mem_univ, true_and]
  constructor
  · intro ⟨_, hmark⟩
    by_cases hlt : L.idxOf v < L.idxOf u
    · refine Or.inl ⟨hlt, ?_⟩
      simpa [hlt] using hmark
    · by_cases hgt : L.idxOf u < L.idxOf v
      · refine Or.inr ⟨hgt, ?_⟩
        rw [if_neg (by omega), if_pos hgt] at hmark
        exact hmark
      · have heq : L.idxOf v = L.idxOf u := by omega
        rw [if_neg (by omega), if_neg (by omega)] at hmark
        exact hmark.elim
  · intro h
    refine ⟨hadj, ?_⟩
    rcases h with ⟨hlt, hto⟩ | ⟨hgt, hnot⟩
    · rw [if_pos hlt]
      exact hto
    · rw [if_neg (by omega), if_pos hgt]
      exact hnot

/-- An arc `v → u` is marked iff it is not in the unmarked direction.
Requires a complete nodup peel order so that `idxOf` is injective. -/
lemma marked_iff_not_unmarked {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    (hcomplete : L.toFinset = univ) (hnd : L.Nodup)
    {v u : Fin n} (hvu : v ≠ u) (hadj : G.Adj v u) :
    ((markedOfList G c L).filter fun e => e.1 = v ∧ e.2 = u).Nonempty ↔
      ¬ unmarkedAdj G c L v u := by
  have hmem (v : Fin n) : v ∈ L := by
    have : v ∈ L.toFinset := by
      rw [hcomplete]
      exact mem_univ v
    exact List.mem_toFinset.1 this
  have hidx_ne : L.idxOf v ≠ L.idxOf u :=
    fun heq => hvu ((List.idxOf_inj (hmem v) (hmem u)).mp heq)
  have hlt_or : L.idxOf v < L.idxOf u ∨ L.idxOf u < L.idxOf v := by omega
  have hnon : ((markedOfList G c L).filter fun e => e.1 = v ∧ e.2 = u).Nonempty ↔
      (v, u) ∈ markedOfList G c L := by
    constructor
    · intro hex
      obtain ⟨e, he⟩ := hex.exists_mem
      simp only [mem_filter] at he
      obtain ⟨hmarked, he1, he2⟩ := he
      rcases e with ⟨a, b⟩
      simp only at he1 he2
      subst he1
      subst he2
      exact hmarked
    · intro h
      exact ⟨(v, u), by simp [h]⟩
  rw [hnon, mem_marked_pair_iff hadj]
  unfold unmarkedAdj
  rcases hlt_or with hlt | hgt
  · -- idx v < idx u: marked ↔ typeO v; unmarked ↔ ¬ typeO v
    constructor
    · intro h hnot
      rcases h with ⟨_, hto⟩ | ⟨hgt', _⟩
      · rcases hnot with ⟨_, hnot'⟩ | ⟨hgt'', _⟩
        · exact hnot' hto
        · exact absurd hgt'' (lt_asymm hlt)
      · exact absurd hgt' (lt_asymm hlt)
    · intro hnot
      refine Or.inl ⟨hlt, ?_⟩
      by_contra hto
      exact hnot (Or.inl ⟨hlt, hto⟩)
  · -- idx u < idx v: marked ↔ ¬ typeO u; unmarked ↔ typeO u
    constructor
    · intro h hnot
      rcases h with ⟨hlt', _⟩ | ⟨_, hnot'⟩
      · exact absurd hlt' (lt_asymm hgt)
      · rcases hnot with ⟨hlt'', _⟩ | ⟨_, hty⟩
        · exact absurd hlt'' (lt_asymm hgt)
        · exact hnot' hty
    · intro hnot
      refine Or.inr ⟨hgt, ?_⟩
      by_contra hty
      exact hnot (Or.inr ⟨hgt, hty⟩)

/-- Every out-arc of a loopless `G` is marked or unmarked. -/
lemma out_arc_marked_or_unmarked {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    (hG : Loopless G) (hcomplete : L.toFinset = univ) (hnd : L.Nodup)
    {v u : Fin n} (hadj : G.Adj v u) :
    ((markedOfList G c L).filter fun e => e.1 = v ∧ e.2 = u).Nonempty ∨
      unmarkedAdj G c L v u := by
  by_cases hunm : unmarkedAdj G c L v u
  · exact Or.inr hunm
  · left
    have hvu : v ≠ u := by
      intro he
      rw [he] at hadj
      exact hG u hadj
    have hiff := marked_iff_not_unmarked (G := G) (c := c) (L := L) hcomplete hnd hvu hadj
    exact hiff.2 hunm

/-- Marked out-arcs of `v` are at least `d` minus its unmarked outdegree. -/
lemma marked_out_ge (G : Digraph (Fin n)) (c : ℕ) (L : List (Fin n))
    (hG : Loopless G) (hcomplete : L.toFinset = univ) (hnd : L.Nodup)
    (hlen : L.length = n) (hd : ∀ v, d ≤ outDeg G v) (v : Fin n) :
    d - (n - 1 - placeRank G c L v)
      ≤ ((markedOfList G c L).filter fun e => e.1 = v).card := by
  classical
  let M := univ.filter fun u : Fin n => (v, u) ∈ markedOfList G c L
  let U := univ.filter fun u : Fin n => unmarkedAdj G c L v u
  have hsub : (univ.filter fun u => G.Adj v u) ⊆ M ∪ U := by
    intro u hu
    have hadj := (mem_filter.mp hu).2
    rcases out_arc_marked_or_unmarked hG hcomplete hnd hadj with hmark | hunmark
    · apply mem_union_left
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      obtain ⟨e, he⟩ := hmark
      have he' := mem_filter.mp he
      have heq : e = (v, u) := Prod.ext he'.2.1 he'.2.2
      simpa [heq] using he'.1
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hunmark⟩)
  have hM : M.card = ((markedOfList G c L).filter fun e => e.1 = v).card := by
    refine Finset.card_bij (fun u _ => (v, u)) ?_ ?_ ?_
    · intro u hu
      exact mem_filter.mpr ⟨(mem_filter.mp hu).2, rfl⟩
    · intro u₁ _ u₂ _ he
      exact congrArg Prod.snd he
    · intro e he
      have he' := mem_filter.mp he
      refine ⟨e.2, ?_, ?_⟩
      · apply mem_filter.mpr
        refine ⟨mem_univ _, ?_⟩
        have heq : (v, e.2) = e := Prod.ext he'.2.symm rfl
        simpa [heq] using he'.1
      · exact Prod.ext he'.2.symm rfl
  have hU : U.card = n - 1 - placeRank G c L v :=
    unmarked_outDeg_eq G c L hcomplete hnd hlen v
  have hdeg : outDeg G v ≤ M.card + U.card :=
    le_trans (card_le_card hsub) (card_union_le M U)
  have hdv := hd v
  rw [hM, hU] at hdeg
  omega

/-- `placeRank` is a permutation of `0..n-1`; summing `f (placeRank v)` is `∑_{i<n} f i`. -/
lemma sum_placeRank_eq_sum_range {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    (hcomplete : L.toFinset = univ) (hnd : L.Nodup) (f : ℕ → ℕ) :
    (∑ v : Fin n, f (placeRank G c L v)) = ∑ i ∈ range n, f i := by
  classical
  have hbij := rankFin_bijective (G := G) (c := c) (L := L) hcomplete hnd
  let e : Fin n ≃ Fin n := Equiv.ofBijective (rankFin G c L) hbij
  have hval (v : Fin n) : placeRank G c L v = (e v : ℕ) := by
    rfl
  have h1 : (∑ v : Fin n, f (placeRank G c L v))
      = ∑ v : Fin n, f (e v : ℕ) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hval]
  rw [h1]
  have h2 : (∑ v : Fin n, f (e v : ℕ))
      = ∑ r : Fin n, f (r : ℕ) :=
    Fintype.sum_equiv e (fun v => f (e v : ℕ)) (fun r => f (r : ℕ)) (fun v => rfl)
  rw [h2, Fin.sum_univ_eq_sum_range]

/-- `∑_{i<n} (d - (n-1-i)) = ∑_{i<n} (d - i)` by the flip `i ↦ n-1-i`. -/
lemma sum_sub_flip (n d : ℕ) :
    (∑ i ∈ range n, (d - (n - 1 - i))) = ∑ i ∈ range n, (d - i) := by
  have hbound (i : ℕ) (hi : i ∈ range n) : i ≤ n - 1 := by
    simp only [mem_range] at hi
    omega
  refine Finset.sum_bij (fun i _ => n - 1 - i) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_range] at hi ⊢
    omega
  · intro i₁ h₁ i₂ h₂ heq
    simp only [mem_range] at h₁ h₂
    have heq' : n - 1 - i₁ = n - 1 - i₂ := heq
    omega
  · intro i hi
    simp only [mem_range] at hi
    refine ⟨n - 1 - i, ?_, ?_⟩
    · simp only [mem_range]
      omega
    · have h1 : i ≤ n - 1 := by omega
      have : n - 1 - (n - 1 - i) = i := by omega
      omega
  · intro i hi
    simp only [mem_range] at hi
    exact rfl

/-- Sum of the nonnegative parts `∑_{i<n} (d-i)` is `d(d+1)/2` when `d < n`. -/
lemma sum_marked_tail_bound (n d : ℕ) (hdn : d < n) :
    d * (d + 1) / 2 ≤ ∑ i ∈ range n, (d - i) := by
  have h := sum_sub_eq n d (le_of_lt hdn)
  have heven : 2 * (d * (d + 1) / 2) = d * (d + 1) := by
    have hdiv := Nat.mul_div_cancel' (Even.two_dvd (Nat.even_mul_succ_self d))
    omega
  omega

/-- Lower bound: `|marked| ≥ d(d+1)/2` from the unmarked transitive tournament. -/
lemma marked_tournament_ge' (G : Digraph (Fin n)) (c : ℕ) (L : List (Fin n))
    (hG : Loopless G) (hcomplete : L.toFinset = univ) (hnd : L.Nodup) (hlen : L.length = n)
    (hd : ∀ v, d ≤ outDeg G v) (hn : 0 < n) (hdn : d < n) :
    d * (d + 1) / 2 ≤ (markedOfList G c L).card := by
  classical
  -- |marked| = ∑ v markedTail v
  have hfib : (markedOfList G c L).card
      = ∑ v : Fin n, ((markedOfList G c L).filter fun e => e.1 = v).card := by
    have H : Set.MapsTo Prod.fst (↑(markedOfList G c L) : Set (Fin n × Fin n))
        (↑(univ : Finset (Fin n)) : Set (Fin n)) := by
      intro e _
      exact mem_univ _
    have h := Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
      (s := markedOfList G c L) (t := univ) H
    exact h
  rw [hfib]
  -- each markedTail ≥ d - (n-1-placeRank v)
  have hpt : ∀ v : Fin n,
      d - (n - 1 - placeRank G c L v)
        ≤ ((markedOfList G c L).filter fun e => e.1 = v).card :=
    fun v => marked_out_ge G c L hG hcomplete hnd hlen hd v
  refine le_trans (sum_marked_tail_bound n d hdn) ?_
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun v _ => hpt v)
  -- ∑ i ∈ range n, (d - i) = ∑ v, (d - (n-1-placeRank v))
  have h1 : (∑ v : Fin n, (d - (n - 1 - placeRank G c L v)))
      = ∑ i ∈ range n, (d - (n - 1 - i)) :=
    sum_placeRank_eq_sum_range hcomplete hnd (fun i => d - (n - 1 - i))
  have h2 := sum_sub_flip n d
  omega

end SemidegreeExt
