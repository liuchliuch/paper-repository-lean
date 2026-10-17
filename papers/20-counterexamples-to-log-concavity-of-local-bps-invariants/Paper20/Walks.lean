import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith

/-!
# Paper 20 — abstract walk model for Lemma 2.2

A word of length `m = 2d` is expanded step by step: at each letter one either
*stays* (weight `z` in the Hecke model) or *moves*.  A walk is therefore a
sequence of stay/move choices, i.e. a function `Fin m → Bool` (`true` = stay).

Lemma 2.2 is combinatorial once admissibility of the palindromic witnesses is
granted (the Hecke descent condition is external):

* each walk is uniquely determined by its stay-set, so the number of walks with
  `2h` stays is at most `binom(m, 2h)`;
* the palindromic walk — stay during the first `h` and the last `h` letters —
  has exactly `2h` stays, and for `h = 0` / `h = m/2` it is the unique walk with
  `0` / `m` stays.

We package admissibility as an arbitrary predicate on walks that contains the
palindromic witnesses, and count admissible walks by twice their number of
stays.  The upper bound holds for *any* admissibility predicate.
-/

namespace Paper20.Walks

/-- A walk of length `m` is a sequence of stay/move choices; `true` = stay. -/
abbrev Walk (m : ℕ) : Type := Fin m → Bool

variable {m : ℕ}

/-! ## Stay-sets and the determination of a walk -/

/-- Stay positions of a walk. -/
def staySet (w : Walk m) : Finset (Fin m) :=
  Finset.univ.filter fun i => w i = true

/-- Number of stays of a walk. -/
def nStays (w : Walk m) : ℕ := (staySet w).card

/-- The walk that stays exactly on `s` and moves at every other letter. -/
def ofStaySet (s : Finset (Fin m)) : Walk m :=
  fun i => decide (i ∈ s)

@[simp]
theorem mem_staySet (w : Walk m) (i : Fin m) :
    i ∈ staySet w ↔ w i = true := by
  simp [staySet]

theorem staySet_ofStaySet (w : Walk m) : ofStaySet (staySet w) = w := by
  funext i
  simp only [ofStaySet, mem_staySet]
  cases hi : w i
  · simp
  · simp

theorem ofStaySet_staySet (s : Finset (Fin m)) : staySet (ofStaySet s) = s := by
  ext i
  simp [staySet, ofStaySet]

/-- Key injection: a walk is determined by its stay-set (every other step is a move). -/
theorem staySet_injective : Function.Injective (staySet : Walk m → Finset (Fin m)) :=
  Function.LeftInverse.injective staySet_ofStaySet

theorem eq_of_staySet_eq {w₁ w₂ : Walk m} (h : staySet w₁ = staySet w₂) : w₁ = w₂ :=
  staySet_injective h

/-! ## Walks with a prescribed number of stays -/

/-- Walks of length `m` with exactly `s` stays. -/
def withStays (m s : ℕ) : Finset (Walk m) :=
  Finset.univ.filter fun w => nStays w = s

@[simp]
theorem mem_withStays {m s : ℕ} {w : Walk m} :
    w ∈ withStays m s ↔ nStays w = s := by
  simp [withStays]

/-- Unconstrained walk count: exactly `binom(m, s)` walks have `s` stays. -/
theorem card_withStays (m s : ℕ) :
    (withStays m s).card = Nat.choose m s := by
  have key : (withStays m s).card
      = ((Finset.univ : Finset (Fin m)).powersetCard s).card := by
    refine Finset.card_bij (fun w _ => staySet w) ?_ ?_ ?_
    · intro w hw
      refine Finset.mem_powersetCard.2 ⟨fun x _ => Finset.mem_univ x, ?_⟩
      simpa [nStays] using hw
    · intro w₁ _ w₂ _ hst
      exact staySet_injective hst
    · intro t ht
      refine ⟨ofStaySet t, ?_, ofStaySet_staySet t⟩
      have ht' : t.card = s := (Finset.mem_powersetCard.1 ht).2
      simp only [mem_withStays, nStays, ofStaySet_staySet t, ht']
  rw [key, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- Every walk has at most `m` stays. -/
theorem nStays_le (w : Walk m) : nStays w ≤ m := by
  have h : staySet w ⊆ (Finset.univ : Finset (Fin m)) := Finset.subset_univ _
  have := Finset.card_le_card h
  simpa [nStays, Finset.card_univ, Fintype.card_fin] using this

/-! ## The palindromic stay-pattern of Lemma 2.2 -/

/-- Stay during the first `h` and the last `h` letters of a word of length `m`
(the walk produced by the palindromic word `Q Q^rev` in the proof of Lemma 2.2). -/
def palindromic (m h : ℕ) : Walk m :=
  fun i => decide (i.val < h ∨ m ≤ i.val + h)

theorem mem_staySet_palindromic {m h : ℕ} {i : Fin m} :
    i ∈ staySet (palindromic m h) ↔ i.val < h ∨ m ≤ i.val + h := by
  simp [palindromic]

/-- The initial segment `{i : Fin m | i.val < h}` is equivalent to `Fin h` when `h ≤ m`. -/
def finEquivValLt {m h : ℕ} (hh : h ≤ m) : {i : Fin m // i.val < h} ≃ Fin h where
  toFun i := ⟨i.val, i.property⟩
  invFun i := ⟨Fin.castLE hh i, by rw [Fin.coe_castLE]; exact i.isLt⟩
  left_inv i := by
    ext
    simp
  right_inv i := by
    ext
    simp

/-- Cardinality of the initial segment `{i | i.val < h}` inside `Fin m`. -/
theorem card_filter_val_lt {m h : ℕ} (hh : h ≤ m) :
    (Finset.univ.filter fun i : Fin m => i.val < h).card = h := by
  have h1 : Fintype.card {i : Fin m // i.val < h}
      = (Finset.univ.filter fun i : Fin m => i.val < h).card :=
    Fintype.card_subtype _
  have h2 : Fintype.card {i : Fin m // i.val < h} = h :=
    (Fintype.card_congr (finEquivValLt hh)).trans (Fintype.card_fin h)
  rw [← h1, h2]

/-- The final segment `{i : Fin m | m ≤ i.val + h}` is equivalent to `Fin h` when `h ≤ m`. -/
def finEquivValAddLe {m h : ℕ} (hh : h ≤ m) : {i : Fin m // m ≤ i.val + h} ≃ Fin h where
  toFun i := ⟨i.val - (m - h), by omega⟩
  invFun i :=
    have hi : m - h + (i : ℕ) < m := by have := i.isLt; omega
    have hp : m ≤ (⟨m - h + (i : ℕ), hi⟩ : Fin m).val + h := by simp; omega
    ⟨⟨m - h + (i : ℕ), hi⟩, hp⟩
  left_inv i := by
    apply Subtype.eq
    apply Fin.ext
    have h1 := i.property
    simp
    omega
  right_inv i := by
    apply Fin.ext
    have h1 := i.isLt
    simp

/-- Cardinality of the final segment `{i | m ≤ i.val + h}` inside `Fin m`. -/
theorem card_filter_val_add_le {m h : ℕ} (hh : h ≤ m) :
    (Finset.univ.filter fun i : Fin m => m ≤ i.val + h).card = h := by
  have h1 : Fintype.card {i : Fin m // m ≤ i.val + h}
      = (Finset.univ.filter fun i : Fin m => m ≤ i.val + h).card :=
    Fintype.card_subtype _
  have h2 : Fintype.card {i : Fin m // m ≤ i.val + h} = h :=
    (Fintype.card_congr (finEquivValAddLe hh)).trans (Fintype.card_fin h)
  rw [← h1, h2]

theorem staySet_palindromic {m h : ℕ} :
    staySet (palindromic m h) =
      (Finset.univ.filter fun i : Fin m => i.val < h) ∪
        (Finset.univ.filter fun i : Fin m => m ≤ i.val + h) := by
  ext i
  simp only [mem_staySet_palindromic, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem disjoint_palindromic_halves {m h : ℕ} (hh : 2 * h ≤ m) :
    Disjoint (Finset.univ.filter fun i : Fin m => i.val < h)
      (Finset.univ.filter fun i : Fin m => m ≤ i.val + h) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  omega

/-- The palindromic walk has exactly `2h` stays when `2h ≤ m`. -/
theorem nStays_palindromic {m h : ℕ} (hh : 2 * h ≤ m) :
    nStays (palindromic m h) = 2 * h := by
  have h1 : h ≤ m := by omega
  rw [nStays, staySet_palindromic,
    Finset.card_union_of_disjoint (disjoint_palindromic_halves hh),
    card_filter_val_lt h1, card_filter_val_add_le h1]
  omega

@[simp]
theorem nStays_palindromic_zero (m : ℕ) : nStays (palindromic m 0) = 0 :=
  nStays_palindromic (by omega)

@[simp]
theorem nStays_palindromic_self (d : ℕ) : nStays (palindromic (2 * d) d) = 2 * d :=
  nStays_palindromic (by omega)

/-! ## Uniqueness at the endpoints -/

theorem staySet_eq_of_nStays_zero {w : Walk m} (h : nStays w = 0) : staySet w = ∅ := by
  rw [nStays] at h
  exact Finset.card_eq_zero.1 h

theorem eq_of_nStays_zero {w : Walk m} (h : nStays w = 0) : w = fun _ => false := by
  funext i
  cases hi : w i with
  | false => rfl
  | true =>
    exfalso
    have mem : i ∈ staySet w := by
      rw [mem_staySet]
      exact hi
    have := staySet_eq_of_nStays_zero h
    rw [this] at mem
    exact absurd mem (by simp)

theorem staySet_eq_of_nStays_full {w : Walk m} (h : nStays w = m) :
    staySet w = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [nStays] at h
  rw [h, Finset.card_univ, Fintype.card_fin]

theorem eq_of_nStays_full {w : Walk m} (h : nStays w = m) : w = fun _ => true := by
  funext i
  cases hi : w i with
  | true => rfl
  | false =>
    exfalso
    have hnot : i ∉ staySet w := by
      intro hin
      have := (mem_staySet w i).1 hin
      simp [hi] at this
    have hsub : staySet w ⊆ (Finset.univ : Finset (Fin m)).erase i := by
      intro x hx
      rw [Finset.mem_erase]
      exact ⟨fun hxi => by rw [hxi] at hx; exact hnot hx, Finset.mem_univ x⟩
    have hcard : ((Finset.univ : Finset (Fin m)).erase i).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have hm : 0 < m := by have := i.isLt; omega
    have hle : nStays w ≤ m - 1 := by
      show (staySet w).card ≤ m - 1
      calc (staySet w).card ≤ ((Finset.univ : Finset (Fin m)).erase i).card :=
          Finset.card_le_card hsub
        _ = m - 1 := hcard
    have heq : nStays w = m := h
    omega

theorem existsUnique_nStays_zero (m : ℕ) : ∃! w : Walk m, nStays w = 0 := by
  refine ⟨fun _ => false, ?_, ?_⟩
  · show nStays (fun _ => false) = 0
    rw [nStays, staySet]
    simp
  · intro w hw
    exact eq_of_nStays_zero hw

theorem existsUnique_nStays_full (m : ℕ) : ∃! w : Walk m, nStays w = m := by
  refine ⟨fun _ => true, ?_, ?_⟩
  · show nStays (fun _ => true) = m
    rw [nStays, staySet]
    simp
  · intro w hw
    exact eq_of_nStays_full hw

/-! ## Admissible walks -/

/-- Number of walks satisfying `adm` with exactly `2h` stays.  The predicate
`adm` is abstract (no decidability required): `Nat.card` of the subtype. -/
noncomputable def admissibleCount {m : ℕ} (adm : Walk m → Prop) (h : ℕ) : ℕ :=
  Nat.card {w : Walk m // adm w ∧ nStays w = 2 * h}

/-- Inclusion of admissible walks with `2h` stays into all walks with `2h` stays. -/
def admEmbedding {m : ℕ} (adm : Walk m → Prop) (h : ℕ) :
    {w : Walk m // adm w ∧ nStays w = 2 * h} → {w : Walk m // nStays w = 2 * h} :=
  fun w => ⟨w.1, w.2.2⟩

theorem admEmbedding_injective {m : ℕ} (adm : Walk m → Prop) (h : ℕ) :
    Function.Injective (admEmbedding adm h) := by
  intro a b hab
  have hval := congrArg
    (Subtype.val : {w : Walk m // nStays w = 2 * h} → Walk m) hab
  apply Subtype.eq
  exact hval

/-- Upper bound: at most `binom(m, 2h)` admissible walks with `2h` stays.
Holds for *any* admissibility predicate, by the stay-set injection. -/
theorem admissibleCount_le {m : ℕ} (adm : Walk m → Prop) (h : ℕ) :
    admissibleCount adm h ≤ Nat.choose m (2 * h) := by
  refine (Nat.card_le_card_of_injective (admEmbedding adm h)
      (admEmbedding_injective adm h)).trans ?_
  have h1 : Nat.card {w : Walk m // nStays w = 2 * h} = Nat.choose m (2 * h) := by
    have h2 : Fintype.card {w : Walk m // nStays w = 2 * h}
        = (withStays m (2 * h)).card := by
      have := Fintype.card_subtype (fun w : Walk m => nStays w = 2 * h)
      simpa [withStays] using this
    have h3 := card_withStays m (2 * h)
    rw [Nat.card_eq_fintype_card, h2, h3]
  exact le_of_eq h1

/-- Lower bound: the palindromic walk is a witness when it is admissible. -/
theorem admissibleCount_pos {m h : ℕ} {adm : Walk m → Prop}
    (hmem : adm (palindromic m h)) (hh : 2 * h ≤ m) : 0 < admissibleCount adm h := by
  haveI hne : Nonempty {w : Walk m // adm w ∧ nStays w = 2 * h} :=
    ⟨⟨palindromic m h, hmem, nStays_palindromic hh⟩⟩
  rw [admissibleCount]
  exact Nat.card_pos

/-- At `h = 0` there is only one subset of stays, so the count is exactly `1`
provided the all-move walk is admissible. -/
theorem admissibleCount_zero {m : ℕ} {adm : Walk m → Prop}
    (hmem : adm (palindromic m 0)) : admissibleCount adm 0 = 1 := by
  haveI hne : Nonempty {w : Walk m // adm w ∧ nStays w = 2 * (0 : ℕ)} :=
    ⟨⟨palindromic m 0, hmem, by simp⟩⟩
  haveI hsub : Subsingleton {w : Walk m // adm w ∧ nStays w = 2 * (0 : ℕ)} := by
    constructor
    intro a b
    have ha : nStays (a : Walk m) = 0 := by simpa using a.2.2
    have hb : nStays (b : Walk m) = 0 := by simpa using b.2.2
    exact Subtype.eq ((eq_of_nStays_zero ha).trans (eq_of_nStays_zero hb).symm)
  rw [admissibleCount]
  exact Nat.card_unique

/-- When `2h = m` every letter is a stay, so the count is exactly `1`
provided the all-stay walk is admissible. -/
theorem admissibleCount_full {m h : ℕ} {adm : Walk m → Prop}
    (hmem : adm (palindromic m h)) (hh : 2 * h = m) : admissibleCount adm h = 1 := by
  have h2 : 2 * h ≤ m := by omega
  haveI hne : Nonempty {w : Walk m // adm w ∧ nStays w = 2 * h} :=
    ⟨⟨palindromic m h, hmem, nStays_palindromic h2⟩⟩
  haveI hsub : Subsingleton {w : Walk m // adm w ∧ nStays w = 2 * h} := by
    constructor
    intro a b
    have ha : nStays (a : Walk m) = m := by
      have h2' : nStays (a : Walk m) = 2 * h := a.2.2
      omega
    have hb : nStays (b : Walk m) = m := by
      have h2' : nStays (b : Walk m) = 2 * h := b.2.2
      omega
    exact Subtype.eq ((eq_of_nStays_full ha).trans (eq_of_nStays_full hb).symm)
  rw [admissibleCount]
  exact Nat.card_unique

end Paper20.Walks
