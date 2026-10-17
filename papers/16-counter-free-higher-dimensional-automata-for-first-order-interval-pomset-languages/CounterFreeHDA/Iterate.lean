/-
Copyright (c) 2026. Counter-Free Higher-Dimensional Automata formalisation.
Stabilisation under iteration: Lemma 4.1 (stable survival) and
Lemma 4.2 (separation of the boundary cubes).
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Stabilisation under iteration (Section 4)

We formalise the two counting/survival lemmas of Section 4 at the level at which
they are used.

* The interface partial injection `f_P : {1,…,r} ⇀ {1,…,r}` is an
  order-preserving partial injection on `Fin r`, packaged as
  `PartialInjectiveOrder`.  Its powers record survival of shared interface
  events under gluing.  Lemma 4.1: for `n ≥ r` (hence `n ≥ k` when `r ≤ k`),
  `f_P^n` is the partial identity on the fixed set `E`.
* Event counting of glued powers is packaged in `PomCounted`: an endomorphism
  of an interface of size `r` that introduces `d` new events per glue has
  `|P^n| = r + n * d`.  Lemma 4.2: if `P ≠ id` then `d ≥ 1` and
  `|P^n| > 2r` for `n ≥ k + 1`, so `P^n` has an event outside both interfaces.
-/

namespace CounterFreeHDA

/-! ## Partial maps on `Fin r` -/

/-- Partial endomaps of the finite linear order `Fin r`.  This is the carrier of
the interface partial injection `f_P` and of its iterates. -/
abbrev PartialMap (r : ℕ) : Type := Fin r → Option (Fin r)

namespace PartialMap

/-- Identity partial map (total on `Fin r`). -/
def pid (r : ℕ) : PartialMap r := fun i => some i

/-- Kleisli composition: `(comp f g) i` applies `f` at `i`, then `g`. -/
def comp {r : ℕ} (f g : PartialMap r) : PartialMap r := fun i => (f i).bind g

/-- Iterates of a partial map: `f^0 = id`, `f^{n+1} = f^n ∘ f`. -/
def pow {r : ℕ} (f : PartialMap r) : ℕ → PartialMap r
  | 0 => pid r
  | n + 1 => comp (pow f n) f

@[simp] theorem pid_apply {r : ℕ} (i : Fin r) : pid r i = some i := rfl

@[simp] theorem comp_apply {r : ℕ} (f g : PartialMap r) (i : Fin r) :
    comp f g i = (f i).bind g := rfl

@[simp] theorem pow_zero {r : ℕ} (f : PartialMap r) : pow f 0 = pid r := rfl

theorem pow_succ {r : ℕ} (f : PartialMap r) (n : ℕ) :
    pow f (n + 1) = comp (pow f n) f := rfl

@[simp] theorem pow_succ_apply {r : ℕ} (f : PartialMap r) (n : ℕ) (i : Fin r) :
    pow f (n + 1) i = (pow f n i).bind f := rfl

theorem pow_one {r : ℕ} (f : PartialMap r) : pow f 1 = f := by
  funext i
  rfl

/-- Bind unfolds to an existential over the first component. -/
theorem bind_eq_some_iff {α β : Type*} {x : Option α} {g : α → Option β} {b : β} :
    x.bind g = some b ↔ ∃ a, x = some a ∧ g a = some b := by
  cases x with
  | none =>
    constructor
    · intro h; simp at h
    · intro h; obtain ⟨a, ha, _⟩ := h; simp at ha
  | some a =>
    constructor
    · intro h
      exact ⟨a, rfl, h⟩
    · intro h
      obtain ⟨a', ha', hg⟩ := h
      simp at ha'
      subst ha'
      exact hg

theorem exists_of_succ_eq_some {r : ℕ} {f : PartialMap r} {i z : Fin r} {t : ℕ}
    (h : pow f (t + 1) i = some z) : ∃ a, pow f t i = some a ∧ f a = some z :=
  bind_eq_some_iff.mp h

/-- Powers distribute over addition of exponents. -/
theorem pow_add {r : ℕ} (f : PartialMap r) (a t : ℕ) :
    pow f (a + t) = comp (pow f a) (pow f t) := by
  induction t with
  | zero =>
    funext i
    simp only [Nat.add_zero, pow_zero, comp_apply, pid_apply]
    cases pow f a i <;> rfl
  | succ t ih =>
    funext i
    have h1 : a + (t + 1) = (a + t) + 1 := by omega
    show pow f (a + (t + 1)) i = (pow f a i).bind (pow f (t + 1))
    rw [h1, pow_succ_apply, ih]
    simp only [comp_apply]
    cases pow f a i with
    | none => rfl
    | some x => simp

theorem pow_add_apply {r : ℕ} {f : PartialMap r} {a : ℕ} {i z : Fin r}
    (h : pow f a i = some z) (t : ℕ) :
    pow f (a + t) i = pow f t z := by
  rw [pow_add, comp_apply, h]
  rfl

/-- Once an iterate is undefined, all later iterates are undefined. -/
theorem pow_eq_none_of_eq_none {r : ℕ} {f : PartialMap r} {t : ℕ} {i : Fin r}
    (h : pow f t i = none) (s : ℕ) (hs : t ≤ s) : pow f s i = none := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hs
  clear hs
  induction u with
  | zero => simpa using h
  | succ u ih =>
    rw [Nat.add_succ, pow_succ_apply, ih]
    rfl

end PartialMap

open PartialMap (pid comp pow bind_eq_some_iff exists_of_succ_eq_some pow_add
  pow_add_apply pow_eq_none_of_eq_none pow_succ_apply)

/-! ### Order-preserving partial injections -/

/-- Order-preserving: whenever both `i` and `i'` are defined, their images are
related in the same strict order. -/
def IsOrderPreserving {r : ℕ} (f : PartialMap r) : Prop :=
  ∀ ⦃i i' : Fin r⦄ ⦃j j' : Fin r⦄, i < i' → f i = some j → f i' = some j' → j < j'

/-- Partial injectivity: distinct defined points have distinct images. -/
def IsPartialInjective {r : ℕ} (f : PartialMap r) : Prop :=
  ∀ ⦃i i' : Fin r⦄ ⦃j : Fin r⦄, f i = some j → f i' = some j → i = i'

/-- An order-preserving partial injection on `Fin r`.  This is the abstract form
of the interface map `f_P` of Section 4: source position `i` maps to target
position `j` when both are the same event.  Order preservation holds because
the two interface orders agree on shared events. -/
structure PartialInjectiveOrder (r : ℕ) where
  toFun : PartialMap r
  orderPreserving : IsOrderPreserving toFun
  partialInjective : IsPartialInjective toFun

/-- A position is *fixed* when it maps to itself. -/
def IsFixed {r : ℕ} (f : PartialMap r) (i : Fin r) : Prop := f i = some i

instance instDecidableIsFixed {r : ℕ} (f : PartialMap r) (i : Fin r) :
    Decidable (IsFixed f i) :=
  inferInstanceAs (Decidable (f i = some i))

/-- The fixed set `E` of `f_P`. -/
def fixedPoints {r : ℕ} (f : PartialMap r) : Set (Fin r) := {i | IsFixed f i}

instance instDecidableMemFixedPoints {r : ℕ} (f : PartialMap r) (i : Fin r) :
    Decidable (i ∈ fixedPoints f) :=
  instDecidableIsFixed f i

theorem pid_orderPreserving {r : ℕ} : IsOrderPreserving (pid r) := by
  intro i i' j j' hlt h1 h2
  simp [pid] at h1 h2
  subst h1
  subst h2
  exact hlt

theorem pid_partialInjective {r : ℕ} : IsPartialInjective (pid r) := by
  intro i i' j h1 h2
  simp [pid] at h1 h2
  subst h1
  exact h2.symm

theorem comp_orderPreserving {r : ℕ} {f g : PartialMap r}
    (hf : IsOrderPreserving f) (hg : IsOrderPreserving g) :
    IsOrderPreserving (comp f g) := by
  intro i i' j j' hlt h1 h2
  obtain ⟨a, hfa, hga⟩ := bind_eq_some_iff.mp h1
  obtain ⟨a', hfa', hga'⟩ := bind_eq_some_iff.mp h2
  exact hg (hf hlt hfa hfa') hga hga'

theorem comp_partialInjective {r : ℕ} {f g : PartialMap r}
    (hf : IsPartialInjective f) (hg : IsPartialInjective g) :
    IsPartialInjective (comp f g) := by
  intro i i' j h1 h2
  obtain ⟨a, hfa, hga⟩ := bind_eq_some_iff.mp h1
  obtain ⟨a', hfa', hga'⟩ := bind_eq_some_iff.mp h2
  have haa' : a = a' := hg hga hga'
  subst haa'
  exact hf hfa hfa'

theorem pow_orderPreserving {r : ℕ} {f : PartialMap r}
    (hf : IsOrderPreserving f) (n : ℕ) : IsOrderPreserving (pow f n) := by
  induction n with
  | zero => exact pid_orderPreserving
  | succ n ih => exact comp_orderPreserving ih hf

theorem pow_partialInjective {r : ℕ} {f : PartialMap r}
    (hf : IsPartialInjective f) (n : ℕ) : IsPartialInjective (pow f n) := by
  induction n with
  | zero => exact pid_partialInjective
  | succ n ih => exact comp_partialInjective ih hf

/-- Powers of an order-preserving partial injection are again order-preserving
partial injections; in particular `f_P^n` makes sense as such a map. -/
def PartialInjectiveOrder.pow {r : ℕ} (f : PartialInjectiveOrder r) (n : ℕ) :
    PartialInjectiveOrder r where
  toFun := PartialMap.pow f.toFun n
  orderPreserving := pow_orderPreserving f.orderPreserving n
  partialInjective := pow_partialInjective f.partialInjective n

/-- The fixed set `E` of an order-preserving partial injection. -/
def PartialInjectiveOrder.E {r : ℕ} (f : PartialInjectiveOrder r) : Set (Fin r) :=
  fixedPoints f.toFun

instance instDecidableMemE {r : ℕ} (f : PartialInjectiveOrder r) (i : Fin r) :
    Decidable (i ∈ f.E) :=
  instDecidableMemFixedPoints f.toFun i

/-! ### Orbit structure of order-preserving partial injections -/

/-- If `f x = some y` with `x < y`, every defined positive iterate of `x`
is strictly larger than `x`. -/
theorem pow_val_lt {r : ℕ} {f : PartialMap r} (hop : IsOrderPreserving f)
    {x y : Fin r} (hmap : f x = some y) (hlt : x < y) :
    ∀ (t : ℕ) (z : Fin r), pow f t x = some z → 0 < t → x < z := by
  intro t
  induction t with
  | zero =>
    intro z _ hpos
    exact absurd hpos (Nat.lt_irrefl 0)
  | succ t ih =>
    intro z hpow _
    obtain ⟨a, ha, hfa⟩ := exists_of_succ_eq_some hpow
    by_cases ht : t = 0
    · subst ht
      have ha' : a = x := by
        simpa [pow, pid] using ha.symm
      subst ha'
      have hzz : z = y := by
        rw [hmap] at hfa
        exact (Option.some.inj hfa).symm
      subst hzz
      exact hlt
    · have hxa : x < a := ih a ha (Nat.pos_of_ne_zero ht)
      exact lt_trans hlt (hop hxa hmap hfa)

/-- If `f x = some y` with `y < x`, every defined positive iterate of `x`
is strictly smaller than `x`. -/
theorem pow_val_gt {r : ℕ} {f : PartialMap r} (hop : IsOrderPreserving f)
    {x y : Fin r} (hmap : f x = some y) (hlt : y < x) :
    ∀ (t : ℕ) (z : Fin r), pow f t x = some z → 0 < t → z < x := by
  intro t
  induction t with
  | zero =>
    intro z _ hpos
    exact absurd hpos (Nat.lt_irrefl 0)
  | succ t ih =>
    intro z hpow _
    obtain ⟨a, ha, hfa⟩ := exists_of_succ_eq_some hpow
    by_cases ht : t = 0
    · subst ht
      have ha' : a = x := by
        simpa [pow, pid] using ha.symm
      subst ha'
      have hzz : z = y := by
        rw [hmap] at hfa
        exact (Option.some.inj hfa).symm
      subst hzz
      exact hlt
    · have hax : a < x := ih a ha (Nat.pos_of_ne_zero ht)
      exact lt_trans (hop hax hfa hmap) hlt

/-- If a positive iterate of `i` is defined, then `f i` is defined. -/
theorem exists_image_of_pow_defined {r : ℕ} {f : PartialMap r} {i : Fin r} :
    ∀ {m : ℕ} {z : Fin r}, 0 < m → pow f m i = some z → ∃ w, f i = some w := by
  intro m
  induction m with
  | zero =>
    intro z hpos _
    exact absurd hpos (Nat.lt_irrefl 0)
  | succ t ih =>
    intro z _ hpow
    obtain ⟨a, ha, hfa⟩ := exists_of_succ_eq_some hpow
    by_cases ht : t = 0
    · subst ht
      have ha' : a = i := by
        simpa [pow, pid] using ha.symm
      subst ha'
      exact ⟨z, hfa⟩
    · exact ih (Nat.pos_of_ne_zero ht) ha

/-- A nontrivial return is impossible: if `f^m i = some i` with `m > 0`, then
`i` is already fixed.  This is the cycle argument of Lemma 4.1: an
order-preserving partial injection on a finite linear order has no cycle of
length greater than one. -/
theorem isFixed_of_pow_self {r : ℕ} {f : PartialMap r}
    (hop : IsOrderPreserving f)
    {i : Fin r} {m : ℕ} (hm : 0 < m) (hpow : pow f m i = some i) :
    IsFixed f i := by
  obtain ⟨j, hj⟩ := exists_image_of_pow_defined hm hpow
  by_cases hji : j = i
  · subst hji
    exact hj
  · by_cases hlt : i < j
    · exact absurd (pow_val_lt hop hj hlt m i hpow hm) (lt_irrefl i)
    · have hjlt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) hji
      exact absurd (pow_val_gt hop hj hjlt m i hpow hm) (lt_irrefl i)

/-- Injectivity: the only preimage of a fixed point is that fixed point. -/
theorem eq_of_image_fixed {r : ℕ} {f : PartialMap r}
    (hinj : IsPartialInjective f) {i v : Fin r}
    (hfix : IsFixed f v) (h : f i = some v) : i = v :=
  hinj h hfix

/-- If some iterate of `i` lands on a fixed point `v`, then `i = v`. -/
theorem eq_of_pow_eq_fixed {r : ℕ} {f : PartialMap r}
    (hinj : IsPartialInjective f) {i v : Fin r} {a : ℕ}
    (hfix : IsFixed f v) (h : pow f a i = some v) : i = v := by
  induction a with
  | zero =>
    have h0 : some i = some v := by simpa [pow, pid] using h
    exact Option.some.inj h0
  | succ t ih =>
    obtain ⟨w, hw, hfw⟩ := exists_of_succ_eq_some h
    have hwv : w = v := eq_of_image_fixed hinj hfix hfw
    subst hwv
    exact ih hw

/-- Fixed points survive every iterate. -/
theorem pow_isFixed {r : ℕ} {f : PartialMap r} {i : Fin r}
    (hfix : IsFixed f i) (n : ℕ) : pow f n i = some i := by
  induction n with
  | zero => simp [pow, pid]
  | succ n ih =>
    rw [pow_succ_apply, ih]
    exact hfix

/-- A nonfixed point dies: some iterate of length at most `r` is undefined.
This is the "nonfixed chains end after at most `r` applications" half of
Lemma 4.1. -/
theorem exists_pow_none_of_not_isFixed {r : ℕ} {f : PartialMap r}
    (hop : IsOrderPreserving f) (hinj : IsPartialInjective f)
    {i : Fin r} (h : ¬ IsFixed f i) :
    ∃ m, m ≤ r ∧ pow f m i = none := by
  by_cases hr : r = 0
  · subst hr
    exact Fin.elim0 i
  · by_contra! hall
    -- Every iterate `0 ≤ t ≤ r` is defined.
    have hsome : ∀ t ≤ r, ∃ z : Fin r, pow f t i = some z := by
      intro t ht
      cases hopt : pow f t i with
      | none => exact absurd hopt (hall t ht)
      | some z => exact ⟨z, rfl⟩
    -- Values of the first `r + 1` iterates, as a map `Fin (r+1) → Fin r`.
    have hbound : ∀ t : Fin (r + 1), t.val ≤ r := fun t => by
      have := t.isLt
      omega
    let F : Fin (r + 1) → Fin r := fun t =>
      Classical.choose (hsome t.val (hbound t))
    have F_spec : ∀ t : Fin (r + 1), pow f t.val i = some (F t) := fun t =>
      Classical.choose_spec (hsome t.val (hbound t))
    -- Any collision of two distinct values forces `i` fixed.
    have F_nocoll : ∀ t u : Fin (r + 1), F t = F u → t ≠ u → IsFixed f i := by
      intro t u hF htu
      have hne : t.val ≠ u.val := by
        intro hvals
        apply htu
        exact Fin.ext hvals
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · -- t.val < u.val
        have h1 : pow f t.val i = some (F t) := F_spec t
        have h2 : pow f u.val i = some (F u) := F_spec u
        have h1' : pow f t.val i = some (F u) := by rw [← hF]; exact h1
        have hadd : t.val + (u.val - t.val) = u.val := by omega
        have hstep : pow f (t.val + (u.val - t.val)) i = pow f (u.val - t.val) (F u) :=
          pow_add_apply h1' (u.val - t.val)
        rw [hadd] at hstep
        have hcycle : pow f (u.val - t.val) (F u) = some (F u) := by
          rw [← hstep]; exact h2
        have hpos : 0 < u.val - t.val := by omega
        have hfixF : IsFixed f (F u) :=
          isFixed_of_pow_self hop hpos hcycle
        have hi : i = F u := eq_of_pow_eq_fixed hinj hfixF h1'
        rw [hi]
        exact hfixF
      · -- u.val < t.val
        have h1 : pow f t.val i = some (F t) := F_spec t
        have h2 : pow f u.val i = some (F u) := F_spec u
        have h2' : pow f u.val i = some (F t) := by rw [hF]; exact h2
        have hadd : u.val + (t.val - u.val) = t.val := by omega
        have hstep : pow f (u.val + (t.val - u.val)) i = pow f (t.val - u.val) (F t) :=
          pow_add_apply h2' (t.val - u.val)
        rw [hadd] at hstep
        have hcycle : pow f (t.val - u.val) (F t) = some (F t) := by
          rw [← hstep]; exact h1
        have hpos : 0 < t.val - u.val := by omega
        have hfixF : IsFixed f (F t) :=
          isFixed_of_pow_self hop hpos hcycle
        have hi : i = F t := eq_of_pow_eq_fixed hinj hfixF h2'
        rw [hi]
        exact hfixF
    -- Therefore `F` is injective.
    have Finj : Function.Injective F := by
      intro t u hF
      by_contra hne
      exact absurd (F_nocoll t u hF hne) h
    -- Pigeonhole: no injection `Fin (r+1) → Fin r`.
    have hcard := Fintype.card_le_of_injective F Finj
    simp only [Fintype.card_fin] at hcard
    omega

/-! ## Lemma 4.1: stable survival -/

/-- **Lemma 4.1 (Stable survival).**
Let `f` be an order-preserving partial injection on `Fin r` and `E` its fixed
set.  For every `n ≥ r`, the `n`-th iterate of `f` is the partial identity on
`E`: it maps each `i ∈ E` to itself and every other position to `none`.  Thus
the events shared by the two interfaces of `P^n` are exactly those represented
by `E`, in their original positions. -/
theorem lemma_4_1 {r : ℕ} (f : PartialInjectiveOrder r) {n : ℕ} (hn : r ≤ n) :
    ∀ i : Fin r,
      PartialMap.pow f.toFun n i = if IsFixed f.toFun i then some i else none := by
  intro i
  by_cases hfix : IsFixed f.toFun i
  · rw [if_pos hfix]
    exact pow_isFixed hfix n
  · rw [if_neg hfix]
    obtain ⟨m, hm, hnone⟩ :=
      exists_pow_none_of_not_isFixed f.orderPreserving f.partialInjective hfix
    exact pow_eq_none_of_eq_none hnone n (le_trans hm hn)

/-- Lemma 4.1, survival half: fixed positions survive every large iterate. -/
theorem lemma_4_1_fixed {r : ℕ} (f : PartialInjectiveOrder r) {n : ℕ} (hn : r ≤ n)
    (i : Fin r) (hi : IsFixed f.toFun i) :
    PartialMap.pow f.toFun n i = some i := by
  rw [lemma_4_1 f hn i]
  exact if_pos hi

/-- Lemma 4.1, survival half on `E`. -/
theorem lemma_4_1_mem_E {r : ℕ} (f : PartialInjectiveOrder r) {n : ℕ} (hn : r ≤ n)
    (i : Fin r) (hi : i ∈ f.E) :
    PartialMap.pow f.toFun n i = some i :=
  lemma_4_1_fixed f hn i hi

/-- Lemma 4.1, death half: nonfixed positions are absent from large iterates. -/
theorem lemma_4_1_not_fixed {r : ℕ} (f : PartialInjectiveOrder r) {n : ℕ} (hn : r ≤ n)
    (i : Fin r) (hi : ¬ IsFixed f.toFun i) :
    PartialMap.pow f.toFun n i = none := by
  rw [lemma_4_1 f hn i]
  exact if_neg hi

/-- Lemma 4.1, death half off `E`. -/
theorem lemma_4_1_not_mem_E {r : ℕ} (f : PartialInjectiveOrder r) {n : ℕ} (hn : r ≤ n)
    (i : Fin r) (hi : i ∉ f.E) :
    PartialMap.pow f.toFun n i = none :=
  lemma_4_1_not_fixed f hn i hi

/-- Lemma 4.1 on the fixed set `E`: `f^n` is the partial identity on `E`. -/
theorem lemma_4_1_on_E {r : ℕ} (f : PartialInjectiveOrder r) {n : ℕ} (hn : r ≤ n) :
    ∀ i : Fin r,
      PartialMap.pow f.toFun n i = if i ∈ f.E then some i else none := by
  intro i
  by_cases hi : i ∈ f.E
  · rw [if_pos hi]
    exact lemma_4_1_mem_E f hn i hi
  · rw [if_neg hi]
    exact lemma_4_1_not_mem_E f hn i hi

/-- Lemma 4.1 in interface language: `f^n` relates positions `i, j` iff both lie
in `E` and `i = j`.  In particular the shared interface of `P^n` is exactly `E`
in its original positions. -/
theorem lemma_4_1_partial_identity {r : ℕ} (f : PartialInjectiveOrder r)
    {n : ℕ} (hn : r ≤ n) (i j : Fin r) :
    PartialMap.pow f.toFun n i = some j ↔ i ∈ f.E ∧ j = i := by
  constructor
  · intro h
    by_cases hi : i ∈ f.E
    · have h1 := lemma_4_1_mem_E f hn i hi
      rw [h1] at h
      exact ⟨hi, Option.some.inj h.symm⟩
    · have h1 := lemma_4_1_not_mem_E f hn i hi
      rw [h1] at h
      exact absurd h (by simp)
  · intro ⟨hi, hj⟩
    rw [hj]
    exact lemma_4_1_mem_E f hn i hi

/-- Lemma 4.1 as stated in the paper: if `r ≤ k` and `n ≥ k` (in particular
`n ≥ r`), then `f_P^n` is the partial identity on `E`. -/
theorem lemma_4_1_stable_survival {r k : ℕ} (f : PartialInjectiveOrder r)
    (hk : r ≤ k) {n : ℕ} (hn : k ≤ n) :
    ∀ i : Fin r,
      PartialMap.pow f.toFun n i = if IsFixed f.toFun i then some i else none :=
  lemma_4_1 f (le_trans hk hn)

/-- Lemma 4.1 for the packaged power `PartialInjectiveOrder.pow`. -/
theorem lemma_4_1_pow_toFun {r : ℕ} (f : PartialInjectiveOrder r) {n : ℕ} (hn : r ≤ n)
    (i : Fin r) :
    (PartialInjectiveOrder.pow f n).toFun i =
      if IsFixed f.toFun i then some i else none :=
  lemma_4_1 f hn i

/-! ## Glued powers: event counting -/

/-- Counting data of an endomorphism `P : U → U` under iterated gluing.
`r = |U|` is the interface size and `d` is the number of new events introduced
by each gluing (`d = |P| - r`).  Gluing `n` copies yields `|P^n| = r + n * d`
events. -/
structure PomCounted where
  /-- Interface size `|U|`. -/
  r : ℕ
  /-- New events per glue, `d = |P| - r`. -/
  d : ℕ

/-- Event-count arithmetic of iterated gluing (alias of `PomCounted`). -/
abbrev GlueCount := PomCounted

namespace PomCounted

/-- Event count of the `n`-th glued power, defined by the gluing recursion
`|P^0| = r` and `|P^{n+1}| = |P^n| + d`. -/
def powCard (P : PomCounted) : ℕ → ℕ
  | 0 => P.r
  | n + 1 => P.powCard n + P.d

@[simp] theorem powCard_zero (P : PomCounted) : P.powCard 0 = P.r := rfl

@[simp] theorem powCard_succ (P : PomCounted) (n : ℕ) :
    P.powCard (n + 1) = P.powCard n + P.d := rfl

/-- Closed form of the glued-power event count: `|P^n| = r + n * d`. -/
theorem powCard_eq (P : PomCounted) (n : ℕ) : P.powCard n = P.r + n * P.d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [powCard_succ, ih]
    ring

/-- A single glue has `r + d = |P|` events. -/
theorem powCard_one (P : PomCounted) : P.powCard 1 = P.r + P.d := by
  rw [powCard_eq]
  ring

/-- The identity endomorphism `id_U` has `d = 0`. -/
def idCounted (r : ℕ) : PomCounted := ⟨r, 0⟩

@[simp] theorem idCounted_d (r : ℕ) : (idCounted r).d = 0 := rfl

/-- At the counting level, `P = id_U` exactly when `|P| = r`, i.e. `d = 0`:
if `|P| = r` both interfaces consist of all events and `P = id_U`, and
conversely. -/
def IsIdentity (P : PomCounted) : Prop := P.d = 0

theorem d_pos_of_ne_id (P : PomCounted) (h : ¬ P.IsIdentity) : 1 ≤ P.d := by
  have : P.d ≠ 0 := by
    intro h0
    exact h h0
  omega

/-- The union of the two interfaces of `P^n` has at most `2r` events. -/
def interfaceBound (P : PomCounted) : ℕ := 2 * P.r

end PomCounted

/-- Counting data of a concrete endomorphism `P : U → U`: `|P|` events, two
interfaces of size `r`, with `r ≤ |P|`. -/
structure CountedEndo where
  /-- Interface size `|U|`. -/
  r : ℕ
  /-- Event count `|P|`. -/
  card : ℕ
  /-- Interfaces embed into the event set. -/
  h_le : r ≤ card

namespace CountedEndo

/-- New events per glue: `d = |P| - r`. -/
def d (P : CountedEndo) : ℕ := P.card - P.r

theorem card_eq (P : CountedEndo) : P.card = P.r + P.d := by
  have h := P.h_le
  simp only [d]
  omega

/-- `P = id_U` at the counting level: every event is an interface event. -/
def IsIdentity (P : CountedEndo) : Prop := P.card = P.r

theorem isIdentity_iff_d_eq_zero (P : CountedEndo) :
    P.IsIdentity ↔ P.d = 0 := by
  simp only [IsIdentity, d]
  have h := P.h_le
  constructor <;> intro h0 <;> omega

theorem d_pos_of_ne_id (P : CountedEndo) (h : ¬ P.IsIdentity) : 1 ≤ P.d := by
  have hd0 : P.d ≠ 0 := fun h0 => h ((isIdentity_iff_d_eq_zero P).2 h0)
  omega

/-- Forget to `PomCounted`. -/
def toPomCounted (P : CountedEndo) : PomCounted := ⟨P.r, P.d⟩

theorem toPomCounted_d (P : CountedEndo) : P.toPomCounted.d = P.d := rfl

theorem powCard_eq (P : CountedEndo) (n : ℕ) :
    P.toPomCounted.powCard n = P.r + n * (P.card - P.r) := by
  rw [PomCounted.powCard_eq]
  rfl

end CountedEndo

/-! ## Lemma 4.2: separation of the boundary cubes -/

/-- **Lemma 4.2 (Separation of the boundary cubes).**
If `P ≠ id_U` then `d = |P| - r ≥ 1`, and for every `n ≥ k + 1` (where `r ≤ k`)
the `n`-th power satisfies `|P^n| = r + n * d > 2r`.  Both interfaces of `P^n`
have `r` events, so their union has at most `2r` events; the inequality exhibits
an event of `P^n` outside the two interfaces, separating the boundary cubes. -/
theorem lemma_4_2 {k : ℕ} (P : PomCounted) (hd : 1 ≤ P.d) (hk : P.r ≤ k)
    {n : ℕ} (hn : k + 1 ≤ n) :
    2 * P.r < P.powCard n := by
  rw [P.powCard_eq]
  have h1 : 2 * P.r < P.r + (k + 1) * P.d := by
    have hk' : P.r + 1 ≤ k + 1 := Nat.succ_le_succ hk
    have hdmul : (k + 1) * 1 ≤ (k + 1) * P.d := Nat.mul_le_mul_left (k + 1) hd
    omega
  have h2 : P.r + (k + 1) * P.d ≤ P.r + n * P.d :=
    Nat.add_le_add_left (Nat.mul_le_mul_right P.d hn) P.r
  omega

/-- Lemma 4.2 packaged with the hypothesis `P ≠ id` on a counted endomorphism:
nonidentity forces `d ≥ 1`. -/
theorem lemma_4_2_of_ne_id {k : ℕ} (P : CountedEndo) (hne : ¬ P.IsIdentity)
    (hk : P.r ≤ k) {n : ℕ} (hn : k + 1 ≤ n) :
    2 * P.r < P.toPomCounted.powCard n := by
  have hd : 1 ≤ P.toPomCounted.d := by
    rw [CountedEndo.toPomCounted_d]
    exact CountedEndo.d_pos_of_ne_id P hne
  exact lemma_4_2 P.toPomCounted hd hk hn

/-- Concrete form of the separation: if the event set of `P^n` has
`|P^n| = r + n d` elements and the two interfaces have at most `r` events each,
then some event lies outside both interfaces. -/
theorem lemma_4_2_exists_outside {k : ℕ} (P : PomCounted) (hd : 1 ≤ P.d)
    (hk : P.r ≤ k) {n : ℕ} (hn : k + 1 ≤ n)
    (E : Type) [Fintype E] [DecidableEq E] (hcard : Fintype.card E = P.powCard n)
    (src tgt : Finset E) (hs : src.card ≤ P.r) (ht : tgt.card ≤ P.r) :
    ∃ e : E, e ∉ src ∧ e ∉ tgt := by
  by_contra! hall
  have hsub : (Finset.univ : Finset E) ⊆ src ∪ tgt := by
    intro e _
    by_cases hes : e ∈ src
    · exact Finset.mem_union_left _ hes
    · exact Finset.mem_union_right _ (hall e hes)
  have hle : Fintype.card E ≤ (src ∪ tgt).card := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card hsub
  have hunion : (src ∪ tgt).card ≤ src.card + tgt.card :=
    Finset.card_union_le src tgt
  have hcount := lemma_4_2 P hd hk hn
  rw [← hcard] at hcount
  omega

/-- Lemma 4.2 in the form of the paper: for `P ≠ id_U` and `n ≥ k + 1`, the
`n`-th power has an event outside its two interfaces. -/
theorem lemma_4_2_separation {k : ℕ} (P : CountedEndo) (hne : ¬ P.IsIdentity)
    (hk : P.r ≤ k) {n : ℕ} (hn : k + 1 ≤ n)
    (E : Type) [Fintype E] [DecidableEq E] (hcard : Fintype.card E = P.toPomCounted.powCard n)
    (src tgt : Finset E) (hs : src.card ≤ P.r) (ht : tgt.card ≤ P.r) :
    ∃ e : E, e ∉ src ∧ e ∉ tgt := by
  have hd : 1 ≤ P.toPomCounted.d := by
    rw [CountedEndo.toPomCounted_d]
    exact CountedEndo.d_pos_of_ne_id P hne
  exact lemma_4_2_exists_outside P.toPomCounted hd hk hn E hcard src tgt hs ht

end CounterFreeHDA
