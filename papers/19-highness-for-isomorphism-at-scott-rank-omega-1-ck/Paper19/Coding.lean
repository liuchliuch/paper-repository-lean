import Paper19.Core
import Mathlib.Data.List.GetD

/-!
# Binary coding of streams and the predicate `R_T` (Section 2)

Code `f ∈ ω^ω` by the binary real
`X_f = 0^{f(0)} 1 0^{f(1)} 1 0^{f(2)} 1 ⋯`,
with decoding bounds `b_f(i) = ∑_{j ≤ i} (f j + 1)`.

Proved here:
* completed blocks are monotone under extension of binary strings;
* `R_T` is monotone under extension;
* `f ∈ [T]` implies `(X_f, b_f) ∈ Q_T` (`isQT_of_path`);
* every member of `Q_T` recovers a path of `T` (`isPath_of_isQT`).
-/

namespace Paper19

open List

/-! ## Trailing open zero-run -/

/-- Length of the unfinished zero-run left open at the end of `η`
when scanned with initial accumulator `z`. -/
def openZeros : Bin → ℕ → ℕ
  | [], z => z
  | true :: rest, _ => openZeros rest 0
  | false :: rest, z => openZeros rest (z + 1)

@[simp] theorem openZeros_nil (z : ℕ) : openZeros [] z = z := rfl

theorem openZeros_cons_true (rest : Bin) (z : ℕ) :
    openZeros (true :: rest) z = openZeros rest 0 := rfl

theorem openZeros_cons_false (rest : Bin) (z : ℕ) :
    openZeros (false :: rest) z = openZeros rest (z + 1) := rfl

theorem openZeros_append (η η' : Bin) (z : ℕ) :
    openZeros (η ++ η') z = openZeros η' (openZeros η z) := by
  induction η generalizing z with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | true => simp [openZeros, ih]
    | false => simp [openZeros, ih]

theorem openZeros_replicate_false (a z : ℕ) :
    openZeros (List.replicate a false) z = z + a := by
  induction a generalizing z with
  | zero => rfl
  | succ n ihn =>
    simp only [List.replicate_succ, openZeros_cons_false]
    rw [ihn]
    omega

/-- Scanning `η ++ η'` from accumulator `z` first closes the blocks of `η`,
then continues on `η'` from the leftover open count. -/
theorem completedBlocksAux_append (η η' : Bin) (z : ℕ) :
    completedBlocksAux (η ++ η') z =
      completedBlocksAux η z ++ completedBlocksAux η' (openZeros η z) := by
  induction η generalizing z with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | true => simp [completedBlocksAux, openZeros, ih]
    | false => simp [completedBlocksAux, openZeros, ih]

theorem completedBlocks_append (η η' : Bin) :
    completedBlocks (η ++ η') =
      completedBlocks η ++ completedBlocksAux η' (openZeros η 0) := by
  simpa [completedBlocks] using completedBlocksAux_append η η' 0

/-- Completed blocks of a prefix form a prefix of completed blocks of the extension. -/
theorem completedBlocks_prefix {η η' : Bin} (h : η <+: η') :
    completedBlocks η <+: completedBlocks η' := by
  obtain ⟨rest, rfl⟩ := h
  rw [completedBlocks_append]
  exact prefix_append _ _

theorem completedBlocks_mono {η η' : Bin} (h : η <+: η') :
    (completedBlocks η).length ≤ (completedBlocks η').length :=
  (completedBlocks_prefix h).length_le

/-- Once enough blocks are completed in `η`, extending does not change
the first `i + 1` completed blocks. -/
theorem completedBlocks_take_mono {η η' : Bin} (h : η <+: η') (i : ℕ)
    (hlen : i + 1 ≤ (completedBlocks η).length) :
    (completedBlocks η).take (i + 1) = (completedBlocks η').take (i + 1) := by
  have hp := completedBlocks_prefix h
  have hpf : completedBlocks η = (completedBlocks η').take (completedBlocks η).length :=
    prefix_iff_eq_take.mp hp
  calc (completedBlocks η).take (i + 1)
      = ((completedBlocks η').take (completedBlocks η).length).take (i + 1) := by rw [← hpf]
    _ = (completedBlocks η').take (min (completedBlocks η).length (i + 1)) := by
      rw [take_take, Nat.min_comm]
    _ = (completedBlocks η').take (i + 1) := by rw [min_eq_right hlen]

/-- `R_T` remains true when the binary string is extended. -/
theorem RT.monotone {T : Tree} {η η' : Bin} (h : η <+: η') {i : ℕ}
    (hRT : RT T η i) : RT T η' i := by
  refine ⟨?_, ?_⟩
  · exact le_trans hRT.1 (completedBlocks_mono h)
  · rw [← completedBlocks_take_mono h i hRT.1]
    exact hRT.2

/-! ## The block string `0^{a_0} 1 ⋯ 0^{a_k} 1` -/

/-- `codeOf as` is the binary string `0^{as 0} 1 0^{as 1} 1 ⋯`. -/
def codeOf : List ℕ → Bin
  | [] => []
  | a :: rest => List.replicate a false ++ true :: codeOf rest

@[simp] theorem codeOf_nil : codeOf [] = [] := rfl

theorem codeOf_cons (a : ℕ) (rest : List ℕ) :
    codeOf (a :: rest) = List.replicate a false ++ true :: codeOf rest := rfl

theorem codeOf_singleton (a : ℕ) : codeOf [a] = List.replicate a false ++ [true] := by
  simp [codeOf]

theorem completedBlocksAux_replicate_false (a z : ℕ) :
    completedBlocksAux (List.replicate a false) z = [] := by
  induction a generalizing z with
  | zero => rfl
  | succ n ihn =>
    have h := ihn (z + 1)
    simpa [List.replicate_succ, completedBlocksAux] using h

theorem completedBlocks_replicate_false (a : ℕ) :
    completedBlocks (List.replicate a false) = [] :=
  completedBlocksAux_replicate_false a 0

theorem completedBlocksAux_cons_true (rest : Bin) (z : ℕ) :
    completedBlocksAux (true :: rest) z = z :: completedBlocksAux rest 0 := rfl

theorem completedBlocksAux_codeOf_zero (as : List ℕ) :
    completedBlocksAux (codeOf as) 0 = as := by
  induction as with
  | nil => rfl
  | cons a rest ih =>
    rw [codeOf_cons, completedBlocksAux_append, completedBlocksAux_replicate_false,
      completedBlocksAux_cons_true, openZeros_replicate_false]
    simp [ih]

/-- Completed blocks of `codeOf as` are exactly `as`. -/
theorem completedBlocks_codeOf (as : List ℕ) :
    completedBlocks (codeOf as) = as :=
  completedBlocksAux_codeOf_zero as

/-! ## Delimiter positions of `decodeBoundOf` / `binaryOf` -/

theorem decodeBoundOf_succ_lt (f : Stream) (i : ℕ) :
    decodeBoundOf f i < decodeBoundOf f (i + 1) := by
  rw [decodeBoundOf_succ]
  omega

theorem decodeBoundOf_lt_self (f : Stream) (i : ℕ) : i < decodeBoundOf f i := by
  induction i with
  | zero => simp [decodeBoundOf_zero]
  | succ i ih => rw [decodeBoundOf_succ]; omega

theorem decodeBoundOf_add_le (f : Stream) (i d : ℕ) :
    decodeBoundOf f i ≤ decodeBoundOf f (i + d) := by
  induction d with
  | zero => exact le_rfl
  | succ d ihn =>
    have hlt := decodeBoundOf_succ_lt f (i + d)
    have h3 : i + (d + 1) = i + d + 1 := by omega
    rw [h3]
    exact ihn.trans (le_of_lt hlt)

theorem decodeBoundOf_le_of_le (f : Stream) {i j : ℕ} (hij : i ≤ j) :
    decodeBoundOf f i ≤ decodeBoundOf f j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact decodeBoundOf_add_le f i d

theorem binaryOf_iff (f : Stream) (k : ℕ) :
    binaryOf f k = true ↔ ∃ j ≤ k, k + 1 = decodeBoundOf f j := by
  simp [binaryOf]

/-- The first `decodeBoundOf f i` bits of `X_f` form exactly
`0^{f 0} 1 ⋯ 0^{f i} 1`.

This is the key combinatorial identity of the coding; the proof unfolds the
delimiter positions of `binaryOf` against the recursive definition of `codeOf`.
-/
theorem binaryPrefix_codeOf (f : Stream) (i : ℕ) :
    List.ofFn (fun k : Fin (decodeBoundOf f i) => binaryOf f k)
      = codeOf (List.ofFn (fun j : Fin (i + 1) => f j)) := by
  induction i with
  | zero =>
    have hlen : decodeBoundOf f 0 = f 0 + 1 := decodeBoundOf_zero f
    have hcode : (List.ofFn fun j : Fin 1 => f j) = [f 0] := by simp
    rw [hlen, hcode, codeOf_singleton]
    apply List.ext_getElem
    · simp [List.length_ofFn, List.length_replicate, List.length_cons, List.length_nil]
    · intro k hk1 hk2
      by_cases hk : k < f 0
      · have hbf : binaryOf f k = false := by
          have hiff := binaryOf_iff f k
          apply Bool.eq_false_of_not_eq_true
          intro htrue
          have hex := hiff.1 htrue
          rcases hex with ⟨j, hj, heq⟩
          -- k+1 = decodeBoundOf f j ≥ j+1 and j ≤ k < f 0, so decodeBoundOf f j ≤ f 0
          have hge := decodeBoundOf_le_of_le f (show 0 ≤ j by omega)
          rw [decodeBoundOf_zero] at hge
          omega
        have hget : (List.replicate (f 0) false ++ [true])[k] = false := by
          have hk2' : k < (List.replicate (f 0) false).length := by
            simp [List.length_replicate]; omega
          rw [List.getElem_append_left hk2']
          simp [List.getElem_replicate, hk]
        rw [List.getElem_ofFn, hbf, hget]
      · have hk : k = f 0 := by
          have hlen2 : (List.replicate (f 0) false ++ [true]).length = f 0 + 1 := by simp
          have hklt : k < f 0 + 1 := by
            have : k < decodeBoundOf f 0 := by simpa using hk2
            rwa [hlen] at this
          omega
        have hbf : binaryOf f k = true := by
          rw [binaryOf_iff]
          exact ⟨0, by omega, by rw [decodeBoundOf_zero]; omega⟩
        have hget : (List.replicate (f 0) false ++ [true])[k] = true := by
          have hle : (List.replicate (f 0) false).length ≤ k := by
            simp [List.length_replicate]; omega
          rw [List.getElem_append_right hle]
          simp [hk]
        rw [List.getElem_ofFn, hbf, hget]
  | succ i ih =>
    have hc : ∀ a b : List ℕ, codeOf (a ++ b) = codeOf a ++ codeOf b := by
      intro a b
      induction a with
      | nil => rfl
      | cons x xs ih => simp [codeOf, ih, List.append_assoc]
    have hs : List.ofFn (fun j : Fin (i + 1 + 1) => f j) =
        List.ofFn (fun j : Fin (i + 1) => f j) ++ [f (i + 1)] := by
      simpa using List.ofFn_succ' (fun j : Fin (i + 1 + 1) => f j)
    rw [hs, hc, codeOf_singleton, ← ih]
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_append, List.length_replicate,
        List.length_singleton]
      exact decodeBoundOf_succ f i
    · intro k hk hk'
      rw [List.getElem_ofFn]
      by_cases hki : k < decodeBoundOf f i
      · rw [List.getElem_append_left (by simpa using hki), List.getElem_ofFn]
      · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hki)]
        simp only [List.length_ofFn]
        have hpos : decodeBoundOf f i ≤ k := Nat.le_of_not_gt hki
        have hkmax : k ≤ decodeBoundOf f i + f (i + 1) := by
          simp only [List.length_ofFn] at hk
          rw [decodeBoundOf_succ] at hk; omega
        by_cases hlast : k = decodeBoundOf f i + f (i + 1)
        · have ht : binaryOf f k = true := by
            rw [binaryOf_iff]
            refine ⟨i + 1, ?_, ?_⟩
            · have := decodeBoundOf_lt_self f i; omega
            · rw [decodeBoundOf_succ]; omega
          rw [ht, List.getElem_append_right (by simp; omega)]
          simp [hlast]
        · have hf : binaryOf f k = false := by
            apply Bool.eq_false_of_not_eq_true
            rw [binaryOf_iff]
            rintro ⟨j, hj, heq⟩
            by_cases hji : j ≤ i
            · have := decodeBoundOf_le_of_le f hji; omega
            · have := decodeBoundOf_le_of_le f (show i + 1 ≤ j by omega)
              rw [decodeBoundOf_succ] at this; omega
          rw [hf, List.getElem_append_left (by simp; omega)]
          simp

theorem completedBlocks_binaryPrefix (f : Stream) (i : ℕ) :
    completedBlocks (List.ofFn (fun k : Fin (decodeBoundOf f i) => binaryOf f k))
      = List.ofFn (fun j : Fin (i + 1) => f j) := by
  rw [binaryPrefix_codeOf, completedBlocks_codeOf]

theorem completedBlocks_binaryPrefix_length (f : Stream) (i : ℕ) :
    (completedBlocks (List.ofFn (fun k : Fin (decodeBoundOf f i) => binaryOf f k))).length
      = i + 1 := by
  rw [completedBlocks_binaryPrefix, List.length_ofFn]

theorem completedBlocks_binaryPrefix_take (f : Stream) (i : ℕ) :
    (completedBlocks (List.ofFn (fun k : Fin (decodeBoundOf f i) => binaryOf f k))).take (i + 1)
      = List.ofFn (fun j : Fin (i + 1) => f j) := by
  rw [completedBlocks_binaryPrefix]
  exact take_of_length_le (by simp)

/-! ## `f ∈ [T]` implies `(X_f, b_f) ∈ Q_T` -/

/-- Lemma 2, path conversion (forward): from `f ∈ [T]`, the pair
`(X_f, b_f)` lies in `Q_T`. -/
theorem isQT_of_path (T : Tree) (f : Stream) (hf : Tree.IsPath T f) :
    IsQT T (binaryOf f) (decodeBoundOf f) := by
  intro i
  refine ⟨?_, ?_⟩
  · rw [completedBlocks_binaryPrefix_length]
  · rw [completedBlocks_binaryPrefix_take]
    exact hf (i + 1)

/-! ## Agreement of completed blocks across prefixes of one stream -/

/-- Shorter prefixes of a stream are prefixes of longer ones. -/
theorem ofFn_isPrefix {X : ℕ → Bool} {b B : ℕ} (h : b ≤ B) :
    List.ofFn (fun k : Fin b => X k) <+: List.ofFn (fun k : Fin B => X k) := by
  have heq : List.ofFn (fun k : Fin b => X k)
      = (List.ofFn (fun k : Fin B => X k)).take b := by
    apply List.ext_get
    · simp [List.length_ofFn, List.length_take, h]
    · intro n hn hn'
      simp [List.getElem_take, List.getElem_ofFn]
  rw [heq]
  exact List.take_prefix _ _

/-- Two prefixes of the same stream that each contain at least `n+1` completed
blocks share the same first `n+1` completed blocks, by extending both to a
common bound and applying monotonicity. -/
theorem completedBlocks_take_agree {X : ℕ → Bool} {b₁ b₂ n : ℕ}
    (h1 : n + 1 ≤ (completedBlocks (List.ofFn (fun k : Fin b₁ => X k))).length)
    (h2 : n + 1 ≤ (completedBlocks (List.ofFn (fun k : Fin b₂ => X k))).length) :
    (completedBlocks (List.ofFn (fun k : Fin b₁ => X k))).take (n + 1)
      = (completedBlocks (List.ofFn (fun k : Fin b₂ => X k))).take (n + 1) := by
  set B := max b₁ b₂
  have p1 : (List.ofFn (fun k : Fin b₁ => X k)) <+: (List.ofFn (fun k : Fin B => X k)) :=
    ofFn_isPrefix (le_max_left b₁ b₂)
  have p2 : (List.ofFn (fun k : Fin b₂ => X k)) <+: (List.ofFn (fun k : Fin B => X k)) :=
    ofFn_isPrefix (le_max_right b₁ b₂)
  have t1 := completedBlocks_take_mono p1 n h1
  have t2 := completedBlocks_take_mono p2 n h2
  rw [t1, t2]

theorem completedBlocks_getElem_agree {X : ℕ → Bool} {b₁ b₂ n : ℕ}
    (h1 : n + 1 ≤ (completedBlocks (List.ofFn (fun k : Fin b₁ => X k))).length)
    (h2 : n + 1 ≤ (completedBlocks (List.ofFn (fun k : Fin b₂ => X k))).length) :
    (completedBlocks (List.ofFn (fun k : Fin b₁ => X k))).getD n 0
      = (completedBlocks (List.ofFn (fun k : Fin b₂ => X k))).getD n 0 := by
  -- Both prefixes share a common extension of the ambient stream `X`.
  -- `completedBlocks_take_agree` identifies the first `n+1` blocks of the two
  -- completed-block lists; the `n`-th entries therefore agree.
  have htake := completedBlocks_take_agree h1 h2
  -- getD on an in-range index equals that entry of the take of length n+1
  have g1 : (completedBlocks (List.ofFn (fun k : Fin b₁ => X k))).getD n 0
      = ((completedBlocks (List.ofFn (fun k : Fin b₁ => X k))).take (n + 1)).getD n 0 := by
    have l1 : n < (completedBlocks (List.ofFn (fun k : Fin b₁ => X k))).length := by omega
    have hlt : n < ((completedBlocks (List.ofFn (fun k : Fin b₁ => X k))).take (n + 1)).length := by
      have hlen := List.length_take (i := n + 1) (l := completedBlocks (List.ofFn (fun k : Fin b₁ => X k)))
      omega
    conv_lhs => rw [List.getD_eq_getElem _ 0 l1]
    conv_rhs => rw [List.getD_eq_getElem _ 0 hlt]
    rw [List.getElem_take]
  have g2 : (completedBlocks (List.ofFn (fun k : Fin b₂ => X k))).getD n 0
      = ((completedBlocks (List.ofFn (fun k : Fin b₂ => X k))).take (n + 1)).getD n 0 := by
    have l2 : n < (completedBlocks (List.ofFn (fun k : Fin b₂ => X k))).length := by omega
    have hlt : n < ((completedBlocks (List.ofFn (fun k : Fin b₂ => X k))).take (n + 1)).length := by
      have hlen := List.length_take (i := n + 1) (l := completedBlocks (List.ofFn (fun k : Fin b₂ => X k)))
      omega
    conv_lhs => rw [List.getD_eq_getElem _ 0 l2]
    conv_rhs => rw [List.getD_eq_getElem _ 0 hlt]
    rw [List.getElem_take]
  calc (completedBlocks (List.ofFn (fun k : Fin b₁ => X k))).getD n 0
      = ((completedBlocks (List.ofFn (fun k : Fin b₁ => X k))).take (n + 1)).getD n 0 := g1
    _ = ((completedBlocks (List.ofFn (fun k : Fin b₂ => X k))).take (n + 1)).getD n 0 := by
        rw [htake]
    _ = (completedBlocks (List.ofFn (fun k : Fin b₂ => X k))).getD n 0 := g2.symm

/-- Bound-aware block extraction: the `n`-th completed block of `X ↾ bound`. -/
def blockOfPrefix (X : ℕ → Bool) (bound n : ℕ) : ℕ :=
  (completedBlocks (List.ofFn (fun k : Fin bound => X k))).getD n 0

theorem blockOfPrefix_agree {X : ℕ → Bool} {b₁ b₂ n : ℕ}
    (h1 : n + 1 ≤ (completedBlocks (List.ofFn (fun k : Fin b₁ => X k))).length)
    (h2 : n + 1 ≤ (completedBlocks (List.ofFn (fun k : Fin b₂ => X k))).length) :
    blockOfPrefix X b₁ n = blockOfPrefix X b₂ n := by
  unfold blockOfPrefix
  exact completedBlocks_getElem_agree h1 h2

/-! ## Recovering a path from `Q_T` -/

/-- Lemma 2, path conversion (backward): from a member of `Q_T` one recovers
a path of `T`.  The hypothesis `∀ i, i ≤ b i` is kept to match
`Spec.Lemma2_PathConversions`; the argument does not use it. -/
theorem isPath_of_isQT {T : Tree} {X : ℕ → Bool} {b : Stream}
    (h : IsQT T X b) (_hb : ∀ i, i ≤ b i) :
    Tree.IsPath T (pathOfQT X b) := by
  intro m
  cases m with
  | zero => exact T.mem_nil
  | succ m =>
    -- From `IsQT` at `m`: the first `m+1` completed blocks of `X ↾ b m`
    -- form a node of `T`.  Those blocks are exactly `pathOfQT X b 0 … m`
    -- by `blockOfPrefix_agree`, so the level-`m+1` node of `pathOfQT` lies in `T`.
    have hRT := h m
    have hmem : T.mem ((completedBlocks (List.ofFn (fun k : Fin (b m) => X k))).take (m + 1)) :=
      hRT.2
    have key :
        List.ofFn (fun j : Fin (m + 1) => pathOfQT X b j)
          = (completedBlocks (List.ofFn (fun k : Fin (b m) => X k))).take (m + 1) := by
      have hlen_eq : (List.ofFn fun j : Fin (m + 1) => pathOfQT X b j).length = m + 1 := by
        simp
      have hRTm := h m
      have hlen_blocks : m + 1 ≤ (completedBlocks (List.ofFn fun k : Fin (b m) => X k)).length :=
        hRTm.1
      apply List.ext_getElem
      · rw [hlen_eq, List.length_take]
        omega
      · intro j hj1 hj2
        have hj : j < m + 1 := by omega
        have hRTj := h j
        have hlen_j : j + 1 ≤ (completedBlocks (List.ofFn fun k : Fin (b j) => X k)).length :=
          hRTj.1
        have hlen_m : j + 1 ≤ (completedBlocks (List.ofFn fun k : Fin (b m) => X k)).length := by
          omega
        have hagree := blockOfPrefix_agree hlen_j hlen_m
        simp only [blockOfPrefix] at hagree
        have hlt_j : j < (completedBlocks (List.ofFn fun k : Fin (b j) => X k)).length := by omega
        have hlt_m : j < (completedBlocks (List.ofFn fun k : Fin (b m) => X k)).length := by omega
        -- Convert getD to getElem on both sides of hagree
        have hagree' :
            (completedBlocks (List.ofFn fun k : Fin (b j) => X k))[j]
              = (completedBlocks (List.ofFn fun k : Fin (b m) => X k))[j] := by
          have e1 := List.getD_eq_getElem _ (0 : ℕ) hlt_j
          have e2 := List.getD_eq_getElem _ (0 : ℕ) hlt_m
          rw [← e1, ← e2]
          exact hagree
        have hL : (List.ofFn fun j : Fin (m + 1) => pathOfQT X b j)[j] = pathOfQT X b j := by
          rw [List.getElem_ofFn]
        have hR : ((completedBlocks (List.ofFn fun k : Fin (b m) => X k)).take (m + 1))[j]
            = (completedBlocks (List.ofFn fun k : Fin (b m) => X k))[j] := by
          simp [List.getElem_take]
        rw [hL, hR]
        show (completedBlocks (List.ofFn fun k : Fin (b j) => X k)).getD j 0 = _
        rw [List.getD_eq_getElem _ (0 : ℕ) hlt_j]
        exact hagree'
    rw [key]
    exact hmem

/-- The coordinate coding in equation (1). -/
def pairStream (X : ℕ → Bool) (b : Stream) : Stream :=
  fun i => 2 * b i + if X i then 1 else 0

def streamBits (g : Stream) : ℕ → Bool := fun i => decide (g i % 2 = 1)
def streamBounds (g : Stream) : Stream := fun i => g i / 2

@[simp] theorem bits_prefix (g : Stream) (m : ℕ) (i : Fin m) :
    bitsOf (List.ofFn (fun j : Fin m => g j)) ⟨i, by simp⟩ = streamBits g i := by
  simp [bitsOf, streamBits]

@[simp] theorem bounds_prefix (g : Stream) (m : ℕ) (i : Fin m) :
    quotsOf (List.ofFn (fun j : Fin m => g j)) ⟨i, by simp⟩ = streamBounds g i := by
  simp [quotsOf, streamBounds]

@[simp] theorem streamBits_pair (X : ℕ → Bool) (b : Stream) :
    streamBits (pairStream X b) = X := by
  funext i
  cases hx : X i <;> simp [streamBits, pairStream, hx] <;> omega

@[simp] theorem streamBounds_pair (X : ℕ → Bool) (b : Stream) :
    streamBounds (pairStream X b) = b := by
  funext i
  cases hx : X i <;> simp [streamBounds, pairStream, hx] <;> omega

theorem bitPrefix_stream (g : Stream) {q m : ℕ} (h : q ≤ m) :
    bitPrefix (List.ofFn (fun j : Fin m => g j)) q =
      List.ofFn (fun j : Fin q => streamBits g j) := by
  rw [bitPrefix_of_le (by simpa using h)]
  simp [bitsOf, streamBits]

theorem isQT_of_STree_path {T : Tree} {g : Stream}
    (hg : (STree T).IsPath g) : IsQT T (streamBits g) (streamBounds g) := by
  intro i
  let m := max (i + 1) (streamBounds g i)
  have hi : i < m := by dsimp [m]; omega
  have hbound : streamBounds g i ≤ m := le_max_right _ _
  have h := hg m ⟨i, by simpa using hi⟩
  simp only [quotsOf, List.get_eq_getElem, List.getElem_ofFn, List.length_ofFn] at h
  change streamBounds g i ≤ m → _ at h
  have h := h hbound
  change RT T (bitPrefix (List.ofFn (fun j : Fin m => g j)) (streamBounds g i)) i at h
  rwa [bitPrefix_stream g hbound] at h

theorem STree_path_of_isQT {T : Tree} {g : Stream}
    (hg : IsQT T (streamBits g) (streamBounds g)) : (STree T).IsPath g := by
  intro m i hi
  have hi' : i.val < m := by simpa using i.is_lt
  have hb : streamBounds g i.val ≤ m := by simpa [quotsOf, streamBounds] using hi
  simp only [quotsOf, List.get_eq_getElem, List.getElem_ofFn]
  change RT T (bitPrefix (List.ofFn (fun j : Fin m => g j)) (streamBounds g i.val)) i.val
  rw [bitPrefix_stream g hb]
  exact hg i.val

theorem pairStream_path {T : Tree} {X : ℕ → Bool} {b : Stream}
    (h : IsQT T X b) : (STree T).IsPath (pairStream X b) :=
  STree_path_of_isQT (by simpa using h)

theorem completedBlocksAux_length_le (η : Bin) (z : ℕ) :
    (completedBlocksAux η z).length ≤ η.length := by
  induction η generalizing z with
  | nil => simp [completedBlocksAux]
  | cons b η ih =>
    have h0 := ih 0
    have h1 := ih (z + 1)
    cases b <;> simp only [completedBlocksAux, List.length_cons] <;> omega

theorem IsQT.bound {T : Tree} {X : ℕ → Bool} {b : Stream} (h : IsQT T X b) (i : ℕ) :
    i ≤ b i := by
  have h1 := (h i).1
  have h2 := completedBlocksAux_length_le (List.ofFn (fun j : Fin (b i) => X j)) 0
  simp only [completedBlocks, List.length_ofFn] at h1 h2
  omega

theorem path_to_STree {T : Tree} {f : Stream} (hf : T.IsPath f) :
    (STree T).IsPath (pairStream (binaryOf f) (decodeBoundOf f)) :=
  pairStream_path (isQT_of_path T f hf)

theorem path_from_STree {T : Tree} {g : Stream} (hg : (STree T).IsPath g) :
    T.IsPath (pathOfQT (streamBits g) (streamBounds g)) :=
  isPath_of_isQT (isQT_of_STree_path hg) (isQT_of_STree_path hg).bound

end Paper19
