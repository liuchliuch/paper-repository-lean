import Paper08.LowDegreeProgram
import Paper08.SchoolbookArithmetic
import Mathlib.Data.List.Sort

/-! # Discrete bit work of the degree-one algorithm

Charges are derived from the actual finite sets and coordinate keys. Sorting
has a source-level mergesort trace, bounded uniformly for every list
representation of the finite set; no quotient representative is chosen by the
algorithm. The finite-set charge is a deliberately loose, permutation-invariant
envelope for that trace. Graph, incidence, assignment and coordinate charges
are sums over the actual loops.
-/
open scoped BigOperators
namespace Paper08.LowDegreeDiscreteCost
open Paper08 LowDegreeAlgorithm PrimitiveProgram

/-- Read a finite coordinate key, including its list cells and integer bits. -/
def keyBits (l : List ℕ) : ℕ := l.length + (l.map Nat.size).sum + 1

def compareBits {α : Type*} (key : α → List ℕ) (a b : α) : ℕ :=
  keyBits (key a) + keyBits (key b) + 1

/-- The exact branch-dependent merge recursion, with a charge for the actual
comparison keys and each list cell visited. -/
def mergeWork {α : Type*} (key : α → List ℕ) (le : α → α → Bool) : List α → List α → ℕ
  | [], ys => ys.length + 1
  | xs, [] => xs.length + 1
  | x :: xs, y :: ys => compareBits key x y + 1 +
      if le x y then mergeWork key le xs (y :: ys) else mergeWork key le (x :: xs) ys
termination_by xs ys => xs.length + ys.length

lemma mergeWork_le {α : Type*} (key : α → List ℕ) (le : α → α → Bool)
    (xs ys : List α) (K : ℕ)
    (hK : ∀ x ∈ xs, ∀ y ∈ ys, compareBits key x y ≤ K) :
    mergeWork key le xs ys ≤ (xs.length + ys.length) * (K + 1) + 1 := by
  induction xs generalizing ys with
  | nil => simp [mergeWork] <;> nlinarith
  | cons x xs ihx =>
    induction ys with
    | nil => simp [mergeWork] <;> nlinarith
    | cons y ys ihy =>
      have hxy := hK x (by simp) y (by simp)
      simp only [mergeWork, List.length_cons]
      split
      · have hh := ihx (y :: ys) (fun a ha b hb => hK a (by simp [ha]) b hb)
        simp only [List.length_cons] at hh
        nlinarith
      · have hh := ihy (fun a ha b hb => hK a ha b (by simp [hb]))
        simp only [List.length_cons] at hh
        nlinarith

/-- Mergesort recursion with exactly the same contiguous split sizes as the
source `List.mergeSort`, including split/list traversal work. -/
def sortWork {α : Type*} (key : α → List ℕ) (le : α → α → Bool) : List α → ℕ
  | [] => 0
  | [_] => 1
  | a :: b :: xs =>
      let l := a :: b :: xs
      let k := (l.length + 1) / 2
      let left := l.take k
      let right := l.drop k
      sortWork key le left + sortWork key le right +
        mergeWork key le (left.mergeSort le) (right.mergeSort le) + l.length + 1
termination_by l => l.length
decreasing_by all_goals simp only [List.length_take, List.length_drop, List.length_cons]; omega

lemma sortWork_le {α : Type*} (key : α → List ℕ) (le : α → α → Bool)
    (l : List α) (K : ℕ) (hK : ∀ x ∈ l, ∀ y ∈ l, compareBits key x y ≤ K) :
    sortWork key le l ≤ l.length ^ 2 * (K + 5) := by
  cases l with
  | nil => simp [sortWork]
  | cons a l =>
    cases l with
    | nil => simp [sortWork]
    | cons b xs =>
      let l := a :: b :: xs
      let k := (l.length + 1) / 2
      let left := l.take k
      let right := l.drop k
      have hleft : left.length < l.length := by dsimp [left, k, l]; simp; omega
      have hright : right.length < l.length := by dsimp [right, k, l]; simp
      have hlpos : 1 ≤ left.length := by dsimp [left, k, l]; simp; omega
      have hrpos : 1 ≤ right.length := by dsimp [right, k, l]; simp; omega
      have hlen : left.length + right.length = l.length := by
        dsimp [left, right]; simp; omega
      have hls : ∀ x ∈ left, x ∈ l := fun x hx => List.mem_of_mem_take hx
      have hrs : ∀ x ∈ right, x ∈ l := fun x hx => List.mem_of_mem_drop hx
      have hl := sortWork_le key le left K (fun x hx y hy => hK x (hls x hx) y (hls y hy))
      have hr := sortWork_le key le right K (fun x hx y hy => hK x (hrs x hx) y (hrs y hy))
      have hm := mergeWork_le key le (left.mergeSort le) (right.mergeSort le) K (by
        intro x hx y hy
        exact hK x (hls x (List.mem_mergeSort.mp hx)) y (hrs y (List.mem_mergeSort.mp hy)))
      simp only [List.length_mergeSort] at hm
      have hcross : left.length + right.length ≤ 2 * left.length * right.length := by
        have ha := Nat.mul_le_mul_left left.length hrpos
        have hb := Nat.mul_le_mul_right right.length hlpos
        nlinarith
      have hcross' := Nat.mul_le_mul_right (K + 5) hcross
      rw [sortWork]
      change sortWork key le left + sortWork key le right +
        mergeWork key le (left.mergeSort le) (right.mergeSort le) + l.length + 1 ≤ _
      change _ ≤ l.length ^ 2 * (K + 5)
      rw [← hlen]
      rw [← hlen] at *
      nlinarith
  
termination_by l.length
decreasing_by all_goals (simp_all [List.length_take, List.length_drop] <;> omega)

/-- Finite-set source sorting charge: all pairs of actual items scan the
actual key-bit sum. It bounds source mergesort for every representative. -/
def sortCharge {α : Type*} (S : Finset α) (key : α → List ℕ) : ℕ :=
  ∑ _a ∈ S, ∑ _b ∈ S, (2 * (∑ x ∈ S, keyBits (key x)) + 6)

lemma sortCharge_eq {α : Type*} (S : Finset α) (key : α → List ℕ) :
    sortCharge S key = S.card ^ 2 * (2 * (∑ x ∈ S, keyBits (key x)) + 6) := by
  simp [sortCharge]
  ring

lemma sortCharge_le {α : Type*} (S : Finset α) (key : α → List ℕ) {D : ℕ}
    (hD : ∀ x ∈ S, keyBits (key x) ≤ D) :
    sortCharge S key ≤ S.card ^ 2 * (2 * (S.card * D) + 6) := by
  rw [sortCharge_eq]
  apply Nat.mul_le_mul_left
  have hh := Finset.sum_le_sum hD
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  simp only [Nat.cast_id] at hh
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hh) 6

/-- The source-level sort trace is bounded independently of the order of the
input representation; this connects the charge to genuine comparison work. -/
theorem source_sort_le_charge {α : Type*} [DecidableEq α] (S : Finset α)
    (key : α → List ℕ) (le : α → α → Bool) (l : List α)
    (hnodup : l.Nodup) (hS : l.toFinset = S) : sortWork key le l ≤ sortCharge S key := by
  let D := ∑ x ∈ S, keyBits (key x)
  have hkey : ∀ x ∈ l, keyBits (key x) ≤ D := by
    intro x hx
    apply Finset.single_le_sum (fun y _ => Nat.zero_le _) (show x ∈ S by rw [← hS]; simpa using hx)
  have hc : ∀ x ∈ l, ∀ y ∈ l, compareBits key x y ≤ 2 * D + 1 := by
    intro x hx y hy
    have hx' := hkey x hx
    have hy' := hkey y hy
    dsimp [compareBits]
    omega
  have hh := sortWork_le key le l (2 * D + 1) hc
  have hlen : l.length = S.card := by rw [← hS, List.toFinset_card_of_nodup hnodup]
  simpa only [hlen, sortCharge_eq, D, Nat.add_assoc, show 1 + 5 = 6 from rfl] using hh

def indexKey {n : ℕ} (v : Fin n) : List ℕ := [v.val]

def gridKey {n : ℕ} (d : Fin n → ℕ) (z : CellGrid.Grid d) : List ℕ :=
  List.ofFn (fun v => (z v).val)

lemma index_size_le {n : ℕ} (v : Fin n) : v.val.size ≤ n :=
  Nat.size_le.mpr (v.isLt.trans (Nat.lt_two_pow_self (n := n)))

lemma indexKey_bits_le {n : ℕ} (v : Fin n) : keyBits (indexKey v) ≤ n + 2 := by
  have h := index_size_le v
  simp [indexKey, keyBits]
  omega

lemma keyBits_ofFn_le {n D : ℕ} (f : Fin n → ℕ) (hf : ∀ v, (f v).size ≤ D) :
    keyBits (List.ofFn f) ≤ n * (D + 1) + 1 := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hf v)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  simp only [keyBits, List.length_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  simp only [Nat.cast_id] at hh
  nlinarith

lemma finsetKey_bits_le {n : ℕ} (C : Finset (Fin n)) : keyBits (finsetKey C) ≤ 2 * n + 1 := by
  have hh := keyBits_ofFn_le (fun v : Fin n => if v ∈ C then 1 else 0) (D := 1) (by
    intro v
    dsimp only
    split_ifs <;> exact Nat.size_le.mpr (by norm_num))
  simpa [finsetKey, Nat.mul_comm] using hh

lemma gridKey_bits_le {n L : ℕ} (C : Finset (Fin n)) (z : CellGrid.Grid (levels C L)) :
    keyBits (gridKey (levels C L) z) ≤ n * (L + 1) + 1 := by
  apply keyBits_ofFn_le
  intro v
  apply Nat.size_le.mpr
  exact (z v).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by
    unfold levels
    split_ifs <;> omega))

/-- Full incidence scan of the actual stored scope, with actual label bits. -/
def incidenceWork {n : ℕ} (S : Finset (Fin n)) (v : Fin n) : ℕ :=
  ∑ w ∈ S, (w.val.size + v.val.size + 2)

lemma incidenceWork_le {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    incidenceWork S v ≤ S.card * (2 * n + 2) := by
  unfold incidenceWork
  calc
    _ ≤ ∑ _w ∈ S, (2 * n + 2) := Finset.sum_le_sum (fun w _ => by
      have hw := index_size_le w
      have hv := index_size_le v
      omega)
    _ = _ := by simp

/-- The naive graph constructor scans every actual vertex pair and factor.
The two scope tests at each occurrence are both charged, even if one fails. -/
def graphWork {n r m : ℕ} (E : FactorFamily n r m) : ℕ :=
  ∑ u : Fin n, ∑ v : Fin n,
    (u.val.size + v.val.size + 2 +
      ∑ e : Fin m, (incidenceWork (E e).scope u + incidenceWork (E e).scope v + 2))

theorem graphWork_le {n r m : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) :
    graphWork E ≤ n ^ 2 * (2 * n + 2 + m * (8 * n + 10)) := by
  have hs (e : Fin m) (v : Fin n) : incidenceWork (E e).scope v ≤ 4 * n + 4 := by
    have hh := (incidenceWork_le (E e).scope v).trans
      (Nat.mul_le_mul_right (2 * n + 2) (lowDegree_scope_card_le E hdeg e))
    nlinarith
  unfold graphWork
  calc
    _ ≤ ∑ _u : Fin n, ∑ _v : Fin n, (2 * n + 2 + m * (8 * n + 10)) := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun e _ =>
        show incidenceWork (E e).scope u + incidenceWork (E e).scope v + 2 ≤ 8 * n + 10 by
          have hu := hs e u; have hv := hs e v; omega)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
      have hu := index_size_le u
      have hv := index_size_le v
      nlinarith
    _ = _ := by simp; ring

/-- Constructing the binary membership key of an actual coordinate block. -/
def blockKeyWork {n : ℕ} (C : Finset (Fin n)) : ℕ :=
  ∑ v : Fin n, (incidenceWork C v + 1)

lemma blockKeyWork_le {n : ℕ} (C : Finset (Fin n)) (hC : C.card ≤ 2) :
    blockKeyWork C ≤ n * (4 * n + 5) := by
  unfold blockKeyWork
  calc
    _ ≤ ∑ _v : Fin n, (4 * n + 5) := by
      apply Finset.sum_le_sum
      intro v _
      have hh := (incidenceWork_le C v).trans (Nat.mul_le_mul_right (2 * n + 2) hC)
      nlinarith
    _ = _ := by simp

/-- Building and deduplicating the actual n candidate blocks, then sorting
exactly `blocks E` by its source membership keys. -/
def blockAssemblyWork {n r m : ℕ} (E : FactorFamily n r m) : ℕ :=
  (∑ v : Fin n, (blockKeyWork (block E v) + 1)) +
  (∑ u : Fin n, ∑ v : Fin n, (compareBits finsetKey (block E u) (block E v) + 1)) +
  sortCharge (blocks E) finsetKey

/-- Original scopes and computed neighbor lists are put in canonical order. -/
def inputSortWork {n r m : ℕ} (E : FactorFamily n r m) : ℕ :=
  (∑ e : Fin m, sortCharge (E e).scope indexKey) +
  ∑ v : Fin n, sortCharge (primalNeighbors E v) indexKey

/-- Find each occurrence's first scoped coordinate, then read the already
computed block and form its key. -/
def ownerWork {n r m : ℕ} (E : FactorFamily n r m) : ℕ :=
  ∑ e : Fin m, ((E e).scope.card * (n + 1) + blockKeyWork (owner E e) + 1)

/-- The source filters every occurrence for each actual block; factor-list
sorting is charged on the actual resulting factor sets. -/
def assignmentWork {n r m : ℕ} (E : FactorFamily n r m) : ℕ :=
  (∑ C ∈ blocks E, ∑ e : Fin m, (compareBits finsetKey (owner E e) C + 1)) +
  ∑ C ∈ blocks E, sortCharge (blockFactors E C) indexKey

/-- Source grid sorting and reading/building every full coordinate key. -/
def gridTraversalWork {n r m : ℕ} (E : FactorFamily n r m) (L : ℕ) : ℕ :=
  ∑ C ∈ blocks E,
    (sortCharge (Finset.univ : Finset (CellGrid.Grid (levels C L))) (gridKey (levels C L)) +
      ∑ z : CellGrid.Grid (levels C L), (keyBits (gridKey (levels C L) z) + 1))

/-- Construct the actual rational query coordinates: scope-index lookup,
reading the grid integer, constructing its dyadic denominator, and division.
The cubic envelope is the same schoolbook arithmetic model as `Expr.work`. -/
def coordinateWork {n r m L : ℕ} (E : FactorFamily n r m)
    (C : Finset (Fin n)) (z : CellGrid.Grid (levels C L)) (e : Fin m) : ℕ :=
  ∑ j : Fin (E e).scope.card,
    let v := (E e).scope.orderEmbOfFin rfl j
    ((E e).scope.card + 1) * (n + 1) +
      ((z v).val.size + levels C L v + 1) ^ 3 + 1

def queryCoordinateWork {n r m : ℕ} (E : FactorFamily n r m) (L : ℕ) : ℕ :=
  ∑ C ∈ blocks E, ∑ z : CellGrid.Grid (levels C L), ∑ e ∈ blockFactors E C,
    coordinateWork E C z e

/-- All previously uncharged discrete work, plus writing the actual expression
nodes. The returned numerical value is still exactly `runQ`. -/
def discreteWork {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b L : ℕ) : ℕ :=
  inputSortWork E + graphWork E + blockAssemblyWork E + ownerWork E + assignmentWork E +
    gridTraversalWork E L + queryCoordinateWork E L + 2 * (outputProgram E query U b L).operations + 1

lemma sortCharge_le_of_card_le {α : Type*} (S : Finset α) (key : α → List ℕ) {N D : ℕ}
    (hN : S.card ≤ N) (hD : ∀ x ∈ S, keyBits (key x) ≤ D) :
    sortCharge S key ≤ N ^ 2 * (2 * (N * D) + 6) := by
  apply (sortCharge_le S key hD).trans
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hN 2)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right D hN)) 6)

lemma inputSortWork_le {n r m : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) :
    inputSortWork E ≤ m * (4 * (4 * (n + 2) + 6)) + n * (2 * (n + 2) + 6) := by
  have hs : (∑ e : Fin m, sortCharge (E e).scope indexKey) ≤ m * (4 * (4 * (n + 2) + 6)) := by
    calc
      _ ≤ ∑ _e : Fin m, (4 * (4 * (n + 2) + 6)) := by
        apply Finset.sum_le_sum
        intro e _
        have hh := sortCharge_le_of_card_le (E e).scope indexKey
          (lowDegree_scope_card_le E hdeg e) (fun v _ => indexKey_bits_le v)
        nlinarith
      _ = _ := by simp
  have hn : (∑ v : Fin n, sortCharge (primalNeighbors E v) indexKey) ≤ n * (2 * (n + 2) + 6) := by
    calc
      _ ≤ ∑ _v : Fin n, (2 * (n + 2) + 6) := by
        apply Finset.sum_le_sum
        intro v _
        simpa using sortCharge_le_of_card_le (primalNeighbors E v) indexKey (hdeg v)
          (fun u _ => indexKey_bits_le u)
      _ = _ := by simp
  exact Nat.add_le_add hs hn

lemma blockAssemblyWork_le {n r m : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) :
    blockAssemblyWork E ≤ n * (n * (4 * n + 5) + 1) + n ^ 2 * (4 * n + 4) +
      n ^ 2 * (2 * (n * (2 * n + 1)) + 6) := by
  have hk : (∑ v : Fin n, (blockKeyWork (block E v) + 1)) ≤ n * (n * (4 * n + 5) + 1) := by
    calc
      _ ≤ ∑ _v : Fin n, (n * (4 * n + 5) + 1) := by
        apply Finset.sum_le_sum
        intro v _
        exact Nat.add_le_add_right (blockKeyWork_le _ (block_card_le_two E hdeg
          (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩))) 1
      _ = _ := by simp
  have hp : (∑ u : Fin n, ∑ v : Fin n, (compareBits finsetKey (block E u) (block E v) + 1)) ≤
      n ^ 2 * (4 * n + 4) := by
    calc
      _ ≤ ∑ _u : Fin n, ∑ _v : Fin n, (4 * n + 4) := by
        apply Finset.sum_le_sum
        intro u _
        apply Finset.sum_le_sum
        intro v _
        have hu := finsetKey_bits_le (block E u)
        have hv := finsetKey_bits_le (block E v)
        dsimp [compareBits]
        omega
      _ = _ := by simp; ring
  have hs := sortCharge_le_of_card_le (blocks E) finsetKey (blocks_card_le E)
    (fun C _ => finsetKey_bits_le C)
  exact Nat.add_le_add (Nat.add_le_add hk hp) hs

lemma ownerWork_le {n r m : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) :
    ownerWork E ≤ m * (2 * (n + 1) + n * (4 * n + 5) + 1) := by
  unfold ownerWork
  calc
    _ ≤ ∑ _e : Fin m, (2 * (n + 1) + n * (4 * n + 5) + 1) := by
      apply Finset.sum_le_sum
      intro e _
      have hs := lowDegree_scope_card_le E hdeg e
      have hk := blockKeyWork_le (owner E e) (block_card_le_two E hdeg (owner_mem_blocks E e))
      nlinarith
    _ = _ := by simp

lemma assignmentWork_le {n r m : ℕ} (E : FactorFamily n r m) :
    assignmentWork E ≤ n * (m * (4 * n + 4)) +
      n * (m ^ 2 * (2 * (m * (m + 2)) + 6)) := by
  have hc (C : Finset (Fin n)) :
      (∑ e : Fin m, (compareBits finsetKey (owner E e) C + 1)) ≤ m * (4 * n + 4) := by
    calc
      _ ≤ ∑ _e : Fin m, (4 * n + 4) := by
        apply Finset.sum_le_sum
        intro e _
        have he := finsetKey_bits_le (owner E e)
        have hC := finsetKey_bits_le C
        dsimp [compareBits]
        omega
      _ = _ := by simp
  have hs (C : Finset (Fin n)) : sortCharge (blockFactors E C) indexKey ≤
      m ^ 2 * (2 * (m * (m + 2)) + 6) :=
    sortCharge_le_of_card_le _ _ (by simpa using Finset.card_le_univ (blockFactors E C)) (fun e _ => indexKey_bits_le e)
  unfold assignmentWork
  apply Nat.add_le_add
  · exact (Finset.sum_le_sum (fun C _ => hc C)).trans (by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact Nat.mul_le_mul_right _ (blocks_card_le E))
  · exact (Finset.sum_le_sum (fun C _ => hs C)).trans (by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact Nat.mul_le_mul_right _ (blocks_card_le E))

lemma gridTraversalWork_le {n r m : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) (L : ℕ) :
    gridTraversalWork E L ≤ n * (2 ^ (2 * L)) ^ 2 *
      (2 * (2 ^ (2 * L) * (n * (L + 1) + 1)) + 6) +
      n * (2 ^ (2 * L)) * (n * (L + 1) + 2) := by
  have hh C (hC : C ∈ blocks E) :
      sortCharge (Finset.univ : Finset (CellGrid.Grid (levels C L))) (gridKey (levels C L)) +
        (∑ z : CellGrid.Grid (levels C L), (keyBits (gridKey (levels C L) z) + 1)) ≤
      (2 ^ (2 * L)) ^ 2 * (2 * (2 ^ (2 * L) * (n * (L + 1) + 1)) + 6) +
        2 ^ (2 * L) * (n * (L + 1) + 2) := by
    apply Nat.add_le_add
    · exact sortCharge_le_of_card_le _ _ (by simpa using grid_card_le E hdeg hC L)
        (fun z _ => gridKey_bits_le C z)
    · calc
        _ ≤ ∑ _z : CellGrid.Grid (levels C L), (n * (L + 1) + 2) :=
          Finset.sum_le_sum (fun z _ => Nat.add_le_add_right (gridKey_bits_le C z) 1)
        _ ≤ _ := by simpa using Nat.mul_le_mul_right (n * (L + 1) + 2) (grid_card_le E hdeg hC L)
  unfold gridTraversalWork
  apply (Finset.sum_le_sum hh).trans
  simp only [Finset.sum_const, nsmul_eq_mul]
  have h := Nat.mul_le_mul_right
    ((2 ^ (2 * L)) ^ 2 * (2 * (2 ^ (2 * L) * (n * (L + 1) + 1)) + 6) +
      2 ^ (2 * L) * (n * (L + 1) + 2)) (blocks_card_le E)
  nlinarith

lemma coordinateWork_le {n r m L : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) (C : Finset (Fin n))
    (z : CellGrid.Grid (levels C L)) (e : Fin m) :
    coordinateWork E C z e ≤ 2 * (3 * (n + 1) + (2 * L + 1) ^ 3 + 1) := by
  have hs := lowDegree_scope_card_le E hdeg e
  have hv (v : Fin n) : (z v).val.size ≤ L := by
    apply Nat.size_le.mpr
    exact (z v).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by unfold levels; split_ifs <;> omega))
  unfold coordinateWork
  calc
    _ ≤ ∑ _j : Fin (E e).scope.card, (3 * (n + 1) + (2 * L + 1) ^ 3 + 1) := by
      apply Finset.sum_le_sum
      intro j _
      dsimp only
      have hlevel : levels C L ((E e).scope.orderEmbOfFin rfl j) ≤ L := by
        unfold levels; split_ifs <;> omega
      have hindex := hv ((E e).scope.orderEmbOfFin rfl j)
      have hpow := Nat.pow_le_pow_left (by omega :
        (z ((E e).scope.orderEmbOfFin rfl j)).val.size +
          levels C L ((E e).scope.orderEmbOfFin rfl j) + 1 ≤ 2 * L + 1) 3
      nlinarith
    _ ≤ _ := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Nat.mul_le_mul_right (3 * (n + 1) + (2 * L + 1) ^ 3 + 1) hs

lemma queryCoordinateWork_le {n r m : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) (L : ℕ) :
    queryCoordinateWork E L ≤ n * (2 ^ (2 * L)) * m *
      (2 * (3 * (n + 1) + (2 * L + 1) ^ 3 + 1)) := by
  let D := 2 * (3 * (n + 1) + (2 * L + 1) ^ 3 + 1)
  have hc (C : Finset (Fin n)) (z : CellGrid.Grid (levels C L)) : (∑ e ∈ blockFactors E C, coordinateWork E C z e) ≤ m * D := by
    apply (Finset.sum_le_sum (fun e _ => coordinateWork_le E hdeg C z e)).trans
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact Nat.mul_le_mul_right D (by simpa using Finset.card_le_univ (blockFactors E C))
  unfold queryCoordinateWork
  calc
    _ ≤ ∑ C ∈ blocks E, ∑ _z : CellGrid.Grid (levels C L), (m * D) :=
      Finset.sum_le_sum (fun C _ => Finset.sum_le_sum (fun z _ => hc C z))
    _ ≤ ∑ _C ∈ blocks E, 2 ^ (2 * L) * (m * D) := by
      apply Finset.sum_le_sum
      intro C hC
      simpa using Nat.mul_le_mul_right (m * D) (grid_card_le E hdeg hC L)
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hh := Nat.mul_le_mul_right (2 ^ (2 * L) * (m * D)) (blocks_card_le E)
      simpa only [Nat.mul_assoc] using hh

lemma outputProgram_operations_le_factors {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (hdeg : FamilyPrimalDegreeLe E 1) (U b L : ℕ) :
    (outputProgram E query U b L).operations ≤
      n * (2 ^ (2 * L) * (m * (2 * b + 6) + 2 * L + 3) + 1) := by
  have hc C (hC : C ∈ blocks E) : (componentProgram E query U b L C).operations ≤
      2 ^ (2 * L) * (m * (2 * b + 6) + 2 * L + 3) := by
    rw [componentProgram_operations]
    apply Nat.mul_le_mul (grid_card_le E hdeg hC L)
    have ht : (blockFactors E C).card ≤ m := by simpa using Finset.card_le_univ (blockFactors E C)
    have hcard := block_card_le_two E hdeg hC
    nlinarith
  letI := finsetOrder n
  unfold outputProgram
  exact (productSet_operations_le _ _ hc).trans (Nat.mul_le_mul_right _ (blocks_card_le E))

/-- Explicit polynomial in input dimensions and grid count. Every summand
corresponds to one of the source loops defined above. -/
def discreteBound (n m b L G : ℕ) : ℕ :=
  (m * (4 * (4 * (n + 2) + 6)) + n * (2 * (n + 2) + 6)) +
  n ^ 2 * (2 * n + 2 + m * (8 * n + 10)) +
  (n * (n * (4 * n + 5) + 1) + n ^ 2 * (4 * n + 4) + n ^ 2 * (2 * (n * (2 * n + 1)) + 6)) +
  m * (2 * (n + 1) + n * (4 * n + 5) + 1) +
  (n * (m * (4 * n + 4)) + n * (m ^ 2 * (2 * (m * (m + 2)) + 6))) +
  (n * G ^ 2 * (2 * (G * (n * (L + 1) + 1)) + 6) + n * G * (n * (L + 1) + 2)) +
  n * G * m * (2 * (3 * (n + 1) + (2 * L + 1) ^ 3 + 1)) +
  2 * (n * (G * (m * (2 * b + 6) + 2 * L + 3) + 1)) + 1

theorem discreteWork_le {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (hdeg : FamilyPrimalDegreeLe E 1) (U b L : ℕ) :
    discreteWork E query U b L ≤ discreteBound n m b L (2 ^ (2 * L)) := by
  have h1 := inputSortWork_le E hdeg
  have h2 := graphWork_le E hdeg
  have h3 := blockAssemblyWork_le E hdeg
  have h4 := ownerWork_le E hdeg
  have h5 := assignmentWork_le E
  have h6 := gridTraversalWork_le E hdeg L
  have h7 := queryCoordinateWork_le E hdeg L
  have h8 := outputProgram_operations_le_factors E query hdeg U b L
  unfold discreteWork discreteBound
  omega

/-- The actual nonnegative ceiling/log/max control path. The integer scan
has exactly `clog 2 (ceil x)+1` rounds and charges the input and round-counter
bits. Ceiling division uses the ordinary cubic integer-arithmetic envelope. -/
def precisionControl (x : ℚ) : ℕ :=
  let N := ⌈x⌉₊
  let P := Nat.clog 2 N
  (BitComplexity.rationalBits x + 1) ^ 3 +
    (∑ j ∈ Finset.range (P + 1), ((N.size + j.size + 1) ^ 2 + 1)) + P.size + 1

def precisionControlBound (B : ℕ) : ℕ :=
  (B + 1) ^ 3 + (B + 1) * ((2 * B + 2) ^ 2 + 1) + B + 1

lemma nat_size_le_self (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self

/-- This numerical bound uses the actual canonical rational numerator; it is
proved from division and needs no magnitude promise on the argument. -/
theorem ceil_numeric_le (x : ℚ) : ⌈x⌉₊ ≤ x.num.natAbs := by
  apply Nat.ceil_le.mpr
  have hd : (1 : ℚ) ≤ (x.den : ℚ) := by exact_mod_cast x.den_pos
  have hn : (x.num : ℚ) ≤ (x.num.natAbs : ℚ) := by
    have hh : x.num ≤ (x.num.natAbs : ℤ) := Int.le_natAbs
    simpa only [Int.cast_natCast] using (show ((x.num : ℤ) : ℚ) ≤ ((x.num.natAbs : ℤ) : ℚ) from
      (Int.cast_le (R := ℚ)).mpr hh)
  calc
    x = (x.num : ℚ) / (x.den : ℚ) := x.num_div_den.symm
    _ ≤ (x.num.natAbs : ℚ) / (x.den : ℚ) := div_le_div_of_nonneg_right hn (by positivity)
    _ ≤ x.num.natAbs := div_le_self (by positivity) hd

theorem ceil_le_pow_inputBits (x : ℚ) : ⌈x⌉₊ ≤ 2 ^ BitComplexity.rationalBits x := by
  apply (ceil_numeric_le x).trans
  apply (Nat.lt_size_self x.num.natAbs).le.trans
  apply Nat.pow_le_pow_right (by decide)
  unfold BitComplexity.rationalBits
  omega

theorem precision_clog_le_inputBits (x : ℚ) :
    Nat.clog 2 ⌈x⌉₊ ≤ BitComplexity.rationalBits x :=
  (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr (ceil_le_pow_inputBits x)

theorem precision_ceil_size_le_inputBits (x : ℚ) :
    (⌈x⌉₊).size ≤ BitComplexity.rationalBits x + 1 := by
  apply Nat.size_le.mpr
  have hh := ceil_le_pow_inputBits x
  have hp := Nat.pow_lt_pow_right (by decide : 1 < 2)
    (show BitComplexity.rationalBits x < BitComplexity.rationalBits x + 1 by omega)
  exact hh.trans_lt hp

/-- The complete ceil/clog/max control cost is polynomial in the actual
input encoding length, even when the numeric ceiling is exponentially large. -/
theorem precisionControl_le_inputBits (x : ℚ) :
    precisionControl x ≤ precisionControlBound (BitComplexity.rationalBits x) := by
  let B := BitComplexity.rationalBits x
  let N := ⌈x⌉₊
  let P := Nat.clog 2 N
  have hp : P ≤ B := precision_clog_le_inputBits x
  have hn : N.size ≤ B + 1 := precision_ceil_size_le_inputBits x
  have hs : (∑ j ∈ Finset.range (P + 1), ((N.size + j.size + 1) ^ 2 + 1)) ≤
      (B + 1) * ((2 * B + 2) ^ 2 + 1) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (P + 1), ((2 * B + 2) ^ 2 + 1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j ≤ B := (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hp
        exact Nat.add_le_add_right (Nat.pow_le_pow_left (by
          have hjbits := nat_size_le_self j
          omega : N.size + j.size + 1 ≤ 2 * B + 2) 2) 1
      _ ≤ _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hp 1)
  have hps := (nat_size_le_self P).trans hp
  change (B + 1) ^ 3 + _ + P.size + 1 ≤ _
  unfold precisionControlBound
  dsimp only [B, N, P] at *
  omega

/-- Precision selection on the actual quotient used by the algorithm. -/
@[simp] theorem precisionControl_choice (A : ℕ) (ε : ℚ) :
    max 1 (Nat.clog 2 ⌈(A : ℚ) / ε⌉₊) = dyadicPrecision A ε := rfl

lemma discreteBound_mono_grid (n m b L : ℕ) {G H : ℕ} (h : G ≤ H) :
    discreteBound n m b L G ≤ discreteBound n m b L H := by
  unfold discreteBound
  gcongr

/-- At the automatically selected mesh, all discrete loops have polynomial
cost in n/ε and the selected logarithmic precisions. -/
theorem selected_discreteWork_le {n r m Δ : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (hdeg : FamilyPrimalDegreeLe E 1) (U T : ℕ) (ε : ℚ) :
    let b := answerBits Δ U n ε
    let L := meshLevel T n ε
    let M := 2 * (⌈((4 * T * n : ℕ) : ℚ) / ε⌉₊ + 1)
    discreteWork E query U b L ≤ discreteBound n m b L (M ^ 2) := by
  dsimp only
  apply (discreteWork_le E query hdeg U _ _).trans
  apply discreteBound_mono_grid
  rw [Nat.mul_comm 2 _, pow_mul]
  exact Nat.pow_le_pow_left (dyadicPrecision_pow_le (4 * T * n) ε) 2

open RationalProgram

lemma precisionControlBound_mono {B C : ℕ} (h : B ≤ C) :
    precisionControlBound B ≤ precisionControlBound C := by
  unfold precisionControlBound
  gcongr

/-- Execute a real expression for the control argument, then its integer
ceil/clog/max path. This is reusable for the main FPTAS parameter expressions. -/
def expressionControlWork (e : Expr) : ℕ := e.work + precisionControl e.eval

def expressionControlBound (H P : ℕ) : ℕ :=
  P * (4 * ((H + 2) * (P + 1)) + 3) ^ 3 +
    precisionControlBound (2 * (H * (P + 1) + 2 * P) + 1)

theorem expressionControlWork_le (e : Expr) {H P : ℕ}
    (hi : e.inputHeight ≤ H) (ho : e.operations ≤ P) :
    expressionControlWork e ≤ expressionControlBound H P := by
  have hh := e.height_le.trans (Nat.add_le_add
    (Nat.mul_le_mul hi (Nat.add_le_add_right ho 1)) (Nat.mul_le_mul_left 2 ho))
  have hb := (bits_le_height e.eval).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hh) 1)
  have hw := e.work_le.trans (Nat.mul_le_mul ho (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (Nat.mul_le_mul
      (Nat.add_le_add_right hi 2) (Nat.add_le_add_right ho 1))) 3) 3))
  exact Nat.add_le_add hw ((precisionControl_le_inputBits e.eval).trans (precisionControlBound_mono hb))

/-- The actual mesh quotient, with its numerator multiplications exposed. -/
def meshArgument (n T : ℕ) (ε : ℚ) : Expr :=
  .node .div (.node .mul (.node .mul (.atom 4) (.atom T)) (.atom n)) (.atom ε)

/-- The actual answer-precision quotient, including the fixed-parameter power. -/
def answerArgument (n Δ U : ℕ) (ε : ℚ) : Expr :=
  .node .div (.node .mul (.node .mul (.node .mul (.atom 4)
    (.node .mul (.atom 2) (.atom Δ))) (natPower (.atom U) (2 * Δ - 1))) (.atom n)) (.atom ε)

@[simp] theorem meshArgument_eval (n T : ℕ) (ε : ℚ) :
    (meshArgument n T ε).eval = ((4 * T * n : ℕ) : ℚ) / ε := by
  simp [meshArgument, Expr.eval, Op.eval]

@[simp] theorem answerArgument_eval (n Δ U : ℕ) (ε : ℚ) :
    (answerArgument n Δ U ε).eval = ((4 * (2 * Δ) * U ^ (2 * Δ - 1) * n : ℕ) : ℚ) / ε := by
  simp [answerArgument, Expr.eval, Op.eval]

/-- This height is computed from the actual input encodings. -/
def parameterHeight (n Δ U T : ℕ) (ε : ℚ) : ℕ :=
  height (n : ℚ) + height (Δ : ℚ) + height (U : ℚ) + height (T : ℚ) + height ε + 5

def precisionSelectionWork (n Δ U T : ℕ) (ε : ℚ) : ℕ :=
  expressionControlWork (meshArgument n T ε) + expressionControlWork (answerArgument n Δ U ε)

def precisionSelectionBound (n Δ U T : ℕ) (ε : ℚ) : ℕ :=
  2 * expressionControlBound (parameterHeight n Δ U T ε) (2 * Δ + 8)

lemma height_four_le : height (4 : ℚ) ≤ 4 := by
  norm_num [height]
  exact Nat.size_le.mpr (by norm_num)

lemma meshArgument_inputHeight (n Δ U T : ℕ) (ε : ℚ) :
    (meshArgument n T ε).inputHeight ≤ parameterHeight n Δ U T ε := by
  have h4 := height_four_le
  simp only [meshArgument, Expr.inputHeight, parameterHeight]
  omega

lemma answerArgument_inputHeight (n Δ U T : ℕ) (ε : ℚ) :
    (answerArgument n Δ U ε).inputHeight ≤ parameterHeight n Δ U T ε := by
  have h4 := height_four_le
  have h2 := height_two_le
  have hp : (natPower (.atom U) (2 * Δ - 1)).inputHeight ≤ parameterHeight n Δ U T ε := by
    apply natPower_inputHeight
    · unfold parameterHeight; omega
    · simp only [Expr.inputHeight, parameterHeight]; omega
  simp only [answerArgument, Expr.inputHeight]
  unfold parameterHeight at *
  omega

lemma precisionSelectionWork_le (n Δ U T : ℕ) (ε : ℚ) :
    precisionSelectionWork n Δ U T ε ≤ precisionSelectionBound n Δ U T ε := by
  have hm := expressionControlWork_le (meshArgument n T ε) (meshArgument_inputHeight n Δ U T ε)
    (P := 2 * Δ + 8) (by simp [meshArgument, Expr.operations] <;> omega)
  have ha := expressionControlWork_le (answerArgument n Δ U ε) (answerArgument_inputHeight n Δ U T ε)
    (P := 2 * Δ + 8) (by simp [answerArgument, Expr.operations] <;> omega)
  unfold precisionSelectionWork precisionSelectionBound
  omega

/-- Full ordinary bit-cost model: effective oracle time, operand-sensitive
rational arithmetic, all discrete source loops and actual precision selection. -/
def completeWork {n r m A degree : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (Δ U T : ℕ) (ε : ℚ) : ℕ :=
  actualTotalWork E labelBits O Δ U T ε +
    discreteWork E (fun e => (O e).valueOracle.query) U (answerBits Δ U n ε) (meshLevel T n ε) +
    precisionSelectionWork n Δ U T ε

def completeBound (n m Δ A degree H U T : ℕ) (ε : ℚ) : ℕ :=
  let b := answerBits Δ U n ε
  let L := meshLevel T n ε
  let M := 2 * (⌈((4 * T * n : ℕ) : ℚ) / ε⌉₊ + 1)
  totalWorkBound n Δ A degree H U T ε + discreteBound n m b L (M ^ 2) +
    precisionSelectionBound n Δ U T ε

theorem completeWork_le {n r m Δ A degree H : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H) (hdeg : FamilyPrimalDegreeLe E 1)
    (hocc : FamilyBoundedOccurrence E Δ) (U T : ℕ) (ε : ℚ) :
    completeWork E labelBits O Δ U T ε ≤ completeBound n m Δ A degree H U T ε := by
  have ha := runProgram_total_work_le E labelBits O hlabels hdeg hocc U T ε
  have hd := selected_discreteWork_le (Δ := Δ) E (fun e => (O e).valueOracle.query) hdeg U T ε
  have hp := precisionSelectionWork_le n Δ U T ε
  exact Nat.add_le_add (Nat.add_le_add ha hd) hp

/-- Lemma A.1 with all non-oracle discrete work included. No component,
integral factorization, output encoding or running-time certificate is assumed. -/
theorem lemma_A1_complete {n r m Δ A degree H : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    {U K : ℝ} (hU : 1 < U) (hK : 0 < K)
    (hrange : ∀ e x, x ∈ Integral.cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U)
    (hLip : ∀ e, (E e).LipOk K) (ε : ℚ) (hε : 0 < ε) :
    FPTAS.Accurate
      ((runProgram E (fun e => (O e).valueOracle.query) Δ (rangeBound U) (lipBudget Δ K U) ε).eval : ℝ)
      (Integral.partitionFunctionFactor E) ε ∧
    completeWork E labelBits O Δ (rangeBound U) (lipBudget Δ K U) ε ≤
      completeBound n m Δ A degree H (rangeBound U) (lipBudget Δ K U) ε := by
  exact ⟨(lemma_A1_effective E labelBits O hlabels hdeg hocc hU hK hrange hLip ε hε).1,
    completeWork_le E labelBits O hlabels hdeg hocc _ _ ε⟩

/-- The computed canonical traversal is exactly the source mergesort output,
and its real comparison trace is covered for every input representation. -/
theorem canonical_source_sort {α : Type*} [LinearOrder α] (S : Finset α)
    (key : α → List ℕ) (l : List α) (hnodup : l.Nodup) (hS : l.toFinset = S) :
    l.mergeSort (fun a b => decide (a ≤ b)) = canonicalList S ∧
    sortWork key (fun a b => decide (a ≤ b)) l ≤ sortCharge S key := by
  constructor
  · have hm : @Finset.mk α (l : Multiset α) (by simpa using hnodup) = S :=
      (List.toFinset_eq hnodup).trans hS
    rw [← hm]
    rfl
  · exact source_sort_le_charge S key _ l hnodup hS

/-- A concrete full-scope scan implements the incidence predicate used in
both graph construction and key materialization. -/
def incidenceBool {n : ℕ} (S : Finset (Fin n)) (v : Fin n) : Bool :=
  (canonicalList S).any (fun w => decide (w = v))

@[simp] theorem incidenceBool_true {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    incidenceBool S v = true ↔ v ∈ S := by
  simp [incidenceBool, List.any_eq_true]

def graphBool {n r m : ℕ} (E : FactorFamily n r m) (u v : Fin n) : Bool :=
  decide (u ≠ v) && (canonicalList (Finset.univ : Finset (Fin m))).any
    (fun e => incidenceBool (E e).scope u && incidenceBool (E e).scope v)

def scannedNeighbors {n r m : ℕ} (E : FactorFamily n r m) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => graphBool E u v = true)

@[simp] theorem scannedNeighbors_eq {n r m : ℕ} (E : FactorFamily n r m) (v : Fin n) :
    scannedNeighbors E v = primalNeighbors E v := by
  ext u
  simp [scannedNeighbors, graphBool, primalNeighbors, List.any_eq_true]

/-- The instrumented naive graph/coordinate-block construction produces the
very same blocks consumed by the already verified rational algorithm. -/
def scannedBlocks {n r m : ℕ} (E : FactorFamily n r m) : Finset (Finset (Fin n)) :=
  Finset.univ.image (fun v => insert v (scannedNeighbors E v))

@[simp] theorem scannedBlocks_eq {n r m : ℕ} (E : FactorFamily n r m) :
    scannedBlocks E = blocks E := by
  unfold scannedBlocks blocks
  apply Finset.image_congr
  intro v _
  dsimp only
  rw [scannedNeighbors_eq]
  rfl

/-- Component assignment is likewise the original source filter, with its
owner obtained from the proved graph scan rather than a partition certificate. -/
def scannedOwner {n r m : ℕ} (E : FactorFamily n r m) (e : Fin m) : Finset (Fin n) :=
  let v := (E e).scope.min' (E e).nonempty
  insert v (scannedNeighbors E v)

@[simp] theorem scannedOwner_eq {n r m : ℕ} (E : FactorFamily n r m) (e : Fin m) :
    scannedOwner E e = owner E e := by
  simp [scannedOwner, owner, block]

def scannedFactors {n r m : ℕ} (E : FactorFamily n r m) (C : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter (fun e => scannedOwner E e = C)

@[simp] theorem scannedFactors_eq {n r m : ℕ} (E : FactorFamily n r m) (C : Finset (Fin n)) :
    scannedFactors E C = blockFactors E C := by
  simp [scannedFactors, blockFactors]

/-- The η=1 corollary with graph, assignment, sorting, coordinate construction
and parameter control included in the ordinary bit-cost model. -/
theorem corollary_1_3_eta_one_complete {n r m Δ A degree H : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    {δ K : ℝ} (hρ : 1 < FPTAS.gamarnikSmediraRho Δ 1 δ) (hK : 0 < K)
    (hrange : ∀ e x, x ∈ Integral.cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ FPTAS.gamarnikSmediraRho Δ 1 δ)
    (hLip : ∀ e, (E e).LipOk K) (ε : ℚ) (hε : 0 < ε) :
    let U := rangeBound (FPTAS.gamarnikSmediraRho Δ 1 δ)
    let T := lipBudget Δ K (FPTAS.gamarnikSmediraRho Δ 1 δ)
    FPTAS.Accurate ((runProgram E (fun e => (O e).valueOracle.query) Δ U T ε).eval : ℝ)
      (Integral.partitionFunctionFactor E) ε ∧
    completeWork E labelBits O Δ U T ε ≤ completeBound n m Δ A degree H U T ε :=
  lemma_A1_complete E labelBits O hlabels hdeg hocc hρ hK hrange hLip ε hε

/-- The parameter-control encoding budget is itself bounded by original
input bits and logarithmic integer sizes. -/
theorem parameterHeight_le_inputBits (n Δ U T : ℕ) (ε : ℚ) :
    parameterHeight n Δ U T ε ≤ BitComplexity.rationalBits ε +
      Nat.clog 2 n + Nat.clog 2 Δ + Nat.clog 2 U + Nat.clog 2 T + 17 := by
  have hn := nat_height_le n
  have hd := nat_height_le Δ
  have hu := nat_height_le U
  have ht := nat_height_le T
  have he := height_le_bits ε
  unfold parameterHeight
  omega

lemma expressionControlBound_mono {H I P Q : ℕ} (hH : H ≤ I) (hP : P ≤ Q) :
    expressionControlBound H P ≤ expressionControlBound I Q := by
  unfold expressionControlBound
  apply Nat.add_le_add
  · gcongr
  · apply precisionControlBound_mono
    gcongr

theorem precisionSelectionBound_le_inputBits (n Δ U T : ℕ) (ε : ℚ) :
    precisionSelectionBound n Δ U T ε ≤
      2 * expressionControlBound (BitComplexity.rationalBits ε +
        Nat.clog 2 n + Nat.clog 2 Δ + Nat.clog 2 U + Nat.clog 2 T + 17) (2 * Δ + 8) :=
  Nat.mul_le_mul_left 2 (expressionControlBound_mono (parameterHeight_le_inputBits n Δ U T ε) le_rfl)

/-- The precision-argument quotients are evaluated by the actual binary
kernel as well; the remaining integer-control scans are charged above. -/
def binarySelectionWork (n Δ U T : ℕ) (ε : ℚ) : ℕ :=
  (SchoolbookArithmetic.execute (meshArgument n T ε)).2 +
    (SchoolbookArithmetic.execute (answerArgument n Δ U ε)).2 +
    precisionControl (meshArgument n T ε).eval + precisionControl (answerArgument n Δ U ε).eval

lemma binarySelectionWork_le (n Δ U T : ℕ) (ε : ℚ) :
    binarySelectionWork n Δ U T ε ≤ 10000 * precisionSelectionBound n Δ U T ε := by
  have hm := SchoolbookArithmetic.exprBitCost_le (meshArgument n T ε)
  have ha := SchoolbookArithmetic.exprBitCost_le (answerArgument n Δ U ε)
  have hp := precisionSelectionWork_le n Δ U T ε
  unfold binarySelectionWork
  rw [(SchoolbookArithmetic.execute_spec _).2, (SchoolbookArithmetic.execute_spec _).2]
  unfold precisionSelectionWork expressionControlWork at hp
  nlinarith

/-- Actual binary arithmetic execution, actual oracle time, discrete source
loops and parameter selection. All values are computed from original leaves. -/
def fullBitWork {n r m A degree : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (Δ U T : ℕ) (ε : ℚ) : ℕ :=
  (SchoolbookArithmetic.execute (runProgram E (fun e => (O e).valueOracle.query) Δ U T ε)).2 +
    oracleTime E labelBits O (answerBits Δ U n ε) (meshLevel T n ε) +
    discreteWork E (fun e => (O e).valueOracle.query) U (answerBits Δ U n ε) (meshLevel T n ε) +
    binarySelectionWork n Δ U T ε

def fullBitBound (n m Δ A degree H U T : ℕ) (ε : ℚ) : ℕ :=
  let b := answerBits Δ U n ε
  let L := meshLevel T n ε
  let M := 2 * (⌈((4 * T * n : ℕ) : ℚ) / ε⌉₊ + 1)
  10000 * totalWorkBound n Δ A degree H U T ε + discreteBound n m b L (M ^ 2) +
    10000 * precisionSelectionBound n Δ U T ε

theorem fullBitWork_le {n r m Δ A degree H : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H) (hdeg : FamilyPrimalDegreeLe E 1)
    (hocc : FamilyBoundedOccurrence E Δ) (U T : ℕ) (ε : ℚ) :
    fullBitWork E labelBits O Δ U T ε ≤ fullBitBound n m Δ A degree H U T ε := by
  have hk := SchoolbookArithmetic.exprBitCost_le
    (runProgram E (fun e => (O e).valueOracle.query) Δ U T ε)
  have ha := runProgram_total_work_le E labelBits O hlabels hdeg hocc U T ε
  have hd := selected_discreteWork_le (Δ := Δ) E (fun e => (O e).valueOracle.query) hdeg U T ε
  have hp := binarySelectionWork_le n Δ U T ε
  have hm : (SchoolbookArithmetic.execute
      (runProgram E (fun e => (O e).valueOracle.query) Δ U T ε)).2 +
      oracleTime E labelBits O (answerBits Δ U n ε) (meshLevel T n ε) ≤
      10000 * totalWorkBound n Δ A degree H U T ε := by
    rw [(SchoolbookArithmetic.execute_spec _).2]
    change _ ≤ 10000 * totalWorkBound n Δ A degree H U T ε
    change _ ≤ totalWorkBound n Δ A degree H U T ε at ha
    nlinarith
  exact Nat.add_le_add (Nat.add_le_add hm hd) hp

/-- Appendix A's actual returned rational, computed by validated binary
kernels, with every non-oracle discrete stage included in its bit-cost model. -/
theorem lemma_A1_bit_algorithm {n r m Δ A degree H : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    {U K : ℝ} (hU : 1 < U) (hK : 0 < K)
    (hrange : ∀ e x, x ∈ Integral.cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U)
    (hLip : ∀ e, (E e).LipOk K) (ε : ℚ) (hε : 0 < ε) :
    FPTAS.Accurate
      ((SchoolbookArithmetic.execute (runProgram E (fun e => (O e).valueOracle.query)
        Δ (rangeBound U) (lipBudget Δ K U) ε)).1 : ℝ)
      (Integral.partitionFunctionFactor E) ε ∧
    fullBitWork E labelBits O Δ (rangeBound U) (lipBudget Δ K U) ε ≤
      fullBitBound n m Δ A degree H (rangeBound U) (lipBudget Δ K U) ε := by
  constructor
  · rw [(SchoolbookArithmetic.execute_spec _).1]
    exact (lemma_A1_effective E labelBits O hlabels hdeg hocc hU hK hrange hLip ε hε).1
  · exact fullBitWork_le E labelBits O hlabels hdeg hocc _ _ ε

/-- η=1 uses the same executed low-degree algorithm and full bit-cost bound. -/
theorem corollary_1_3_eta_one_bit_algorithm {n r m Δ A degree H : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    {δ K : ℝ} (hρ : 1 < FPTAS.gamarnikSmediraRho Δ 1 δ) (hK : 0 < K)
    (hrange : ∀ e x, x ∈ Integral.cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ FPTAS.gamarnikSmediraRho Δ 1 δ)
    (hLip : ∀ e, (E e).LipOk K) (ε : ℚ) (hε : 0 < ε) :
    let U := rangeBound (FPTAS.gamarnikSmediraRho Δ 1 δ)
    let T := lipBudget Δ K (FPTAS.gamarnikSmediraRho Δ 1 δ)
    FPTAS.Accurate ((SchoolbookArithmetic.execute
      (runProgram E (fun e => (O e).valueOracle.query) Δ U T ε)).1 : ℝ)
      (Integral.partitionFunctionFactor E) ε ∧
    fullBitWork E labelBits O Δ U T ε ≤ fullBitBound n m Δ A degree H U T ε :=
  lemma_A1_bit_algorithm E labelBits O hlabels hdeg hocc hρ hK hrange hLip ε hε

end Paper08.LowDegreeDiscreteCost
