import Paper20.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Enum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic

/-!
# Paper 20 — Hilbert series and BPS coefficients

Computational model of equations (13), (24) and (25):
`H_{r,k}` via the partition sum, `F_ℓ = [q^ℓ](1-q)^r H`, and the triangular
recurrence for `n_h(C_{r,k})`, matching Appendix A exactly.

The identification of `H_{r,k}` with the punctual Hilbert series of the
curve singularity, and of `B_{r,k}` with a Hecke trace, is external
(Hilbert–HOMFLY / Mathas); see `coverage.json`.

Sign convention: `H` has nonnegative entries; the working array `F` of
`(1-q)^r H` is an integer array (entries may be negative), as in Appendix A.
-/

namespace Paper20

/-! ## Partition hooks and dimension (computational form, Appendix A `shape`) -/

/-- Column lengths of a part-list (0-based columns). -/
def colLens (parts : List ℕ) (maxCol : ℕ) : List ℕ :=
  (List.range maxCol).map fun j => (parts.filter (· > j)).length

/-- Hook lengths of a part-list, using zero-based rows and columns
(`λ_{i+1} - j + λ'_{j+1} - i - 1` in Appendix A). -/
def hooksOf (parts : List ℕ) : List ℕ :=
  (parts.zipIdx).flatMap fun (a, i) =>
    (List.range a).map fun j =>
      a - j + ((parts.filter (· > j)).length) - i - 1

/-- `ν = Σ_i i·λ_i` (0-based). -/
def nuOf (parts : List ℕ) : ℕ :=
  (parts.zipIdx).foldl (fun acc (a, i) => acc + i * a) 0

/-- Content `c = Σ_i (λ_i(λ_i-1)/2 - i·λ_i)` as an integer (may be negative). -/
def contentOf (parts : List ℕ) : ℤ :=
  (parts.zipIdx).foldl (fun acc (a, i) =>
    acc + ((a * (a - 1) / 2 : ℕ) : ℤ) - ((i * a : ℕ) : ℤ)) 0

/-- Hook-length dimension `f^λ = n! / Π hooks`. -/
def dimOf (n : ℕ) (parts : List ℕ) : ℕ :=
  n.factorial / (hooksOf parts).prod

/-- Number of even hook lengths. -/
def evenHooksOf (parts : List ℕ) : ℕ :=
  (hooksOf parts).countP (fun a => a % 2 == 0)

/-! ## Partition enumeration (Appendix A `partitions`) -/

/-- Fuelled partition generator: `partitionsCappedAux fuel cap n` enumerates
partitions of `n` with parts at most `cap`, using at most `fuel` recursive steps.
For `fuel ≥ n` this matches the Python recursion `partitions(n, cap)` exactly. -/
def partitionsCappedAux (fuel cap n : ℕ) : List (List ℕ) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    if n = 0 then [[]]
    else
      (List.range' 1 (min n cap)).reverse.flatMap fun a =>
        (partitionsCappedAux fuel a (n - a)).map fun tail => a :: tail

/-- Partitions of `n` with every part at most `cap`, weakly decreasing positive parts.
Matches the Python recursion `partitions(n, cap)` (parts emitted large-to-small).
Fuel `n+1` is enough because each recursive call decreases `n`. -/
def partitionsCapped (cap n : ℕ) : List (List ℕ) := partitionsCappedAux (n + 1) cap n

/-- All partitions of `n` (parts weakly decreasing, each positive). -/
def partitionsOf (n : ℕ) : List (List ℕ) := partitionsCapped n n

/-! ## Series arithmetic (truncated polynomials) -/

/-- `Array.set!` preserves length. -/
theorem size_setBang {α : Type*} (t : Array α) (i : ℕ) (v : α) :
    (t.set! i v).size = t.size := by
  simp [Array.set!]

/-- Foldl over a list, with a size-preserving step. -/
theorem size_foldl_cons {α γ : Type*} {f : Array γ → α → Array γ} {l : List α} {b : Array γ}
    (hf : ∀ b a, (f b a).size = b.size) :
    (l.foldl f b).size = b.size := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    show (List.foldl f (f b a) l).size = b.size
    rw [ih, hf]

/-- Geometric step `t[j] += t[j-a]` for `j = a .. t.size-1` (Appendix A). -/
def geomStep (t : Array ℕ) (a : ℕ) : Array ℕ :=
  (List.range (t.size - a)).foldl (init := t) fun t j =>
    t.set! (a + j) (t[a + j]! + t[j]!)

/-- `1 / Π (1-q^{h})` truncated to length `len`, starting from `1`. -/
def geomSeries (hooks : List ℕ) (len : ℕ) : Array ℕ :=
  hooks.foldl geomStep (Array.replicate len 0 |>.set! 0 1)

/-- One finite difference `H ↦ (H[0], H[1]-H[0], …)` over `ℤ`
(each new entry uses the *old* array). -/
def diffOnce (H : Array ℤ) : Array ℤ :=
  (List.range (H.size - 1)).foldl (init := H) fun acc j =>
    acc.set! (j + 1) (H[j + 1]! - H[j]!)

/-- Multiply by `(1-q)^r` by iterating finite differences (`r` times). -/
def mulOneMinusQPow (H : Array ℤ) (r : ℕ) : Array ℤ :=
  (List.range r).foldl (init := H) fun H _ => diffOnce H

/-! ## Hilbert coefficients `H_ℓ` (formula (13), truncated at degree `d`) -/

/-- Degree shift `E = d + (k+1)c + ν` of one partition summand (may a priori be negative). -/
def shiftE (parts : List ℕ) (k d : ℕ) : ℤ :=
  (d : ℤ) + ((k + 1 : ℕ) : ℤ) * contentOf parts + (nuOf parts : ℤ)

/-- Shifted partition summand contribution into `H` of length `d+1` (Appendix A). -/
def addSummand (H : Array ℕ) (parts : List ℕ) (r k d : ℕ) : Array ℕ :=
  let f := dimOf r parts
  let Ei := shiftE parts k d
  if Ei < 0 then H
  else
    let E := Ei.toNat
    if E > d then H
    else
      let t := geomSeries (hooksOf parts) (d - E + 1)
      (List.range t.size).foldl (init := H) fun H j =>
        H.set! (E + j) (H[E + j]! + f * t[j]!)

/-- Hilbert array `H[0..d]` of `C_{r,k}` from formula (13). -/
def hilbertArray (r k : ℕ) : Array ℕ :=
  let d := deg r k
  (partitionsOf r).foldl (fun H parts => addSummand H parts r k d)
    (Array.replicate (d + 1) 0)

/-- `F_ℓ = [q^ℓ](1-q)^r H` for `ℓ = 0..d` (integer array; entries may be negative). -/
def fArray (r k : ℕ) : Array ℤ :=
  mulOneMinusQPow ((hilbertArray r k).map fun x : ℕ => (x : ℤ)) r

/-! ## BPS coefficients via the triangular recurrence (25) -/

/-- Signed binomial `(-1)^j · C(2h, j)` as an integer. -/
def signedChoose (h j : ℕ) : ℤ :=
  (Nat.choose (2 * h) j : ℤ) * if j % 2 = 0 then 1 else -1

/-- One pass of the triangular elimination over indices `0 .. m-1`
(mutable state threaded as a pure pair). -/
def bpsPass (F : Array ℤ) : Array ℤ × Array ℤ :=
  let m := F.size
  let d := m - 1
  (List.range m).foldl (init := (F, Array.replicate m 0)) fun (H, n) ell =>
    let h := d - ell
    let nh := H[ell]!
    let n := n.set! h nh
    let H := (List.range (min (2 * h) (d - ell) + 1)).foldl (init := H) fun H j =>
      H.set! (ell + j) (H[ell + j]! - nh * signedChoose h j)
    (H, n)

/-- Extract all `n_h` of `C_{r,k}` from `F` by (25).
Returns the `n` array as integers (nonnegative in correct runs).
Length of the result equals `F.size`. -/
def bpsFromF (F : Array ℤ) : Array ℤ := (bpsPass F).2

/-- Residual of the triangular elimination (Appendix A `assert not any(H)`). -/
def bpsResidual (F : Array ℤ) : Array ℤ := (bpsPass F).1

/-- BPS coefficients `n_0, …, n_d` of `C_{r,k}` (formulas (13)+(25)), as naturals.
By construction the array has length `deg r k + 1`. -/
def bpsCoeffs (r k : ℕ) : Array ℕ :=
  let d := deg r k
  let n := bpsFromF (fArray r k)
  Array.ofFn fun i : Fin (d + 1) => (n.getD i 0).toNat

/-- The `h`-th BPS coefficient of `C_{r,k}` (0 out of range). -/
def bpsCoeff (r k h : ℕ) : ℕ :=
  (bpsCoeffs r k).getD h 0

/-- BPS polynomial coefficients as a list. -/
def bpsList (r k : ℕ) : List ℕ := (bpsCoeffs r k).toList

/-! ## Size bookkeeping -/

theorem size_geomStep (t : Array ℕ) (a : ℕ) : (geomStep t a).size = t.size :=
  size_foldl_cons fun _ _ => size_setBang ..

theorem size_geomSeries (hooks : List ℕ) (len : ℕ) :
    (geomSeries hooks len).size = len := by
  have key : ∀ (t : Array ℕ) (hs : List ℕ), (hs.foldl geomStep t).size = t.size := by
    intro t hs
    induction hs generalizing t with
    | nil => rfl
    | cons a as ih => rw [List.foldl_cons, ih, size_geomStep]
  unfold geomSeries
  rw [key, size_setBang]
  simp

theorem size_diffOnce (H : Array ℤ) : (diffOnce H).size = H.size :=
  size_foldl_cons fun _ _ => size_setBang ..

theorem size_mulOneMinusQPow (H : Array ℤ) (r : ℕ) :
    (mulOneMinusQPow H r).size = H.size := by
  have key : ∀ (t : Array ℤ) (js : List ℕ),
      (js.foldl (fun H _ => diffOnce H) t).size = t.size := by
    intro t js
    induction js generalizing t with
    | nil => rfl
    | cons _ as ih => rw [List.foldl_cons, ih, size_diffOnce]
  exact key H (List.range r)

theorem size_addSummand (H : Array ℕ) (parts : List ℕ) (r k d : ℕ) :
    (addSummand H parts r k d).size = H.size := by
  unfold addSummand
  dsimp only
  by_cases h1 : shiftE parts k d < 0
  · rw [if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : (shiftE parts k d).toNat > d
    · rw [if_pos h2]
    · rw [if_neg h2]
      exact size_foldl_cons fun t _ => size_setBang t _ _

theorem size_hilbertArray (r k : ℕ) : (hilbertArray r k).size = deg r k + 1 := by
  unfold hilbertArray
  have h := size_foldl_cons
    (f := fun (H : Array ℕ) (parts : List ℕ) => addSummand H parts r k (deg r k))
    (l := partitionsOf r) (b := Array.replicate (deg r k + 1) 0)
    (hf := fun H parts => size_addSummand H parts r k (deg r k))
  rw [h]
  simp

theorem size_fArray (r k : ℕ) : (fArray r k).size = deg r k + 1 := by
  unfold fArray
  rw [size_mulOneMinusQPow, Array.size_map]
  exact size_hilbertArray r k

/-- `bpsCoeffs` has size `deg r k + 1` (length of the BPS polynomial). -/
theorem size_bpsCoeffs (r k : ℕ) : (bpsCoeffs r k).size = deg r k + 1 := by
  unfold bpsCoeffs
  simp [Array.size_ofFn]

/-! ## Hook-length identities -/

/-- A hook list has one entry per box: `length = parts.sum`. -/
theorem hooksOf_length (parts : List ℕ) : (hooksOf parts).length = parts.sum := by
  have hlen :
      ((parts.zipIdx).flatMap fun (a, i) =>
        (List.range a).map fun j =>
          a - j + ((parts.filter (· > j)).length) - i - 1).length
        = ((parts.zipIdx).map fun p => p.1).sum := by
    rw [List.length_flatMap]
    -- `((parts.zipIdx).map fun (a,i) => ((List.range a).map …).length).sum`
    have hmap : (parts.zipIdx).map
          (fun p =>
            ((List.range p.1).map fun j =>
              p.1 - j + ((parts.filter (· > j)).length) - p.2 - 1).length)
        = (parts.zipIdx).map fun p => p.1 := by
      apply List.map_congr_left
      intro p _hp
      rcases p with ⟨a, i⟩
      simp [List.length_map, List.length_range]
    rw [hmap]
  have hfst : ((parts.zipIdx).map fun p => p.1) = parts :=
    List.zipIdx_map_fst 0 parts
  rw [hooksOf, hlen, hfst]

/-- `hooksOf` for a part-list summing to `r` has length `r`. -/
theorem hooksOf_length_eq (r : ℕ) {parts : List ℕ} (h : parts.sum = r) :
    (hooksOf parts).length = r := by
  rw [hooksOf_length, h]

/-- `dimOf` is the hook-length formula `r! / Π hooks` by definition. -/
theorem dimOf_eq (r : ℕ) (parts : List ℕ) :
    dimOf r parts = r.factorial / (hooksOf parts).prod := rfl

/-- For a `Part r`, the computational dimension agrees with `Part.dim`. -/
theorem dimOf_eq_dim {r : ℕ} (p : Part r) :
    dimOf r p.parts = p.dim := by
  show r.factorial / (hooksOf p.parts).prod = r.factorial / p.hooks.prod
  rfl

/-! ## First coefficients and endpoint values -/

/-- `signedChoose h 0 = 1`. -/
@[simp] theorem signedChoose_zero (h : ℕ) : signedChoose h 0 = 1 := by
  simp [signedChoose]

/-- A `set!` at a positive index does not change entry `0`. -/
theorem getZero_setBang {α : Type*} [Inhabited α] {t : Array α} {j : ℕ} {v : α}
    (hj : 0 < j) : (t.set! j v)[0]! = t[0]! := by
  have hset : t.set! j v = t.setIfInBounds j v := rfl
  rw [hset]
  have hne : j ≠ 0 := Nat.ne_of_gt hj
  have key := Array.getElem?_setIfInBounds_ne (xs := t) (i := j) (j := 0) hne (a := v)
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, key]

/-- Setting index `0` of an array of positive length yields the inserted value. -/
theorem getZero_setBang_self {α : Type*} [Inhabited α] {t : Array α} {v : α}
    (ht : 0 < t.size) : (t.set! 0 v)[0]! = v := by
  have hset : t.set! 0 v = t.setIfInBounds 0 v := rfl
  rw [hset]
  have key := Array.getElem?_setIfInBounds_self_of_lt (xs := t) (i := 0) (a := v) ht
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, key]
  simp

/-- `diffOnce` does not change the constant coefficient. -/
theorem diffOnce_getZero {H : Array ℤ} :
    (diffOnce H)[0]! = H[0]! := by
  have key : ∀ (js : List ℕ) (acc : Array ℤ), acc[0]! = H[0]! →
      (js.foldl (init := acc) fun acc j =>
        acc.set! (j + 1) (H[j + 1]! - H[j]!))[0]! = H[0]! := by
    intro js
    induction js with
    | nil => intro acc hacc; simpa using hacc
    | cons j js ih =>
      intro acc hacc
      rw [List.foldl_cons]
      apply ih
      rw [getZero_setBang]
      · exact hacc
      · omega
  unfold diffOnce
  exact key _ _ rfl

/-- `mulOneMinusQPow` does not change the constant coefficient. -/
theorem mulOneMinusQPow_getZero {H : Array ℤ} (r : ℕ) :
    (mulOneMinusQPow H r)[0]! = H[0]! := by
  have key : ∀ (js : List ℕ) (acc : Array ℤ), acc[0]! = H[0]! →
      (js.foldl (fun H _ => diffOnce H) acc)[0]! = H[0]! := by
    intro js
    induction js with
    | nil => intro acc hacc; simpa using hacc
    | cons _ js ih =>
      intro acc hacc
      rw [List.foldl_cons]
      apply ih
      rw [diffOnce_getZero]; exact hacc
  unfold mulOneMinusQPow
  exact key (List.range r) H rfl

/-- `geomStep` does not change entry `0` when the hook length is positive. -/
theorem geomStep_getZero {t : Array ℕ} {a : ℕ} (ha : 0 < a) :
    (geomStep t a)[0]! = t[0]! := by
  have key : ∀ (js : List ℕ) (acc : Array ℕ), acc[0]! = t[0]! →
      (js.foldl (init := acc) fun t j => t.set! (a + j) (t[a + j]! + t[j]!))[0]! = t[0]! := by
    intro js
    induction js with
    | nil => intro acc hacc; simpa using hacc
    | cons j js ih =>
      intro acc hacc
      rw [List.foldl_cons]
      apply ih
      rw [getZero_setBang]
      · exact hacc
      · have : 0 < a + j := Nat.lt_of_lt_of_le ha (Nat.le_add_right a j); omega
  unfold geomStep
  exact key _ _ rfl

/-- `geomSeries` has constant coefficient 1 when `len > 0` and all hook lengths are positive. -/
theorem geomSeries_getZero {hooks : List ℕ} {len : ℕ} (hlen : 0 < len)
    (hpos : ∀ a ∈ hooks, 0 < a) :
    (geomSeries hooks len)[0]! = 1 := by
  have key : ∀ (hs : List ℕ) (acc : Array ℕ),
      (∀ a ∈ hs, 0 < a) → acc[0]! = 1 →
      (hs.foldl geomStep acc)[0]! = 1 := by
    intro hs
    induction hs with
    | nil => intro acc _ hacc; simpa using hacc
    | cons a as ih =>
      intro acc hpos' hacc
      rw [List.foldl_cons]
      apply ih
      · intro b hb; exact hpos' b (List.mem_cons_of_mem _ hb)
      · rw [geomStep_getZero]
        · exact hacc
        · exact hpos' a List.mem_cons_self
  unfold geomSeries
  apply key
  · exact hpos
  · have hsz : 0 < (Array.replicate len 0).size := by
      simpa [Array.size_replicate] using hlen
    exact getZero_setBang_self hsz

/-! ## The one-column partition `1^r` -/

/-- `zipIdx` of the all-ones column. -/
theorem zipIdx_replicate_one (r i : ℕ) :
    (List.replicate r 1).zipIdx i = (List.range r).map (fun j => (1, i + j)) := by
  induction r generalizing i with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.zipIdx_cons, ih (i + 1)]
    have hr : List.range (n + 1) = 0 :: (List.range n).map (· + 1) := by
      rw [List.range_succ_eq_map]
    rw [hr, List.map_cons]
    simp [List.map_map, Nat.add_comm, Nat.add_left_comm]

/-- Column length of the all-ones column. -/
theorem colLen_replicate_one (r j : ℕ) :
    ((List.replicate r 1).filter (· > j)).length = if j = 0 then r else 0 := by
  rw [List.filter_replicate]
  by_cases hj : j = 0
  · subst hj
    simp
  · have hgt : ((1 : ℕ) > j) = false := by
      simp
      omega
    simp [hgt, hj]

/-- Hooks of the one-column partition are `r, r-1, …, 1`. -/
theorem hooksOf_replicate_one (r : ℕ) :
    hooksOf (List.replicate r 1) = (List.range r).map (fun j => r - j) := by
  unfold hooksOf
  rw [zipIdx_replicate_one r 0]
  simp only [List.flatMap_map]
  have h : ∀ i : ℕ, ((List.range 1).map fun j =>
      1 - j + ((List.replicate r 1).filter (· > j)).length - i - 1) = [r - i] := by
    intro i
    have h1 : List.range 1 = [0] := rfl
    rw [h1]
    simp only [List.map_cons, List.map_nil]
    have h0 : (1 : ℕ) - 0 + ((List.replicate r 1).filter (· > 0)).length - i - 1 = r - i := by
      rw [colLen_replicate_one]
      simp
      omega
    rw [h0]
  simp only [h]
  simp only [Nat.zero_add]
  rw [← List.map_eq_flatMap]

/-- Product of the one-column hooks is `r!`. -/
theorem prod_hooks_replicate_one (r : ℕ) :
    ((List.range r).map (fun j => r - j)).prod = r.factorial := by
  induction r with
  | zero => simp
  | succ n ih =>
    have h : (List.range (n + 1)).map (fun j => (n + 1) - j)
        = (n + 1) :: (List.range n).map (fun j => n - j) := by
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      have : ((fun j : ℕ => (n + 1) - j) ∘ (· + 1)) = fun j : ℕ => n - j := by
        funext x
        show (n + 1) - (x + 1) = n - x
        omega
      rw [this]
      simp
    rw [h, List.prod_cons, ih]
    simp [Nat.factorial_succ]

/-- Dimension of the one-column partition is 1. -/
theorem dimOf_replicate_one (r : ℕ) :
    dimOf r (List.replicate r 1) = 1 := by
  unfold dimOf
  rw [hooksOf_replicate_one, prod_hooks_replicate_one]
  exact Nat.div_self (Nat.factorial_pos r)

end Paper20
