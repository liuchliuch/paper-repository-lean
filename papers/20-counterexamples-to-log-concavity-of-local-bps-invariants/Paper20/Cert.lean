import Mathlib.Data.List.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Triangular recurrence (25) — pure functional, kernel-reducible

`extract F = n` implements Appendix A's loop with incremental binomials
`C(2h,j+1) = C(2h,j)·(2h-j)/(j+1)` and pure `Array` state passing.

All recursion is structural (fuel), so `decide` can kernel-reduce the checker.
-/

namespace Paper20.Cert

/-- Inner loop with structural fuel: subtract `n_h · C(2h,j)` (sign in `c`). -/
def bump (H : Array Int) (ell h maxJ : ℕ) (fuel j : ℕ) (c : Int) : Array Int :=
  match fuel with
  | 0 => H
  | fuel + 1 =>
    if j > maxJ then H
    else
      let sign : Int := if j % 2 = 0 then 1 else -1
      let idx := ell + j
      let H := H.set! idx (H.getD idx 0 - sign * c)
      let c' : Int := if j < 2 * h then c * ((2 * h - j : Nat) : Int) / ((j + 1 : Nat) : Int) else c
      bump H ell h maxJ fuel (j + 1) c'

/-- Outer loop over `ell = 0..d` (structural fuel). -/
def extractGo (d fuel : ℕ) (ell : ℕ) (H n : Array Int) : Array Int :=
  match fuel with
  | 0 => n
  | fuel + 1 =>
    if ell > d then n
    else
      let h := d - ell
      let nh := H.getD ell 0
      let n := n.set! h nh
      let maxJ := min (2 * h) (d - ell)
      let H := bump H ell h maxJ (maxJ + 1) 0 nh
      extractGo d fuel (ell + 1) H n

/-- Extract `n_0..n_d` from residual `F` by (25). -/
def extract (F : Array Int) : Array Int :=
  extractGo (F.size - 1) F.size 0 F (Array.replicate F.size 0)

/-- `true` iff `n` agrees with `extract F`. -/
def checkRecurrence (F n : Array Int) : Bool :=
  (extract F).isEqv n (fun a b => a == b)

/-- Positivity. -/
def allPos (xs : Array Int) : Bool := xs.all (fun x => 0 < x)

/-! ## Equation (25), closed form -/

/-- Signed binomial coefficient `(-1)^{i-h} · C(2i, i-h)` of (25). -/
def coeff25 (h i : ℕ) : Int :=
  if i ≤ h then 0
  else
    ((-1 : Int) ^ (i - h)) * (Nat.choose (2 * i) (i - h) : Int)

/-- Equation (25) at index `h` for sequences of length `d+1`:
`n_h = F_{d-h} - Σ_{j=h+1}^{d} (-1)^{j-h} C(2j, j-h) n_j`. -/
def eq25 (F n : List Int) (h : ℕ) : Prop :=
  (n[h]?).getD 0 =
    (F[F.length - 1 - h]?).getD 0 -
      ((List.range (F.length - 1 - h)).foldl (fun s t =>
        s + coeff25 h (h + 1 + t) * (n[h + 1 + t]?).getD 0) 0)

/-- The full triangular system (25) through degree `d = F.length - 1`. -/
def satisfies25 (F n : List Int) : Prop :=
  n.length = F.length ∧ ∀ h, h < F.length → eq25 F n h

end Paper20.Cert
