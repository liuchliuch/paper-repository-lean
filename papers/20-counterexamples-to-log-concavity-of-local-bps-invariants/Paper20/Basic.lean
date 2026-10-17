import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Order.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Paper 20 — combinatorial core

Partitions of an integer as weakly decreasing positive lists, Young-diagram
hook lengths (zero-based rows and columns, as in Appendix A), content,
`ν`, and the hook-length dimension `f^λ`.
-/

namespace Paper20

/-- A partition of `n` as a weakly decreasing list of positive parts. -/
structure Part (n : ℕ) where
  parts : List ℕ
  sorted : parts.Pairwise (· ≥ ·)
  pos : ∀ x ∈ parts, 0 < x
  sum_eq : parts.sum = n

namespace Part

variable {n : ℕ} (p : Part n)

/-- The `i`-th part (0-based), or `0` out of range. -/
def get (i : ℕ) : ℕ := p.parts.getD i 0

/-- Column length `#{rows with part > j}` (0-based `j`). -/
def colLen (j : ℕ) : ℕ := (p.parts.filter (· > j)).length

/-- All hook lengths (zero-based box coordinates). -/
def hooks : List ℕ :=
  (p.parts.zipIdx).flatMap fun (a, i) =>
    (List.range a).map fun j => a - j + p.colLen j - i - 1

/-- `ν(λ) = Σ_i i · λ_i` with 0-based row index. -/
def nu : ℕ := (p.parts.zipIdx).foldl (fun acc (a, i) => acc + i * a) 0

/-- Content `c_λ = Σ_{(i,j)∈λ} (j-i)`. -/
def content : ℤ :=
  (p.parts.zipIdx).foldl (fun acc (a, i) =>
    acc + ((a * (a - 1) / 2 : ℕ) : ℤ) - ((i * a : ℕ) : ℤ)) 0

/-- Number of even hook lengths. -/
def evenHooks : ℕ := p.hooks.countP (fun a => a % 2 == 0)

/-- Hook-length dimension `f^λ = n! / Π_□ h_□`. -/
def dim : ℕ := n.factorial / p.hooks.prod

/-- Total hook sum. -/
def hookSum : ℕ := p.hooks.sum

end Part

/-- One-row partition of `n+1`. -/
def oneRow (n : ℕ) : Part (n + 1) where
  parts := [n + 1]
  sorted := by simp
  pos := by
    intro x hx
    simp at hx
    omega
  sum_eq := by simp

/-- One-column partition of `n+1` (`n+1` rows of length 1). -/
def oneCol (n : ℕ) : Part (n + 1) where
  parts := List.replicate (n + 1) 1
  sorted := by
    induction n with
    | zero =>
      simp [List.replicate]
    | succ m ih =>
      have h1 : List.replicate (m + 2) 1 = 1 :: List.replicate (m + 1) 1 := by
        simp [List.replicate]
      rw [h1]
      constructor
      · intro y hy
        have : y ∈ List.replicate (m + 1) 1 := by
          simp [List.mem_replicate] at hy ⊢
          exact hy
        simp [List.mem_replicate] at this
        omega
      · simpa [List.replicate] using ih
  pos := by
    intro x hx
    simp [List.mem_replicate] at hx
    omega
  sum_eq := by
    show (List.replicate (n + 1) 1).sum = n + 1
    rw [List.sum_const_nat]
    simp

/-- `d = k * binom r 2` from equation (3). -/
def deg (r k : ℕ) : ℕ := k * Nat.choose r 2

@[simp] theorem deg_eq (r k : ℕ) : deg r k = k * Nat.choose r 2 := rfl

end Paper20
