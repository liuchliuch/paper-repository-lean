import Paper20.Basic
import Paper20.Walks

/-!
# Paper 20 — Lemma 2.2: bounds on the BPS coefficients of `C_{r,k}`

For `r ≥ 2`, `k ≥ 1` and `0 ≤ h ≤ d = k · binom(r, 2)` the local BPS
coefficients of the `r`-fold point `C_{r,k}` satisfy

  `1 ≤ n_h(C_{r,k}) ≤ binom(2d, 2h)`,  and  `n_0 = n_d = 1`.

The proof (paper §2, Lemma 2.2) is combinatorial: a closed `w₀`-to-`w₀`
walk of length `2d` is a stay/move word, each walk is determined by its
stay-set (so at most `binom(2d, 2h)` walks have `2h` stays), and the
palindromic word `Q Q^rev` produces an admissible walk with stays at the
first `h` and last `h` letters (so at least one such walk exists).

We therefore state Lemma 2.2 for any walk-count `n` of contact-order degree
`d` (`IsWalkBPSCount`), and prove the four conclusions from the abstract
walk model of `Paper20.Walks`.  The identification of the *geometric* BPS
coefficients of `C_{r,k}` with such a walk count is the external
Hilbert–HOMFLY / Rutherford bridge (recorded as `exempt_external_dependency`
in `coverage.json`); here the walk model *is* the definition of `n_h`.

A formula-side endpoint `n_d = F_0 = 1` is also proved from the triangular
recurrence (25), independently of the walk model.
-/

namespace Paper20

open Walks

/-! ## Walk-count interface for the BPS coefficients -/

/-- `n` is a walk BPS count of contact-order degree `d` when `n h` counts the
admissible walks of a word of length `2d` having exactly `2h` stays, and the
palindromic witnesses of Lemma 2.2 are among the admissible walks. -/
def IsWalkBPSCount (n : ℕ → ℕ) (d : ℕ) : Prop :=
  ∃ adm : Walk (2 * d) → Prop,
    (∀ h, h ≤ d → adm (palindromic (2 * d) h)) ∧
      ∀ h, n h = admissibleCount adm h

/-- Every admissibility predicate containing the palindromic witnesses yields
a walk BPS count. -/
theorem isWalkBPSCount_of_adm {d : ℕ} (adm : Walk (2 * d) → Prop)
    (palin : ∀ h, h ≤ d → adm (palindromic (2 * d) h)) :
    IsWalkBPSCount (fun h => admissibleCount adm h) d :=
  ⟨adm, palin, fun _ => rfl⟩

/-! ## Lemma 2.2 for walk counts -/

variable {n : ℕ → ℕ} {d h : ℕ}

/-- Lemma 2.2, lower bound: `1 ≤ n h` for `h ≤ d`.
(The palindromic walk with `2h` stays is admissible.) -/
theorem lemma_2_2_lower (hn : IsWalkBPSCount n d) (hh : h ≤ d) : 1 ≤ n h := by
  obtain ⟨adm, palin, count⟩ := hn
  rw [count h]
  have hmem : adm (palindromic (2 * d) h) := palin h hh
  exact Nat.succ_le_of_lt (admissibleCount_pos hmem (by omega))

/-- Lemma 2.2, upper bound: `n h ≤ binom(2d, 2h)` for `h ≤ d`.
(A walk is determined by its stay-set.) -/
theorem lemma_2_2_upper (hn : IsWalkBPSCount n d) (hh : h ≤ d) :
    n h ≤ Nat.choose (2 * d) (2 * h) := by
  obtain ⟨adm, _, count⟩ := hn
  rw [count h]
  exact admissibleCount_le adm h

/-- Lemma 2.2: `n 0 = 1` (the all-move walk is the unique walk with no stays). -/
theorem lemma_2_2_n0 (hn : IsWalkBPSCount n d) : n 0 = 1 := by
  obtain ⟨adm, palin, count⟩ := hn
  rw [count 0]
  exact admissibleCount_zero (palin 0 (by omega))

/-- Lemma 2.2: `n d = 1` (the all-stay walk is the unique walk with `2d` stays). -/
theorem lemma_2_2_nd (hn : IsWalkBPSCount n d) : n d = 1 := by
  obtain ⟨adm, palin, count⟩ := hn
  rw [count d]
  exact admissibleCount_full (palin d le_rfl) (by omega)

/-- Lemma 2.2: strict positivity `0 < n h` for all `h ≤ d`
(used by Theorems 1.1 and 1.2). -/
theorem lemma_2_2_pos (hn : IsWalkBPSCount n d) : ∀ h ≤ d, 0 < n h := by
  intro h hh
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (lemma_2_2_lower hn hh)

/-- Full statement of Lemma 2.2 for a walk BPS count of degree `d`. -/
theorem lemma_2_2 (hn : IsWalkBPSCount n d) (hh : h ≤ d) :
    1 ≤ n h ∧ n h ≤ Nat.choose (2 * d) (2 * h) ∧ n 0 = 1 ∧ n d = 1 :=
  ⟨lemma_2_2_lower hn hh, lemma_2_2_upper hn hh, lemma_2_2_n0 hn, lemma_2_2_nd hn⟩

/-! ## Lemma 2.2 for `C_{r,k}` -/

/-- Lemma 2.2 in the paper's variables: for `r ≥ 2`, `k ≥ 1` and
`0 ≤ h ≤ d = k · binom(r, 2)`,

  `1 ≤ n_h(C_{r,k}) ≤ binom(2d, 2h)`,  and  `n_0 = n_d = 1`. -/
theorem lemma_2_2_C {n : ℕ → ℕ} (r k h : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hh : h ≤ deg r k) (hn : IsWalkBPSCount n (deg r k)) :
    1 ≤ n h ∧ n h ≤ Nat.choose (2 * deg r k) (2 * h) ∧ n 0 = 1 ∧ n (deg r k) = 1 :=
  lemma_2_2 hn hh

/-- Strict positivity of every BPS coefficient of `C_{r,k}` through degree `d`. -/
theorem lemma_2_2_C_pos {n : ℕ → ℕ} (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hn : IsWalkBPSCount n (deg r k)) : ∀ h ≤ deg r k, 0 < n h :=
  lemma_2_2_pos hn

/-- The contact-order degree of `C_{r,k}` is `d = k · binom(r, 2)`. -/
theorem deg_pos (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) : 0 < deg r k := by
  unfold deg
  have h1 : 0 < Nat.choose r 2 := by
    have := Nat.choose_pos (show 2 ≤ r from hr)
    exact this
  have h2 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  exact Nat.mul_pos h2 h1

/-! ## Formula-side endpoint from the triangular recurrence (25)

Equation (25) reads
  `n_h = F_{d-h} - Σ_{j=h+1}^{d} (-1)^{j-h} binom(2j, j-h) n_j`,
so at `h = d` the sum is empty and `n_d = F_0`.  The constant term of
`(1-q)^r H_{r,k}` is `F_0 = H_0 = 1`, hence `n_d = 1` already from the
formula side.  (`n_0 = 1` is harder from the recurrence alone and is taken
from the walk model above.)
-/

/-- Triangular recurrence (25) as an integer identity. -/
def SatisfiesRecurrence25 (n F : ℕ → ℕ) (d : ℕ) : Prop :=
  ∀ h ≤ d, (n h : ℤ) = (F (d - h) : ℤ) -
    ∑ j ∈ Finset.Ioc h d, (-1 : ℤ) ^ (j - h) * (Nat.choose (2 * j) (j - h) : ℤ) * (n j : ℤ)

/-- Formula-side `n_d = 1` from (25) and `F 0 = 1`. -/
theorem recurrence_n_d {n F : ℕ → ℕ} {d : ℕ}
    (hrec : SatisfiesRecurrence25 n F d) (hF0 : F 0 = 1) : n d = 1 := by
  have h := hrec d le_rfl
  have hsum : (∑ j ∈ Finset.Ioc d d,
      (-1 : ℤ) ^ (j - d) * (Nat.choose (2 * j) (j - d) : ℤ) * (n j : ℤ)) = 0 := by
    simp
  have hfd : (F (d - d) : ℤ) = (F 0 : ℤ) := by rw [Nat.sub_self]
  have key : (n d : ℤ) = (F 0 : ℤ) := by
    rw [hsum] at h
    rw [hfd] at h
    simpa using h
  have key2 : (n d : ℤ) = 1 := by rwa [hF0] at key
  exact_mod_cast key2

/-- Combined walk-model and formula-side packaging of Lemma 2.2 for `C_{r,k}`:
the walk count supplies the two-sided bound and `n_0 = n_d = 1`; the recurrence
independently reproduces `n_d = 1` whenever `F 0 = 1`. -/
theorem lemma_2_2_package {n : ℕ → ℕ} {d h : ℕ} (hn : IsWalkBPSCount n d)
    (hh : h ≤ d) (F : ℕ → ℕ) (hF0 : F 0 = 1) :
    1 ≤ n h ∧ n h ≤ Nat.choose (2 * d) (2 * h) ∧ n 0 = 1 ∧ n d = 1 ∧
      (SatisfiesRecurrence25 n F d → n d = 1) := by
  refine ⟨lemma_2_2_lower hn hh, lemma_2_2_upper hn hh, lemma_2_2_n0 hn,
    lemma_2_2_nd hn, ?_⟩
  intro hrec
  exact recurrence_n_d hrec hF0

end Paper20
