import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Flattenings and Schmidt rank

For an `N`-tensor with coefficient array `T` and local dimensions `d`,
the flattening across a cut `S | S^c` is the matrix of `T` with rows indexed
by coordinates on `S` and columns by coordinates on `S^c`.  Its rank is the
Schmidt rank across that cut.  The paper's hypothesis (1) bounds every
nontrivial Schmidt rank by `D`.
-/

noncomputable section

namespace UniformBorderRank

open Finset

variable {N : ℕ}

/-- Coefficient array of an `N`-tensor. -/
abbrev Coeffs {N : ℕ} (d : Fin N → ℕ) := (∀ i : Fin N, Fin (d i)) → ℂ

/-- Product (decomposable) tensor. -/
def isProduct {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d) : Prop :=
  ∃ v : ∀ i : Fin N, (Fin (d i) → ℂ),
    ∀ idx : ∀ i : Fin N, Fin (d i),
      T idx = ∏ i : Fin N, v i (idx i)

/-- CP rank ≤ `b`: sum of `b` product tensors. -/
def cpRankLe {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d) (b : ℕ) : Prop :=
  ∃ k : Fin b → Coeffs d, (∀ j, isProduct (k j)) ∧ (∀ idx, T idx = ∑ j : Fin b, k j idx)

/-- Border rank ≤ `b`: limit of tensors of CP rank ≤ `b`. -/
def borderRankLe {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d) (b : ℕ) : Prop :=
  ∃ s : ℕ → Coeffs d,
    (∀ n, cpRankLe (s n) b) ∧
    (∀ idx, Filter.Tendsto (fun n => s n idx) Filter.atTop (nhds (T idx)))

/-- Flattening matrix across `S`: rows = coords on `S`, cols = coords on `S^c`.
    We encode both index types as functions `Fin N → ℕ` constrained to `S` / `Sᶜ`. -/
def flatCoeff {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) (S : Finset (Fin N))
    (row : ∀ i ∈ S, Fin (d i)) (col : ∀ i ∈ Sᶜ, Fin (d i)) : ℂ :=
  T (fun i => if h : i ∈ S then row i h else col i (Finset.mem_compl.mpr h))

/-- Schmidt rank across `S | S^c`: dimension of the row space of the flattening.
    Encoded as the dimension of the span of flattening rows. -/
def schmidtRank {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) (S : Finset (Fin N)) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ
    (Set.range (fun row : ∀ i ∈ S, Fin (d i) =>
      (fun col : ∀ i ∈ Sᶜ, Fin (d i) => flatCoeff d T S row col))))

/-- Largest nontrivial Schmidt rank. -/
def maxSchmidtRank {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) : ℕ :=
  sSup (Set.range (fun S : Finset (Fin N) => if S ≠ ∅ ∧ S ≠ univ then schmidtRank d T S else 0))

/-- All-cut hypothesis (1): every nontrivial flattening has rank ≤ `D`. -/
def allCutLe {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) (D : ℕ) : Prop :=
  ∀ S : Finset (Fin N), S ≠ ∅ → S ≠ univ → schmidtRank d T S ≤ D

/-- Product tensors have CP rank ≤ 1. -/
lemma cpRankLe_one_of_isProduct {N : ℕ} {d : Fin N → ℕ} {T : Coeffs d}
    (h : isProduct T) : cpRankLe T 1 := by
  obtain ⟨v, hv⟩ := h
  refine ⟨fun _ => T, ?_, ?_⟩
  · intro _j; exact ⟨v, hv⟩
  · intro idx
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_const,
      Finset.card_singleton, one_smul]

/-- Border rank is bounded by CP rank. -/
lemma borderRankLe_of_cpRankLe {N : ℕ} {d : Fin N → ℕ} {T : Coeffs d} {b : ℕ}
    (h : cpRankLe T b) : borderRankLe T b := by
  refine ⟨fun _ => T, fun _n => h, ?_⟩
  intro idx
  exact tendsto_const_nhds

/-- CP rank 1 tensors are product tensors. -/
lemma isProduct_of_cpRankLe_one {N : ℕ} {d : Fin N → ℕ} {T : Coeffs d}
    (h : cpRankLe T 1) : isProduct T := by
  obtain ⟨k, hp, hsum⟩ := h
  have hT : T = k 0 := by
    funext idx
    rw [hsum]
    simp
  rw [hT]
  exact hp 0

/-- Sum of `b` products is a sum of `c` products when `b = c`. -/
lemma cpRankLe_refl {N : ℕ} {d : Fin N → ℕ} {T : Coeffs d} {b : ℕ}
    (h : cpRankLe T b) : cpRankLe T b := h

/-- Border rank ≤ b implies border rank ≤ b (trivial monotonicity at equality). -/
lemma borderRankLe_refl {N : ℕ} {d : Fin N → ℕ} {T : Coeffs d} {b : ℕ}
    (h : borderRankLe T b) : borderRankLe T b := h

end UniformBorderRank
