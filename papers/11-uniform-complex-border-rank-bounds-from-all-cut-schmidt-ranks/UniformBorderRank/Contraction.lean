import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import UniformBorderRank.Flattening

/-!
# Lemma 2.1: Faithful product contraction (coefficient model)

`contractCoeffs T J b u_J = ∑_{u_K} T(u_J,u_K) ∏_{i∈K} b_i(u_K i)`.

Coefficient contraction is linear in `T`, with its restriction to any subspace
`E`. The complete rank-growth proof and Lemma 2.1 are in `Faithful.lean`.
No `sorry` in this file.
-/

noncomputable section

namespace UniformBorderRank

open Finset

/-- Complementary multi-indices to `J`. -/
abbrev CompIndex {N : ℕ} (d : Fin N → ℕ) (J : Finset (Fin N)) : Type :=
  ∀ i : (Jᶜ : Finset (Fin N)), Fin (d i)

/-- Product contraction on the coefficient model. -/
def contractCoeffs {N : ℕ} {d : Fin N → ℕ}
    (T : Coeffs d) (J : Finset (Fin N))
    (b : ∀ i : Fin N, Fin (d i) → ℂ) : (∀ i : J, Fin (d i)) → ℂ :=
  fun uJ =>
    ∑ uK : CompIndex d J,
      T (fun i => if h : i ∈ J then uJ ⟨i, h⟩ else uK ⟨i, Finset.mem_compl.mpr h⟩)
        * (∏ i : (Jᶜ : Finset (Fin N)), b i (uK i))

lemma contractCoeffs_add {N : ℕ} {d : Fin N → ℕ}
    (T U : Coeffs d) (J : Finset (Fin N))
    (b : ∀ i : Fin N, Fin (d i) → ℂ) :
    contractCoeffs (T + U) J b = contractCoeffs T J b + contractCoeffs U J b := by
  funext uJ
  simp only [contractCoeffs, Pi.add_apply, add_mul, Finset.sum_add_distrib]
lemma contractCoeffs_smul {N : ℕ} {d : Fin N → ℕ}
    (c : ℂ) (T : Coeffs d) (J : Finset (Fin N))
    (b : ∀ i : Fin N, Fin (d i) → ℂ) :
    contractCoeffs (c • T) J b = c • contractCoeffs T J b := by
  funext uJ
  simp only [contractCoeffs, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
def contractLinearMap {N : ℕ} {d : Fin N → ℕ}
    (J : Finset (Fin N)) (b : ∀ i : Fin N, Fin (d i) → ℂ) :
    Coeffs d →ₗ[ℂ] ((∀ i : J, Fin (d i)) → ℂ) where
  toFun T := contractCoeffs T J b
  map_add' T U := contractCoeffs_add T U J b
  map_smul' c T := contractCoeffs_smul c T J b
def contractOn {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N))
    (b : ∀ i : Fin N, Fin (d i) → ℂ) :
    E →ₗ[ℂ] ((∀ i : J, Fin (d i)) → ℂ) :=
  (contractLinearMap J b).comp E.subtype

/-- **Lemma 2.1 (statement), coefficient form.**
    If `dim E = r ≥ 1`, there are `J` with `|J| ≤ r-1` and `b` such that
    `fun T : E => contractCoeffs T J b` is injective. -/
def faithful_product_contraction {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (r : ℕ) : Prop :=
  r = Module.finrank ℂ E ∧ 1 ≤ r →
  ∃ (J : Finset (Fin N)) (b : ∀ i : Fin N, Fin (d i) → ℂ),
    J.card ≤ r - 1 ∧
    Function.Injective (fun T : E => contractCoeffs T.val J b)


/-- Rank of `contractOn` as a function of `J` and `b`:
    `d(J) = finrank (range (contractOn E J b))`. -/
def contractRank {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N))
    (b : ∀ i : Fin N, Fin (d i) → ℂ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (contractOn E J b))

/-- Maximum rank over all covector choices `b` for a fixed `J`:
    `d(J) = max_b contractRank E J b`. -/
def maxContractRank {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N)) : ℕ :=
  sSup { contractRank E J b | b : ∀ i : Fin N, Fin (d i) → ℂ }

lemma contractCoeffs_univ {N : ℕ} {d : Fin N → ℕ}
    (T : Coeffs d) (b : ∀ i : Fin N, Fin (d i) → ℂ)
    (u : ∀ i : (univ : Finset (Fin N)), Fin (d i)) :
    contractCoeffs T univ b u = T (fun i => u ⟨i, mem_univ i⟩) := by
  classical
  haveI : IsEmpty ↥((univ : Finset (Fin N))ᶜ) :=
    ⟨fun i => (Finset.mem_compl.mp i.property) (mem_univ i.val)⟩
  haveI : Unique (CompIndex d (univ : Finset (Fin N))) := Pi.uniqueOfIsEmpty _
  simp [contractCoeffs]

lemma contractOn_univ_injective {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (b : ∀ i : Fin N, Fin (d i) → ℂ) :
    Function.Injective (contractOn E univ b) := by
  intro T U h
  apply Subtype.ext
  funext u
  have h' := congrFun h (fun i => u i)
  simpa [contractOn, contractLinearMap, contractCoeffs_univ] using h'

lemma contractRank_le {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N))
    (b : ∀ i : Fin N, Fin (d i) → ℂ) :
    contractRank E J b ≤ Module.finrank ℂ E :=
  LinearMap.finrank_range_le _

lemma contractRank_univ {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d))
    (b : ∀ i : Fin N, Fin (d i) → ℂ) :
    contractRank E (univ : Finset (Fin N)) b = Module.finrank ℂ E := by
  exact LinearEquiv.finrank_eq
    (LinearEquiv.ofInjective (contractOn E univ b) (contractOn_univ_injective E b)).symm

lemma contractRank_empty_le {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d))
    (b : ∀ i : Fin N, Fin (d i) → ℂ) :
    contractRank E (∅ : Finset (Fin N)) b ≤ 1 := by
  exact (LinearMap.range (contractOn E ∅ b)).finrank_le.trans_eq (by simp)

lemma maxContractRank_le {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N)) :
    maxContractRank E J ≤ Module.finrank ℂ E := by
  apply csSup_le
  · exact ⟨_, ⟨0, rfl⟩⟩
  · rintro _ ⟨b, rfl⟩
    exact contractRank_le E J b

lemma contractRank_le_max {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N))
    (b : ∀ i : Fin N, Fin (d i) → ℂ) :
    contractRank E J b ≤ maxContractRank E J := by
  apply le_csSup
  · exact ⟨Module.finrank ℂ E, by rintro _ ⟨b, rfl⟩; exact contractRank_le E J b⟩
  · exact ⟨b, rfl⟩

lemma maxContractRank_attained {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N)) :
    ∃ b : ∀ i : Fin N, Fin (d i) → ℂ, contractRank E J b = maxContractRank E J := by
  have hn : Set.Nonempty {contractRank E J b | b : ∀ i : Fin N, Fin (d i) → ℂ} :=
    ⟨_, ⟨0, rfl⟩⟩
  have hb : BddAbove {contractRank E J b | b : ∀ i : Fin N, Fin (d i) → ℂ} :=
    ⟨Module.finrank ℂ E, by rintro _ ⟨b, rfl⟩; exact contractRank_le E J b⟩
  obtain ⟨b, hb⟩ := Nat.sSup_mem hn hb
  exact ⟨b, hb⟩

lemma maxContractRank_univ {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) :
    maxContractRank E univ = Module.finrank ℂ E := by
  apply le_antisymm (maxContractRank_le E univ)
  simpa only [contractRank_univ] using contractRank_le_max E univ 0

/-- The greedy rank-growth argument, with the growth premise explicit. -/
lemma growth_steps_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (step : Finset ι → ℕ)
    (h0 : step ∅ = 1) (hbound : ∀ J, step J ≤ r)
    (hgrow : ∀ J, step J < r → ∃ i ∉ J, step J < step (insert i J)) :
    ∃ J : Finset ι, J.card ≤ r - 1 ∧ step J = r := by
  suffices h : ∀ k : ℕ, k ≤ r - 1 →
      ∃ J : Finset ι, J.card ≤ k ∧ (step J = r ∨ k + 1 ≤ step J) by
    obtain ⟨J, hJ, hs⟩ := h (r - 1) le_rfl
    refine ⟨J, hJ, ?_⟩
    have hr : 1 ≤ r := by have := hbound ∅; omega
    rcases hs with hs | hs
    · exact hs
    · have := hbound J; omega
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨∅, by simp, Or.inr (by omega)⟩
  | succ k ih =>
    intro hk
    obtain ⟨J, hJ, hs⟩ := ih (by omega)
    by_cases hfull : step J = r
    · exact ⟨J, by omega, Or.inl hfull⟩
    · obtain ⟨i, hi, hinc⟩ := hgrow J (lt_of_le_of_ne (hbound J) hfull)
      refine ⟨insert i J, ?_, Or.inr ?_⟩
      · rw [card_insert_of_notMem hi]; omega
      · rcases hs with hs | hs <;> omega

end UniformBorderRank
