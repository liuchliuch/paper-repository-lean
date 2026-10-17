import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import UniformBorderRank.FdExpand
import UniformBorderRank.FdLimit
import UniformBorderRank.FdRank

/-!
# Assembly of `borderRankLe (prodCurveCoeff) (k+1)` (paper (13))

Per-subset Tendsto of finite-difference terms, then `tendsto_finset_sum`.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace UniformBorderRank

open Filter Finset

/-- `ε_n = ((n+1 : ℕ) : ℂ)⁻¹` tends to `0`. -/
lemma tendsto_eps_inv_complex :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℂ)⁻¹)) atTop (nhds 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  have hnorm : (fun n : ℕ => ‖(((n + 1 : ℕ) : ℂ)⁻¹)‖)
      = (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) := by
    funext n
    have h1 : ‖(((n + 1 : ℕ) : ℂ)⁻¹)‖ = ‖(((n + 1 : ℕ) : ℂ))‖⁻¹ := norm_inv _
    have h2 : ‖(((n + 1 : ℕ) : ℂ))‖ = (((n + 1 : ℕ) : ℝ)) := by
      have hcast : ((n + 1 : ℕ) : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) := by
        rw [Complex.ofReal_natCast]
      rw [hcast, Complex.norm_real, Real.norm_of_nonneg]
      · exact_mod_cast (Nat.zero_le (n + 1))
    rw [h1, h2]
  rw [hnorm]
  exact tendsto_inv_add_one

/-- `ε_n` is nonzero for every `n`. -/
lemma eps_inv_complex_ne_zero (n : ℕ) : (((n + 1 : ℕ) : ℂ)⁻¹) ≠ 0 :=
  eps_inv_ne_zero n

/-- `c * ε_n ^ m → 0` when `m > 0`. -/
lemma tendsto_const_mul_pow_zero (c : ℂ) (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℂ)⁻¹) ^ m * c) atTop (nhds 0) := by
  have hbase := tendsto_eps_inv_complex
  have hpow : Tendsto (fun x : ℂ => x ^ m) (nhds 0) (nhds ((0 : ℂ) ^ m)) :=
    (continuous_pow m).continuousAt.tendsto
  have h0p : (0 : ℂ) ^ m = 0 := zero_pow (by omega : m ≠ 0)
  rw [h0p] at hpow
  have h := (hpow.comp hbase).mul_const c
  -- h : Tendsto (fun n => ε_n^m * c) atTop (nhds (0 * c))
  have h0c : (0 : ℂ) * c = 0 := by ring
  rw [h0c] at h
  exact h

/-- Each subset term of `fdApprox` along `ε_n` tends to
    `if A.card = k then eS A else 0`. -/
lemma tendsto_fdTerm {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (k : ℕ) (idx : ∀ i, Fin (d i))
    (A : Finset (Fin N)) :
    Tendsto
      (fun n : ℕ =>
        ((1 : ℂ) / (Nat.factorial k : ℂ)) * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ k)⁻¹
          * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ A.card
              * eS d v w idx A * UniformBorderRank.S A.card k))
      atTop
      (nhds (if A.card = k then eS d v w idx A else 0)) := by
  by_cases hlt : A.card < k
  · have hz : ∀ n : ℕ,
        ((1 : ℂ) / (Nat.factorial k : ℂ)) * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ k)⁻¹
          * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ A.card
              * eS d v w idx A * UniformBorderRank.S A.card k) = 0 := by
      intro n
      exact fdTerm_lt d v w k (((n + 1 : ℕ) : ℂ)⁻¹) idx A hlt
    have hif : (if A.card = k then eS d v w idx A else 0) = 0 := by
      rw [if_neg (by omega : ¬A.card = k)]
    rw [hif]
    have : (fun n : ℕ =>
        ((1 : ℂ) / (Nat.factorial k : ℂ)) * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ k)⁻¹
          * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ A.card
              * eS d v w idx A * UniformBorderRank.S A.card k))
        = fun _ => 0 := funext hz
    rw [this]
    exact tendsto_const_nhds
  · by_cases heq : A.card = k
    · have hconst : ∀ n : ℕ,
          ((1 : ℂ) / (Nat.factorial k : ℂ)) * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ k)⁻¹
            * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ A.card
                * eS d v w idx A * UniformBorderRank.S A.card k)
          = eS d v w idx A := by
        intro n
        exact fdTerm_eq d v w k (((n + 1 : ℕ) : ℂ)⁻¹) idx A heq (eps_inv_complex_ne_zero n)
      have hif : (if A.card = k then eS d v w idx A else 0) = eS d v w idx A := by
        rw [if_pos heq]
      rw [hif]
      have : (fun n : ℕ =>
          ((1 : ℂ) / (Nat.factorial k : ℂ)) * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ k)⁻¹
            * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ A.card
                * eS d v w idx A * UniformBorderRank.S A.card k))
          = fun _ => eS d v w idx A := funext hconst
      rw [this]
      exact tendsto_const_nhds
    · have hgt : k < A.card := by omega
      have hexp : 0 < A.card - k := by omega
      have hif : (if A.card = k then eS d v w idx A else 0) = 0 := by
        rw [if_neg heq]
      rw [hif]
      set cval : ℂ := eS d v w idx A * (UniformBorderRank.S A.card k / (Nat.factorial k : ℂ))
      have hform : ∀ n : ℕ,
          ((1 : ℂ) / (Nat.factorial k : ℂ)) * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ k)⁻¹
            * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ A.card
                * eS d v w idx A * UniformBorderRank.S A.card k)
          = ((((n + 1 : ℕ) : ℂ)⁻¹) ^ (A.card - k)) * cval := by
        intro n
        have h := fdTerm_tail_form d v w k (((n + 1 : ℕ) : ℂ)⁻¹) idx A hgt
          (eps_inv_complex_ne_zero n)
        show _ = _
        exact h
      have hts := tendsto_const_mul_pow_zero cval (A.card - k) hexp
      have : (fun n : ℕ =>
          ((1 : ℂ) / (Nat.factorial k : ℂ)) * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ k)⁻¹
            * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ A.card
                * eS d v w idx A * UniformBorderRank.S A.card k))
          = (fun n : ℕ => ((((n + 1 : ℕ) : ℂ)⁻¹) ^ (A.card - k)) * cval) :=
        funext hform
      rw [this]
      exact hts


/-- The powerset sum of `fdApprox` terms tends to
    `∑_A (if A.card = k then eS A else 0)`. -/
lemma tendsto_fdApprox_sum {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (k : ℕ) (idx : ∀ i, Fin (d i)) :
    Tendsto
      (fun n : ℕ => fdApprox d v w k (((n + 1 : ℕ) : ℂ)⁻¹) idx)
      atTop
      (nhds (∑ A : Finset (Fin N), if A.card = k then eS d v w idx A else 0)) := by
  have hform : ∀ n : ℕ,
      fdApprox d v w k (((n + 1 : ℕ) : ℂ)⁻¹) idx
        = ∑ A : Finset (Fin N),
            ((1 : ℂ) / (Nat.factorial k : ℂ)) * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ k)⁻¹
              * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ A.card
                  * eS d v w idx A * UniformBorderRank.S A.card k) := by
    intro n
    exact fdApprox_eq_sum_A d v w k (((n + 1 : ℕ) : ℂ)⁻¹) idx
  have hper := tendsto_fdTerm d v w k idx
  have hsum := tendsto_finset_sum (univ : Finset (Finset (Fin N))) (fun A _ => hper A)
  -- hsum : Tendsto (fun n => ∑ A, fdTerm n A) atTop (nhds (∑ A, limit A))
  have : (fun n : ℕ => fdApprox d v w k (((n + 1 : ℕ) : ℂ)⁻¹) idx)
      = (fun n : ℕ => ∑ A : Finset (Fin N),
          ((1 : ℂ) / (Nat.factorial k : ℂ)) * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ k)⁻¹
            * ((((n + 1 : ℕ) : ℂ)⁻¹) ^ A.card
                * eS d v w idx A * UniformBorderRank.S A.card k)) :=
    funext hform
  rw [this]
  exact hsum

/-- The limit of the powerset sum is `prodCurveCoeff k idx`. -/
lemma sum_ite_card_eq {N : ℕ} (d : Fin N → ℕ)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (k : ℕ) (idx : ∀ i, Fin (d i)) :
    (∑ A : Finset (Fin N), if A.card = k then eS d v w idx A else 0)
      = prodCurveCoeff d v w k idx := by
  rw [prodCurveCoeff_eq_sum]
  have hset : (univ : Finset (Finset (Fin N))).filter (fun A => A.card = k)
      = powersetCard k (univ : Finset (Fin N)) := by
    ext A
    simp [mem_powersetCard]
  have h : ∑ A : Finset (Fin N), (if A.card = k then eS d v w idx A else 0)
      = ∑ A ∈ powersetCard k (univ : Finset (Fin N)), eS d v w idx A := by
    rw [← sum_filter, hset]
  exact h

/-- **Paper (13):** `borderRankLe (prodCurveCoeff d v w k) (k+1)` for `0 < N`. -/
theorem borderRankLe_prodCurveCoeff {N : ℕ} (d : Fin N → ℕ) (hN : 0 < N)
    (v w : ∀ i : Fin N, Fin (d i) → ℂ) (k : ℕ) :
    borderRankLe (prodCurveCoeff d v w k) (k + 1) := by
  refine ⟨fun n => fdApprox d v w k (((n + 1 : ℕ) : ℂ)⁻¹), ?_, ?_⟩
  · intro n
    exact cpRankLe_fdApprox d hN v w k _
  · intro idx
    have h := tendsto_fdApprox_sum d v w k idx
    have hlim : (∑ A : Finset (Fin N), if A.card = k then eS d v w idx A else 0)
        = prodCurveCoeff d v w k idx :=
      sum_ite_card_eq d v w k idx
    rw [hlim] at h
    exact h

end UniformBorderRank
