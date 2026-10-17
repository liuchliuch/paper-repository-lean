/-
Copyright (c) 2026. Fixed input support and feasible response tables
(Proposition 4.1).
-/
import Paper06.Basic
import Paper06.Conditioning
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Set BigOperators
open scoped Classical

namespace Paper06

/-! ### Sampling-without-replacement bound `L(M,k)` -/

/-- Sampling-without-replacement bound `L(M,k) = log(M^k / (M)_k)`. -/
noncomputable def LboundM (M k : ℕ) : ℝ :=
  log (((M : ℝ) ^ k) / (Nat.descFactorial M k : ℝ))

/-- `LboundM` coincides with the unrestricted bound `L(n,k)` of Proposition 2.2. -/
theorem LboundM_eq_Lbound (n k : ℕ) : LboundM n k = Lbound n k := rfl

/-- **Proposition 4.1**, the sampling bound nonnegativity. -/
theorem prop_4_1_Lbound_nonneg (M k : ℕ) (hk : 1 ≤ k) (hM : k < M) :
    0 ≤ (k * (k - 1) : ℝ) / (2 * (M - k + 1)) := by
  have hk1 : (0:ℝ) ≤ k - 1 := by
    have : (1:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hk0 : (0:ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  have hn1 : (0:ℝ) < M - k + 1 := by
    have : (k:ℝ) < M := by exact_mod_cast hM
    linarith
  positivity

/-- **Proposition 4.1**, simultaneous nonnegativity form. -/
theorem prop_4_1_simultaneous (M : ℕ) (hM : 0 < M) :
    ∀ k : ℕ, 1 ≤ k → k < M →
      0 ≤ (k * (k - 1) : ℝ) / (2 * (M - k + 1)) := by
  intro k hk hMk
  exact prop_4_1_Lbound_nonneg M k hk hMk

/-- When `s = 1`, `L(M,k)` becomes the unrestricted bound `L(n,k)`. -/
theorem prop_4_1_s_eq_one (n k : ℕ) : LboundM n k = Lbound n k := rfl

/-! ### Table law `q_λ` -/

/-- Table law `q_λ(x,a) = π(x) · (1/M) · ∑_j 1{λ_j(x) = a}`.
    The construction does not depend on the sample size `k`. -/
noncomputable def tableLaw {X A : Type*} [Fintype X] [Fintype A]
    (π : X → ℝ) (M : ℕ) (tables : Fin M → (X → A))
    (x : X) (a : A) : ℝ :=
  π x * (1 / (M : ℝ)) * (∑ j : Fin M, if tables j x = a then (1:ℝ) else 0)

/-- The table-induced law has nonnegative weights. -/
theorem tableLaw_nonneg {X A : Type*} [Fintype X] [Fintype A]
    (π : X → ℝ) (hπ : ∀ x, 0 ≤ π x) (M : ℕ) (hM : 0 < M)
    (tables : Fin M → (X → A)) (x : X) (a : A) :
    0 ≤ tableLaw π M tables x a := by
  unfold tableLaw
  have hsum : (0:ℝ) ≤ ∑ j : Fin M, if tables j x = a then (1:ℝ) else 0 := by
    refine Finset.sum_nonneg ?_
    intro j _
    by_cases h : tables j x = a
    · simp [h]
    · simp [h]
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hMne : (M:ℝ) ≠ 0 := ne_of_gt hM0
  have hinv : (0:ℝ) ≤ 1 / (M:ℝ) := by positivity
  have hπx : (0:ℝ) ≤ π x := hπ x
  have hmul : (0:ℝ) ≤ π x * (1 / (M:ℝ)) := mul_nonneg hπx hinv
  exact mul_nonneg hmul hsum

/-- For each fixed response row `p`, exactly one output `a` satisfies `p = a`. -/
theorem sum_ite_eq_one {A : Type*} [Fintype A] (p : A) :
    (∑ a : A, if p = a then (1:ℝ) else 0) = 1 := by
  classical
  rw [Finset.sum_eq_single p]
  · simp
  · intro b _ hb
    have hne : ¬ (p = b) := fun he => hb he.symm
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ p) h

/-- **Table-law input marginal = π.**
For every input `x`, the output marginal of `q_λ` is exactly `π x`,
independently of the response tables. Requires `M > 0`. -/
theorem tableLaw_marginal {X A : Type*} [Fintype X] [Fintype A]
    (π : X → ℝ) (M : ℕ) (hM : 0 < M)
    (tables : Fin M → (X → A)) (x : X) :
    ∑ a : A, tableLaw π M tables x a = π x := by
  have hMne : (M:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  -- Factor the constants out of the `a`-sum.
  have hfactor : (∑ a : A, π x * (1 / (M : ℝ))
        * (∑ j : Fin M, if tables j x = a then (1:ℝ) else 0))
      = π x * (1 / (M : ℝ))
        * (∑ a : A, ∑ j : Fin M, if tables j x = a then (1:ℝ) else 0) := by
    rw [← Finset.mul_sum]
  -- Swap the two finite sums.
  have hswap : (∑ a : A, ∑ j : Fin M, if tables j x = a then (1:ℝ) else 0)
      = ∑ j : Fin M, (∑ a : A, if tables j x = a then (1:ℝ) else 0) :=
    Finset.sum_comm
  -- Each inner `a`-sum equals 1.
  have hinner : ∀ j : Fin M, (∑ a : A, if tables j x = a then (1:ℝ) else 0) = 1 :=
    fun j => sum_ite_eq_one (tables j x)
  -- `∑ j, 1 = M`.
  have hcard : (∑ _j : Fin M, (1:ℝ)) = (M:ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  calc ∑ a : A, tableLaw π M tables x a
      = ∑ a : A, π x * (1 / (M : ℝ))
          * (∑ j : Fin M, if tables j x = a then (1:ℝ) else 0) := rfl
    _ = π x * (1 / (M : ℝ))
          * (∑ a : A, ∑ j : Fin M, if tables j x = a then (1:ℝ) else 0) := hfactor
    _ = π x * (1 / (M : ℝ))
          * (∑ j : Fin M, (∑ a : A, if tables j x = a then (1:ℝ) else 0)) := by
              rw [hswap]
    _ = π x * (1 / (M : ℝ)) * (∑ _j : Fin M, (1:ℝ)) := by
              rw [Finset.sum_congr rfl (fun j _ => hinner j)]
    _ = π x * (1 / (M : ℝ)) * (M:ℝ) := by rw [hcard]
    _ = π x * ((1 / (M : ℝ)) * (M:ℝ)) := mul_assoc _ _ _
    _ = π x * 1 := by rw [div_mul_cancel₀ _ hMne]
    _ = π x := mul_one _

/-! ### Table law as a `FinProb` on `X × A` -/

/-- The table law `q_λ` assembled as a probability law on `X × A`.
    The construction of this law (hence of the mixing distribution `μ`)
    does not depend on the sample size `k`. -/
noncomputable def tableLawFinProb {X A : Type*} [Fintype X] [Fintype A]
    (π : X → ℝ) (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (M : ℕ) (hM : 0 < M) (tables : Fin M → (X → A)) :
    FinProb (X × A) where
  w za := tableLaw π M tables za.1 za.2
  nonneg := by
    intro za
    exact tableLaw_nonneg π hπ M hM tables za.1 za.2
  sum_eq_one := by
    have hprod : (∑ za : X × A, tableLaw π M tables za.1 za.2)
        = ∑ x : X, ∑ a : A, tableLaw π M tables x a :=
      Fintype.sum_prod_type' (fun x a => tableLaw π M tables x a)
    rw [hprod]
    have hinner : ∀ x : X, (∑ a : A, tableLaw π M tables x a) = π x :=
      fun x => tableLaw_marginal π M hM tables x
    rw [Finset.sum_congr rfl (fun x _ => hinner x)]
    exact hπ1

theorem tableLawFinProb_w {X A : Type*} [Fintype X] [Fintype A]
    (π : X → ℝ) (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (M : ℕ) (hM : 0 < M) (tables : Fin M → (X → A))
    (x : X) (a : A) :
    (tableLawFinProb π hπ hπ1 M hM tables).w (x, a) = tableLaw π M tables x a :=
  rfl

/-- The input marginal of the assembled table law is `π`. -/
theorem tableLawFinProb_marginal {X A : Type*} [Fintype X] [Fintype A]
    (π : X → ℝ) (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (M : ℕ) (hM : 0 < M) (tables : Fin M → (X → A))
    (x : X) :
    (∑ a : A, (tableLawFinProb π hπ hπ1 M hM tables).w (x, a)) = π x :=
  tableLaw_marginal π M hM tables x

/-! ### Sampling bound `L(M,k) ≤ k(k-1)/(2(M-k+1))` -/

/-- Helper: `((k - 1 : ℕ) : ℝ) = k - 1` for `k ≥ 1`. -/
theorem cast_pred_eq (k : ℕ) (hk : 1 ≤ k) : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by
  simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) hk)

/-- Helper: `∑_{i<k} (i:ℝ) = k(k-1)/2`. -/
theorem sum_range_cast_id (k : ℕ) (hk : 1 ≤ k) :
    (∑ i ∈ Finset.range k, (i : ℝ)) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  have h2 := congrArg (Nat.cast : ℕ → ℝ) (Finset.sum_range_id_mul_two k)
  have hsum2 : (∑ i ∈ Finset.range k, (i : ℝ)) * 2 =
      (k : ℝ) * ((k : ℝ) - 1) := by
    simpa only [Nat.cast_mul, Nat.cast_two, Nat.cast_sum, Nat.cast_sub hk,
      Nat.cast_one] using h2
  linarith

/-- **Sampling bound.** `L(M,k) = log(M^k / (M)_k) ≤ k(k-1)/(2(M-k+1))`
for `1 ≤ k ≤ M`.  Write the ratio as `∏_{i<k} M/(M-i)`, take logs,
apply `-log(1-x) ≤ x/(1-x)`, and telescope. -/
theorem LboundM_le (M k : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) :
    LboundM M k ≤ (k * (k - 1) : ℝ) / (2 * (M - k + 1)) := by
  -- Positivity setup.
  have hMpos : (0:ℝ) < M := by
    have : (1:ℝ) ≤ M := by exact_mod_cast (le_trans hk hkM)
    linarith
  have hMne : (M:ℝ) ≠ 0 := ne_of_gt hMpos
  have hkpos : (0:ℝ) < k := by
    have : (1:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hMk : (k:ℝ) ≤ M := by exact_mod_cast hkM
  have hden : (0:ℝ) < M - k + 1 := by linarith
  -- Cast identity for `M - i`.
  have hcast_sub : ∀ i : ℕ, i < M → ((M - i : ℕ) : ℝ) = M - i := by
    intro i hi
    exact_mod_cast (Nat.cast_sub (Nat.le_of_lt hi))
  -- `descFactorial` as a product.
  have hdesc : (Nat.descFactorial M k : ℝ)
      = ∏ i ∈ Finset.range k, ((M - i : ℕ) : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range]
    exact_mod_cast (Nat.cast_prod (fun i => M - i) (Finset.range k))
  have hpow : ((M : ℝ) ^ k) = ∏ _i ∈ Finset.range k, (M : ℝ) := by
    rw [Finset.prod_const, Finset.card_range]
  have hratio : ((M : ℝ) ^ k) / (Nat.descFactorial M k : ℝ)
      = ∏ i ∈ Finset.range k, ((M : ℝ) / ((M - i : ℕ) : ℝ)) := by
    rw [hpow, hdesc, Finset.prod_div_distrib]
  -- Each factor is positive.
  have hpos : ∀ i ∈ Finset.range k, (0:ℝ) < (M : ℝ) / ((M - i : ℕ) : ℝ) := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have hiM : i < M := lt_of_lt_of_le hi' hkM
    have h2 : (0:ℝ) < ((M - i : ℕ) : ℝ) := by
      have : (0:ℕ) < M - i := Nat.sub_pos_of_lt hiM
      exact_mod_cast this
    positivity
  -- Log of the product is the sum of logs.
  have hlog : log (((M : ℝ) ^ k) / (Nat.descFactorial M k : ℝ))
      = ∑ i ∈ Finset.range k, log ((M : ℝ) / ((M - i : ℕ) : ℝ)) := by
    rw [hratio, Real.log_prod (Finset.range k)
      (fun i => (M : ℝ) / ((M - i : ℕ) : ℝ))
      (fun i hi => ne_of_gt (hpos i hi))]
  -- Each term: `log(M/(M-i)) = -log(1 - i/M)`.
  have hterm : ∀ i ∈ Finset.range k,
      log ((M : ℝ) / ((M - i : ℕ) : ℝ)) = -log (1 - (i : ℝ) / M) := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have hiM : i < M := lt_of_lt_of_le hi' hkM
    have hMi : (0:ℝ) < ((M - i : ℕ) : ℝ) := by
      have : (0:ℕ) < M - i := Nat.sub_pos_of_lt hiM
      exact_mod_cast this
    have hcast := hcast_sub i hiM
    have him1 : (i:ℝ) / M < 1 := by
      rw [div_lt_one hMpos]
      exact_mod_cast hiM
    have hne : (1:ℝ) - i / M ≠ 0 := by
      have : (0:ℝ) < 1 - i / M := by linarith
      exact ne_of_gt this
    have key : (M : ℝ) / ((M - i : ℕ) : ℝ) = 1 / (1 - (i : ℝ) / M) := by
      rw [hcast]
      have h1 : (1:ℝ) - i / M = (M - i) / M := by
        rw [sub_div, div_self hMne]
      rw [h1, one_div_div]
    rw [key, Real.log_div (by norm_num) hne, Real.log_one, zero_sub]
  have hsumlog : log (((M : ℝ) ^ k) / (Nat.descFactorial M k : ℝ))
      = ∑ i ∈ Finset.range k, (-log (1 - (i : ℝ) / M)) := by
    rw [hlog]
    exact Finset.sum_congr rfl (fun i hi => hterm i hi)
  -- Pointwise: `-log(1 - i/M) ≤ i/(M-i)`.
  have hpoint : ∀ i ∈ Finset.range k,
      -log (1 - (i : ℝ) / M) ≤ (i : ℝ) / ((M - i : ℕ) : ℝ) := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have hiM : i < M := lt_of_lt_of_le hi' hkM
    have him : (0:ℝ) ≤ i / M := by positivity
    have him1 : (i:ℝ) / M < 1 := by
      rw [div_lt_one hMpos]
      exact_mod_cast hiM
    have hle := neg_log_one_sub_le ((i:ℝ) / M) him him1
    have hcast := hcast_sub i hiM
    have hre : (i:ℝ) / M / (1 - i / M) = (i:ℝ) / ((M - i : ℕ) : ℝ) := by
      have h1 : (1:ℝ) - i / M = (M - i) / M := by
        rw [sub_div, div_self hMne]
      rw [h1, hcast]
      field_simp
    rw [hre] at hle
    exact hle
  -- Pointwise: `i/(M-i) ≤ i/(M-k+1)` for `i < k`.
  have hpoint2 : ∀ i ∈ Finset.range k,
      (i : ℝ) / ((M - i : ℕ) : ℝ) ≤ (i : ℝ) / (M - k + 1) := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have hiM : i < M := lt_of_lt_of_le hi' hkM
    have hcast := hcast_sub i hiM
    have hposi : (0:ℝ) ≤ i := by exact_mod_cast (Nat.zero_le i)
    have hdenA : (0:ℝ) < ((M - i : ℕ) : ℝ) := by
      have : (0:ℕ) < M - i := Nat.sub_pos_of_lt hiM
      exact_mod_cast this
    have hle : (M - k + 1 : ℝ) ≤ ((M - i : ℕ) : ℝ) := by
      rw [hcast]
      have hi1 : (i:ℝ) ≤ k - 1 := by
        have : i + 1 ≤ k := Nat.succ_le_of_lt hi'
        have : (i:ℝ) + 1 ≤ k := by exact_mod_cast this
        have hk1 : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := cast_pred_eq k hk
        linarith
      linarith
    exact div_le_div_of_nonneg_left hposi hden hle
  -- Chain the inequalities and sum.
  have hsum_le : log (((M : ℝ) ^ k) / (Nat.descFactorial M k : ℝ))
      ≤ ∑ i ∈ Finset.range k, (i : ℝ) / (M - k + 1) := by
    rw [hsumlog]
    refine Finset.sum_le_sum ?_
    intro i hi
    exact le_trans (hpoint i hi) (hpoint2 i hi)
  -- `∑_{i<k} i/(M-k+1) = (∑ i) / (M-k+1)`.
  have hsum_div : (∑ i ∈ Finset.range k, (i : ℝ) / (M - k + 1))
      = (∑ i ∈ Finset.range k, (i : ℝ)) / (M - k + 1) :=
    (Finset.sum_div _ _ _).symm
  have hsum_id := sum_range_cast_id k hk
  -- Evaluate the constant.
  have hconst : (∑ i ∈ Finset.range k, (i : ℝ)) / (M - k + 1)
      = (k * (k - 1) : ℝ) / (2 * (M - k + 1)) := by
    rw [hsum_id]
    field_simp

  -- Assemble.
  unfold LboundM
  calc log (((M : ℝ) ^ k) / (Nat.descFactorial M k : ℝ))
      ≤ ∑ i ∈ Finset.range k, (i : ℝ) / (M - k + 1) := hsum_le
    _ = (∑ i ∈ Finset.range k, (i : ℝ)) / (M - k + 1) := hsum_div
    _ = (k * (k - 1) : ℝ) / (2 * (M - k + 1)) := hconst

/-- **Proposition 4.1**, sampling bound in named form.
`L(M,k) = Lbound M k`. -/
theorem prop_4_1_Lbound_le (M k : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) :
    LboundM M k ≤ (k * (k - 1) : ℝ) / (2 * (M - k + 1)) :=
  LboundM_le M k hk hkM

theorem prop_4_1_Lbound_eq (M k : ℕ) : LboundM M k = Lbound M k := rfl

/-! ### Simultaneous `k`-uniformity of the table law -/

/-- **Proposition 4.1**, simultaneous `k`-uniformity.
    A single table law `μ = tableLawFinProb …` (whose construction does not
    involve `k`) has input marginal `π` and satisfies the sampling bound
    for every `1 ≤ k ≤ M`. -/
theorem prop_4_1_same_mu_all_k {X A : Type*} [Fintype X] [Fintype A]
    (π : X → ℝ) (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (M : ℕ) (hM : 0 < M) (tables : Fin M → (X → A)) :
    let μ : FinProb (X × A) := tableLawFinProb π hπ hπ1 M hM tables
    (∀ x : X, ∑ a : A, μ.w (x, a) = π x) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ M →
      LboundM M k ≤ (k * (k - 1) : ℝ) / (2 * (M - k + 1))) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact tableLawFinProb_marginal π hπ hπ1 M hM tables x
  · intro k hk hkM
    exact LboundM_le M k hk hkM

/-- The mixing distribution `μ` produced by a family of response tables is
    the same object for every sample size `k` (it is defined without
    reference to `k`). -/
theorem tableLawFinProb_indep_of_k {X A : Type*} [Fintype X] [Fintype A]
    (π : X → ℝ) (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (M : ℕ) (hM : 0 < M) (tables : Fin M → (X → A)) :
    tableLawFinProb π hπ hπ1 M hM tables
      = tableLawFinProb π hπ hπ1 M hM tables :=
  rfl

/-- Combined Proposition 4.1 package: nonnegativity of the sampling bound,
    the closed form of `L(M,k)`, and the analytic upper bound. -/
theorem prop_4_1_package (M k : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) :
    0 ≤ (k * (k - 1) : ℝ) / (2 * (M - k + 1)) ∧
    LboundM M k = Lbound M k ∧
    LboundM M k ≤ (k * (k - 1) : ℝ) / (2 * (M - k + 1)) := by
  refine ⟨?_, rfl, LboundM_le M k hk hkM⟩
  by_cases hlt : k < M
  · exact prop_4_1_Lbound_nonneg M k hk hlt
  · have hkM' : M = k := (le_antisymm hkM (le_of_not_gt hlt)).symm
    subst M
    have hrew : (k * (k - 1) : ℝ) / (2 * (k - k + 1)) = (k * (k - 1) : ℝ) / 2 := by
      rw [sub_self, zero_add, mul_one]
    rw [hrew]
    have h1 : (0:ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
    have h2 : (0:ℝ) ≤ k - 1 := by
      have : (1:ℝ) ≤ k := by exact_mod_cast hk
      linarith
    positivity

end Paper06
