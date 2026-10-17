/-
Copyright (c) 2026. Sampling with and without replacement and its entropy cost.
-/
import Paper06.Basic
import Paper06.Divergence
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals

open Real BigOperators
open scoped Classical

namespace Paper06.Sampling

/-- The exact relative entropy cost of sampling distinct ordered indices. -/
noncomputable def cost (M k : ℕ) : ℝ :=
  Real.log (((M : ℝ) ^ k) / (M.descFactorial k : ℝ))

/-- The numerical sampling bound, including the endpoint `k = M`. -/
theorem cost_le (M k : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) :
    cost M k ≤ (k : ℝ) * ((k : ℝ) - 1) / (2 * ((M : ℝ) - k + 1)) := by
  have hM : 0 < M := lt_of_lt_of_le (by omega) hkM
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hM0 : (M : ℝ) ≠ 0 := ne_of_gt hMr
  have hkMr : (k : ℝ) ≤ M := by exact_mod_cast hkM
  have hden : (0 : ℝ) < (M : ℝ) - k + 1 := by linarith
  have hdesc : (M.descFactorial k : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.descFactorial_pos.mpr hkM))
  have hprod : ∀ i ∈ Finset.range k, ((M - i : ℕ) : ℝ) ≠ 0 := by
    intro i hi
    have hiM : i < M := lt_of_lt_of_le (Finset.mem_range.mp hi) hkM
    exact_mod_cast (ne_of_gt (Nat.sub_pos_of_lt hiM))
  have hexp : cost M k = ∑ i ∈ Finset.range k,
      Real.log ((M : ℝ) / ((M - i : ℕ) : ℝ)) := by
    unfold cost
    rw [Real.log_div (pow_ne_zero k hM0) hdesc, Real.log_pow,
      Nat.descFactorial_eq_prod_range, Nat.cast_prod,
      Real.log_prod _ _ hprod]
    have hconst : (k : ℝ) * Real.log (M : ℝ) =
        ∑ _i ∈ Finset.range k, Real.log (M : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hconst, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (Real.log_div hM0 (hprod i hi)).symm
  have hpoint : ∀ i ∈ Finset.range k,
      Real.log ((M : ℝ) / ((M - i : ℕ) : ℝ)) ≤
        (i : ℝ) / ((M : ℝ) - k + 1) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hiM : i < M := lt_of_lt_of_le hik hkM
    have hsub : ((M - i : ℕ) : ℝ) = (M : ℝ) - i :=
      Nat.cast_sub (le_of_lt hiM)
    have hsubpos : (0 : ℝ) < ((M - i : ℕ) : ℝ) := by
      exact_mod_cast (Nat.sub_pos_of_lt hiM)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hMr hsubpos)
    have hterm : (M : ℝ) / ((M - i : ℕ) : ℝ) - 1 =
        (i : ℝ) / ((M - i : ℕ) : ℝ) := by
      apply (eq_div_iff (hprod i hi)).2
      rw [sub_mul, div_mul_cancel₀ _ (hprod i hi), one_mul, hsub]
      ring
    rw [hterm] at hlog
    apply hlog.trans
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg i) hden
    rw [hsub]
    have hik' : (i : ℝ) + 1 ≤ k := by exact_mod_cast (Nat.succ_le_of_lt hik)
    linarith
  have hsum : (∑ i ∈ Finset.range k, (i : ℝ)) =
      (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    have heq := congrArg (Nat.cast : ℕ → ℝ) (Finset.sum_range_id_mul_two k)
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] at heq
    rw [Nat.cast_sub hk, Nat.cast_one] at heq
    linarith
  rw [hexp]
  calc
    _ ≤ ∑ i ∈ Finset.range k, (i : ℝ) / ((M : ℝ) - k + 1) :=
      Finset.sum_le_sum hpoint
    _ = (k : ℝ) * ((k : ℝ) - 1) / (2 * ((M : ℝ) - k + 1)) := by
      rw [← Finset.sum_div, hsum, div_div]

/-- The cost is nonnegative whenever the distinct-index law exists. -/
theorem cost_nonneg (M k : ℕ) (hkM : k ≤ M) : 0 ≤ cost M k := by
  have hd : (0 : ℝ) < (M.descFactorial k : ℝ) := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hkM)
  apply Real.log_nonneg
  apply (one_le_div hd).2
  exact_mod_cast (Nat.descFactorial_le_pow M k)

/-- A bounded density ratio gives an upper bound for finite relative entropy.
The domination itself guarantees a positive denominator wherever the first law is positive. -/
theorem klPos_le_log_of_domination {α : Type*} [Fintype α]
    (p q : FinProb α) (C : ℝ) (_hC : 0 < C)
    (h : ∀ x, p.w x ≤ C * q.w x) : FinProb.klPos p q ≤ Real.log C := by
  have hpoint : ∀ x, p.w x * Real.log (p.w x / q.w x) ≤ p.w x * Real.log C := by
    intro x
    by_cases hp : p.w x = 0
    · simp [hp]
    · have hp' : 0 < p.w x := lt_of_le_of_ne (p.nonneg x) (Ne.symm hp)
      have hq : 0 < q.w x := by
        by_contra hn
        have hq0 : q.w x = 0 := le_antisymm (le_of_not_gt hn) (q.nonneg x)
        have hh := h x
        rw [hq0, mul_zero] at hh
        linarith
      apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
      apply Real.log_le_log (div_pos hp' hq)
      exact (div_le_iff₀ hq).2 (h x)
  unfold FinProb.klPos
  calc
    _ ≤ ∑ x, p.w x * Real.log C := Finset.sum_le_sum (fun x _ => hpoint x)
    _ = Real.log C := by rw [← Finset.sum_mul, p.sum_eq_one, one_mul]

/-- Uniform iid ordered indices from `[M]`. -/
noncomputable def iidLaw (M k : ℕ) (hM : 0 < M) : FinProb (Fin k → Fin M) where
  w _ := 1 / (M : ℝ) ^ k
  nonneg _ := by positivity
  sum_eq_one := by
    have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
    simp [Finset.sum_const, nsmul_eq_mul, hMr]

@[simp] theorem iidLaw_w (M k : ℕ) (hM : 0 < M) (z : Fin k → Fin M) :
    (iidLaw M k hM).w z = 1 / (M : ℝ) ^ k := rfl

/-- Uniform distinct ordered indices from `[M]`, regarded on the whole tuple space. -/
noncomputable def distinctLaw (M k : ℕ) (hkM : k ≤ M) : FinProb (Fin k → Fin M) where
  w z := if Function.Injective z then 1 / (M.descFactorial k : ℝ) else 0
  nonneg z := by split_ifs <;> positivity
  sum_eq_one := by
    have hcard : Fintype.card {z : Fin k → Fin M // Function.Injective z} =
        M.descFactorial k := by
      rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _)]
      simp
    have hdn : (M.descFactorial k : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Nat.descFactorial_pos.mpr hkM))
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Fintype.card_subtype, hcard]
    exact mul_one_div_cancel hdn

@[simp] theorem distinctLaw_w (M k : ℕ) (hkM : k ≤ M) (z : Fin k → Fin M) :
    (distinctLaw M k hkM).w z =
      if Function.Injective z then 1 / (M.descFactorial k : ℝ) else 0 := rfl

/-- The exact constant density ratio on distinct tuples. -/
noncomputable def densityRatio (M k : ℕ) : ℝ :=
  (M : ℝ) ^ k / (M.descFactorial k : ℝ)

theorem densityRatio_pos (M k : ℕ) (hM : 0 < M) (hkM : k ≤ M) :
    0 < densityRatio M k := by
  unfold densityRatio
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hdr : (0 : ℝ) < (M.descFactorial k : ℝ) := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hkM)
  positivity

/-- Sampling without replacement is dominated by iid sampling with the exact ratio. -/
theorem distinct_le_densityRatio_mul_iid (M k : ℕ) (hM : 0 < M) (hkM : k ≤ M)
    (z : Fin k → Fin M) :
    (distinctLaw M k hkM).w z ≤ densityRatio M k * (iidLaw M k hM).w z := by
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  have hp : (M : ℝ) ^ k ≠ 0 := pow_ne_zero k hMr
  have heq : densityRatio M k * (iidLaw M k hM).w z =
      1 / (M.descFactorial k : ℝ) := by
    simp only [densityRatio, iidLaw_w]
    field_simp
  rw [heq, distinctLaw_w]
  split_ifs
  · exact le_rfl
  · positivity

/-- On distinct tuples the likelihood ratio is the constant `M^k / (M)_k`. -/
theorem distinct_iid_likelihoodRatio (M k : ℕ) (hM : 0 < M) (hkM : k ≤ M)
    (z : Fin k → Fin M) (hz : Function.Injective z) :
    (distinctLaw M k hkM).w z / (iidLaw M k hM).w z = densityRatio M k := by
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  have hd : (M.descFactorial k : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.descFactorial_pos.mpr hkM))
  simp only [distinctLaw_w, if_pos hz, iidLaw_w, densityRatio]
  field_simp

/-- The two finite sampling laws have exactly the paper's logarithmic KL cost. -/
theorem klPos_distinct_iid (M k : ℕ) (hM : 0 < M) (hkM : k ≤ M) :
    FinProb.klPos (distinctLaw M k hkM) (iidLaw M k hM) = cost M k := by
  have hpoint : ∀ z : Fin k → Fin M,
      (distinctLaw M k hkM).w z *
          Real.log ((distinctLaw M k hkM).w z / (iidLaw M k hM).w z) =
        (distinctLaw M k hkM).w z * cost M k := by
    intro z
    by_cases hz : Function.Injective z
    · rw [distinct_iid_likelihoodRatio M k hM hkM z hz]
      rfl
    · simp [distinctLaw_w, hz]
  unfold FinProb.klPos
  rw [Finset.sum_congr rfl (fun z _ => hpoint z), ← Finset.sum_mul,
    (distinctLaw M k hkM).sum_eq_one, one_mul]

/-- Multiplying both laws by the same independent law preserves density domination. -/
theorem prod_domination {α β : Type*} [Fintype α] [Fintype β]
    (r : FinProb α) (p q : FinProb β) (C : ℝ)
    (h : ∀ y, p.w y ≤ C * q.w y) :
    ∀ z, (Paper06.prod r p).w z ≤ C * (Paper06.prod r q).w z := by
  intro z
  simp only [Paper06.prod_w]
  calc
    r.w z.1 * p.w z.2 ≤ r.w z.1 * (C * q.w z.2) :=
      mul_le_mul_of_nonneg_left (h z.2) (r.nonneg z.1)
    _ = C * (r.w z.1 * q.w z.2) := by ring

/-- A common independent random environment leaves the sampling KL cost unchanged. -/
theorem klPos_common_prod_distinct_iid {α : Type*} [Fintype α]
    (r : FinProb α) (M k : ℕ) (hM : 0 < M) (hkM : k ≤ M) :
    FinProb.klPos (Paper06.prod r (distinctLaw M k hkM))
      (Paper06.prod r (iidLaw M k hM)) = cost M k := by
  have hpoint : ∀ z : α × (Fin k → Fin M),
      (Paper06.prod r (distinctLaw M k hkM)).w z *
          Real.log ((Paper06.prod r (distinctLaw M k hkM)).w z /
            (Paper06.prod r (iidLaw M k hM)).w z) =
        (Paper06.prod r (distinctLaw M k hkM)).w z * cost M k := by
    intro z
    by_cases hr : r.w z.1 = 0
    · simp [Paper06.prod_w, hr]
    by_cases hz : Function.Injective z.2
    · have heq : (Paper06.prod r (distinctLaw M k hkM)).w z /
          (Paper06.prod r (iidLaw M k hM)).w z = densityRatio M k := by
        simp only [Paper06.prod_w]
        rw [mul_div_mul_left _ _ hr,
          distinct_iid_likelihoodRatio M k hM hkM z.2 hz]
      rw [heq]
      rfl
    · simp [Paper06.prod_w, distinctLaw_w, hz]
  unfold FinProb.klPos
  rw [Finset.sum_congr rfl (fun z _ => hpoint z), ← Finset.sum_mul,
    (Paper06.prod r (distinctLaw M k hkM)).sum_eq_one, one_mul]

/-- Domination gives the exact support condition needed by finite relative entropy. -/
theorem supports_of_domination {α : Type*} [Fintype α]
    (p q : FinProb α) (C : ℝ) (h : ∀ x, p.w x ≤ C * q.w x) :
    FinProb.Supports p q := by
  intro x hx
  have hh := h x
  rw [hx, mul_zero] at hh
  exact le_antisymm hh (p.nonneg x)

/-- Every finite pushforward preserves a pointwise density bound. -/
theorem map_domination {α β : Type*} [Fintype α] [Fintype β]
    (p q : FinProb α) (C : ℝ) (h : ∀ x, p.w x ≤ C * q.w x) (f : α → β) :
    ∀ y, (FinProb.map p f).w y ≤ C * (FinProb.map q f).w y := by
  intro y
  simp only [FinProb.map_w, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : f x = y
  · simpa only [hx, if_true] using h x
  · simp [hx]

/-- Support-safe entropy bound after any finite observation map. -/
theorem klPos_map_le_log_of_domination {α β : Type*} [Fintype α] [Fintype β]
    (p q : FinProb α) (C : ℝ) (hC : 0 < C)
    (h : ∀ x, p.w x ≤ C * q.w x) (f : α → β) :
    FinProb.klPos (FinProb.map p f) (FinProb.map q f) ≤ Real.log C :=
  klPos_le_log_of_domination _ _ C hC (map_domination p q C h f)

/-- The same bound for relative entropy with an explicit infinite value. -/
theorem kl_map_le_log_of_domination {α β : Type*} [Fintype α] [Fintype β]
    (p q : FinProb α) (C : ℝ) (hC : 0 < C)
    (h : ∀ x, p.w x ≤ C * q.w x) (f : α → β) :
    FinProb.kl (FinProb.map p f) (FinProb.map q f) ≤ (Real.log C : EReal) := by
  rw [FinProb.kl_of_support
    (supports_of_domination _ _ C (map_domination p q C h f))]
  exact EReal.coe_le_coe (klPos_map_le_log_of_domination p q C hC h f)

/-- Data processing for distinct-index sampling followed by any observation. -/
theorem klPos_map_distinct_iid_le {β : Type*} [Fintype β]
    (M k : ℕ) (hM : 0 < M) (hkM : k ≤ M) (f : (Fin k → Fin M) → β) :
    FinProb.klPos (FinProb.map (distinctLaw M k hkM) f)
      (FinProb.map (iidLaw M k hM) f) ≤ cost M k := by
  exact klPos_map_le_log_of_domination _ _ (densityRatio M k)
    (densityRatio_pos M k hM hkM)
    (distinct_le_densityRatio_mul_iid M k hM hkM) f

/-- Common randomness can be retained through an arbitrary observation map. -/
theorem klPos_map_common_prod_distinct_iid_le {α β : Type*}
    [Fintype α] [Fintype β] (r : FinProb α)
    (M k : ℕ) (hM : 0 < M) (hkM : k ≤ M)
    (f : (α × (Fin k → Fin M)) → β) :
    FinProb.klPos (FinProb.map (Paper06.prod r (distinctLaw M k hkM)) f)
      (FinProb.map (Paper06.prod r (iidLaw M k hM)) f) ≤ cost M k := by
  exact klPos_map_le_log_of_domination _ _ (densityRatio M k)
    (densityRatio_pos M k hM hkM)
    (prod_domination r _ _ (densityRatio M k)
      (distinct_le_densityRatio_mul_iid M k hM hkM)) f

/-- The common-randomness observation bound also holds for extended relative entropy. -/
theorem kl_map_common_prod_distinct_iid_le {α β : Type*}
    [Fintype α] [Fintype β] (r : FinProb α)
    (M k : ℕ) (hM : 0 < M) (hkM : k ≤ M)
    (f : (α × (Fin k → Fin M)) → β) :
    FinProb.kl (FinProb.map (Paper06.prod r (distinctLaw M k hkM)) f)
      (FinProb.map (Paper06.prod r (iidLaw M k hM)) f) ≤ (cost M k : EReal) := by
  exact kl_map_le_log_of_domination _ _ (densityRatio M k)
    (densityRatio_pos M k hM hkM)
    (prod_domination r _ _ (densityRatio M k)
      (distinct_le_densityRatio_mul_iid M k hM hkM)) f

end Paper06.Sampling
