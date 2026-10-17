import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# Finite weighted Holder and MGF blocking without independence

All factors are functions on one and the same finite sample space. The only
assumption on the joint weights is nonnegativity; normalization to total mass
one is allowed but is not needed for these homogeneous inequalities.
-/

open BigOperators Real Finset

namespace PsgEst.FiniteHolder

variable {α : Type*} [Fintype α]

/-- Finite expectation with respect to real nonnegative weights. -/
noncomputable def expectation (w f : α → ℝ) : ℝ := ∑ x, w x * f x

/-- Multi-factor weighted Holder. The factors may be arbitrarily dependent,
and zero expectations are included. -/
theorem holder_rpow (k : ℕ) (hk : 0 < k) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (f : Fin k → α → ℝ) (hf : ∀ r x, 0 ≤ f r x) :
    (∑ x, w x * ∏ r : Fin k, (f r x) ^ (1 / (k : ℝ))) ≤
      ∏ r : Fin k, (∑ x, w x * f r x) ^ (1 / (k : ℝ)) := by
  classical
  let q : ℝ := 1 / (k : ℝ)
  let M : Fin k → ℝ := fun r => ∑ x, w x * f r x
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hq : 0 < q := one_div_pos.mpr hkR
  have hweights : ∑ r : Fin k, q = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [q]
    field_simp
  have hMnonneg (r : Fin k) : 0 ≤ M r :=
    sum_nonneg (fun x _ => mul_nonneg (hw x) (hf r x))
  change (∑ x, w x * ∏ r : Fin k, (f r x) ^ q) ≤ ∏ r : Fin k, M r ^ q
  by_cases hzero : ∃ r, M r = 0
  · obtain ⟨r0, hr0⟩ := hzero
    have hweighted_zero (x : α) : w x * f r0 x = 0 := by
      have hle : w x * f r0 x ≤ M r0 :=
        Finset.single_le_sum (fun y _ => mul_nonneg (hw y) (hf r0 y)) (mem_univ x)
      rw [hr0] at hle
      exact le_antisymm hle (mul_nonneg (hw x) (hf r0 x))
    have hterm_zero (x : α) : w x * ∏ r : Fin k, (f r x) ^ q = 0 := by
      by_cases hw0 : w x = 0
      · simp [hw0]
      · have hf0 : f r0 x = 0 := (mul_eq_zero.mp (hweighted_zero x)).resolve_left hw0
        have hprod : (∏ r : Fin k, (f r x) ^ q) = 0 := by
          apply Finset.prod_eq_zero (mem_univ r0)
          rw [hf0, Real.zero_rpow (ne_of_gt hq)]
        rw [hprod, mul_zero]
    simp_rw [hterm_zero]
    simpa only [sum_const_zero] using
      (Finset.prod_nonneg (fun r _ => Real.rpow_nonneg (hMnonneg r) q))
  · have hMpos (r : Fin k) : 0 < M r := by
      exact lt_of_le_of_ne (hMnonneg r) (by intro h; exact hzero ⟨r, h.symm⟩)
    let P : ℝ := ∏ r : Fin k, M r ^ q
    have hP : 0 < P := Finset.prod_pos (fun r _ => Real.rpow_pos_of_pos (hMpos r) q)
    have hamgm (x : α) : (∏ r : Fin k, (f r x) ^ q) / P ≤
        ∑ r : Fin k, q * (f r x / M r) := by
      have h := Real.geom_mean_le_arith_mean_weighted (s := (univ : Finset (Fin k)))
        (fun _ => q) (fun r => f r x / M r) (fun _ _ => hq.le) hweights
        (fun r _ => div_nonneg (hf r x) (hMnonneg r))
      simpa only [Real.div_rpow (hf _ x) (hMnonneg _) q, Finset.prod_div_distrib]
        using h
    have hpoint (x : α) : ∏ r : Fin k, (f r x) ^ q ≤
        (∑ r : Fin k, q * (f r x / M r)) * P :=
      (div_le_iff₀ hP).mp (hamgm x)
    have hmean : (∑ x, w x * ∑ r : Fin k, q * (f r x / M r)) = 1 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      calc (∑ r : Fin k, ∑ x, w x * (q * (f r x / M r))) =
          ∑ r : Fin k, q * (M r / M r) := by
            apply Finset.sum_congr rfl
            intro r _
            dsimp only [M]
            simp only [Finset.sum_div, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
        _ = ∑ r : Fin k, q := by
            apply Finset.sum_congr rfl
            intro r _
            rw [div_self (ne_of_gt (hMpos r)), mul_one]
        _ = 1 := hweights
    calc (∑ x, w x * ∏ r : Fin k, (f r x) ^ q) ≤
        ∑ x, w x * ((∑ r : Fin k, q * (f r x / M r)) * P) :=
          Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hw x))
      _ = (∑ x, w x * ∑ r : Fin k, q * (f r x / M r)) * P := by
          simp only [← mul_assoc]
          rw [← Finset.sum_mul]
      _ = P := by rw [hmean, one_mul]

/-- Exponentials turn the geometric mean of the rescaled block MGFs into
one exponential of the full block sum. -/
theorem exp_sum_eq_prod_rpow (k : ℕ) (hk : 0 < k) (θ : ℝ) (a : Fin k → ℝ) :
    exp (θ * ∑ r, a r) =
      ∏ r : Fin k, (exp ((k : ℝ) * θ * a r)) ^ (1 / (k : ℝ)) := by
  have hkR : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
  simp_rw [← Real.exp_mul]
  rw [← Real.exp_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  field_simp

/-- Finite MGF blocking. No independence, stationarity, Markov property or
concentration conclusion is assumed. -/
theorem mgf_sum_le_product (k : ℕ) (hk : 0 < k) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (A : Fin k → α → ℝ) (θ : ℝ) :
    (∑ x, w x * exp (θ * ∑ r, A r x)) ≤
      ∏ r : Fin k, (∑ x, w x * exp ((k : ℝ) * θ * A r x)) ^ (1 / (k : ℝ)) := by
  have h := holder_rpow k hk w hw (fun r x => exp ((k : ℝ) * θ * A r x))
    (fun _ _ => (Real.exp_pos _).le)
  simpa only [← exp_sum_eq_prod_rpow k hk θ] using h

/-- A convenient MGF interface: block bounds of the form `exp(k*c_r)`
combine into `exp(sum c_r)` for the full dependent sum. -/
theorem mgf_sum_le_exp_sum (k : ℕ) (hk : 0 < k) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (A : Fin k → α → ℝ) (θ : ℝ) (c : Fin k → ℝ)
    (hblock : ∀ r : Fin k, (∑ x, w x * exp ((k : ℝ) * θ * A r x)) ≤ exp ((k : ℝ) * c r)) :
    (∑ x, w x * exp (θ * ∑ r, A r x)) ≤ exp (∑ r, c r) := by
  have hq : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  calc (∑ x, w x * exp (θ * ∑ r, A r x)) ≤
      ∏ r : Fin k, (∑ x, w x * exp ((k : ℝ) * θ * A r x)) ^ (1 / (k : ℝ)) :=
        mgf_sum_le_product k hk w hw A θ
    _ ≤ ∏ r : Fin k, (exp ((k : ℝ) * c r)) ^ (1 / (k : ℝ)) := by
      apply Finset.prod_le_prod
      · intro r _
        exact Real.rpow_nonneg (sum_nonneg fun x _ => mul_nonneg (hw x) (Real.exp_pos _).le) _
      · intro r _
        exact Real.rpow_le_rpow
          (sum_nonneg fun x _ => mul_nonneg (hw x) (Real.exp_pos _).le) (hblock r) hq
    _ = exp (∑ r, c r) := by
      simpa only [one_mul, mul_one] using (exp_sum_eq_prod_rpow k hk 1 c).symm

/-- Equivalent form when each block's log-MGF bound is supplied directly. -/
theorem mgf_sum_le_exp_average (k : ℕ) (hk : 0 < k) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (A : Fin k → α → ℝ) (θ : ℝ) (B : Fin k → ℝ)
    (hblock : ∀ r : Fin k, (∑ x, w x * exp ((k : ℝ) * θ * A r x)) ≤ exp (B r)) :
    (∑ x, w x * exp (θ * ∑ r, A r x)) ≤ exp ((∑ r, B r) / (k : ℝ)) := by
  have hkR : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
  have h := mgf_sum_le_exp_sum k hk w hw A θ (fun r => B r / (k : ℝ)) (by
    intro r
    convert hblock r using 1
    congr 1
    field_simp)
  simpa only [Finset.sum_div] using h

end PsgEst.FiniteHolder
