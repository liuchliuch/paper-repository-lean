import P31.Schedule
import Mathlib.Analysis.SpecificLimits.Normed

/-! Infinite history identity (4.5) and stage-weighted geometric accounting (§5). -/

namespace P31.Schedule

open scoped BigOperators

/-- The full history series in (4.5), including its exceptional first increment.
The equality actually requires only `|τ θ| < 1`. -/
theorem hasSum_weighted_alpha {σ₁ τ θ : ℝ} (hr : |τ*θ| < 1) :
    HasSum (fun k : ℕ => alpha σ₁ τ (k+1)*θ^k) (σ₁*(1-θ)/(1-τ*θ)) := by
  have hden : 1-τ*θ ≠ 0 := by
    have hlt : τ*θ < 1 := lt_of_le_of_lt (le_abs_self _) hr
    exact ne_of_gt (sub_pos.mpr hlt)
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.sum_range_one, Nat.zero_add, alpha_one, pow_zero, mul_one]
  convert (hasSum_geometric_of_abs_lt_one hr).mul_left (σ₁*(τ-1)*θ) using 1
  · ext n
    rw [show n+1+1=n+2 by omega, alpha_succ_succ, pow_succ, mul_pow]
    ring
  · change σ₁*(1-θ)/(1-τ*θ)-σ₁ = (σ₁*(τ-1)*θ)/(1-τ*θ)
    apply (eq_div_iff hden).2
    rw [sub_mul, div_mul_cancel₀ _ hden]
    ring

/-- The exact original infinite sum, with no sign restrictions on the weights. -/
theorem tsum_weighted_alpha {σ₁ τ θ : ℝ} (hr : |τ*θ| < 1) :
    (∑' k : ℕ, alpha σ₁ τ (k+1)*θ^k) = σ₁*(1-θ)/(1-τ*θ) :=
  (hasSum_weighted_alpha hr).tsum_eq

/-- Original nonnegative-schedule specialization of (4.5). -/
theorem tsum_weighted_alpha_of_nonneg {σ₁ τ θ : ℝ}
    (_hσ : 0 ≤ σ₁) (hτ : 1 ≤ τ) (hθ : 0 ≤ θ) (hr : τ*θ < 1) :
    (∑' k : ℕ, alpha σ₁ τ (k+1)*θ^k) = σ₁*(1-θ)/(1-τ*θ) := by
  apply tsum_weighted_alpha
  rwa [abs_of_nonneg (mul_nonneg (by linarith : 0 ≤ τ) hθ)]

/-- The literal balanced-parameter instance stated in the paper. -/
theorem tsum_balanced_weighted_alpha {p κ σ₁ : ℝ} (hκ : 1 < κ) :
    (∑' k : ℕ, alpha σ₁ (tau p κ) (k+1)*theta p^k) =
      σ₁*(1-theta p)/(1-ratio κ) := by
  have hr : |tau p κ*theta p| < 1 := by
    rw [tau_mul_theta, abs_of_pos (ratio_pos κ)]
    exact ratio_lt_one hκ
  simpa only [tau_mul_theta] using tsum_weighted_alpha (σ₁ := σ₁) hr

/-- The series in the shifted-atom representation count (§5):
`∑_{s≥1} s r^(s-1) = 1/(1-r)^2`. -/
theorem hasSum_stage_weighted_geometric {r : ℝ} (hr : |r| < 1) :
    HasSum (fun k : ℕ => ((k+1:ℕ):ℝ)*r^k) (1/(1-r)^2) := by
  simpa using (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
    (by simpa only [Real.norm_eq_abs] using hr) :
    HasSum (fun n : ℕ => ((n+1).choose 1:ℝ)*r^n) (1/(1-r)^(1+1)))

theorem tsum_stage_weighted_geometric {r : ℝ} (hr : |r| < 1) :
    (∑' k : ℕ, ((k+1:ℕ):ℝ)*r^k) = 1/(1-r)^2 :=
  (hasSum_stage_weighted_geometric hr).tsum_eq

/-- The finite weighted geometric sum is bounded independently of the number of stages. -/
theorem stage_weighted_geometric_sum_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k+1:ℕ):ℝ)*r^k) ≤ 1/(1-r)^2 := by
  apply sum_le_hasSum (Finset.range n) _
    (hasSum_stage_weighted_geometric (by rwa [abs_of_nonneg hr0]))
  intro k _
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0 _)

/-- Summing power-dependent query terms with the extra cost `s` from §5. -/
theorem stage_weighted_power_sum_le {B r b : ℝ} (hB : 0 ≤ B)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hb : 0 < b) (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k+1:ℕ):ℝ)*(B*r^k)^b) ≤ B^b/(1-r^b)^2 := by
  calc
    _ = B^b * ∑ k ∈ Finset.range n, ((k+1:ℕ):ℝ)*(r^b)^k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Real.mul_rpow hB (pow_nonneg hr0 _), ← Real.rpow_natCast,
        ← Real.rpow_mul hr0, mul_comm (k:ℝ) b, Real.rpow_mul hr0, Real.rpow_natCast]
      ring
    _ ≤ B^b * (1/(1-r^b)^2) := mul_le_mul_of_nonneg_left
      (stage_weighted_geometric_sum_le (Real.rpow_nonneg hr0 b)
        (Real.rpow_lt_one hr0 hr1 hb) n) (Real.rpow_nonneg hB b)
    _ = B^b/(1-r^b)^2 := by ring

/-- The additive cost of representing all historical atoms is at most `S²`. -/
theorem sum_stage_weights_le_sq (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k+1:ℕ):ℝ)) ≤ (n:ℝ)^2 := by
  calc
    _ ≤ ∑ _k ∈ Finset.range n, (n:ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact_mod_cast (show k+1 ≤ n from Nat.succ_le_of_lt (Finset.mem_range.mp hk))
    _ = (n:ℝ)^2 := by simp [pow_two]

/-- The paper's `∑_{s=1}^S s T_s` representation bound before absorbing `S²`. -/
theorem stage_weighted_budget_sum_le {C B r b : ℝ} {T : ℕ → ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hr0 : 0 ≤ r) (hr1 : r < 1) (hb : 0 < b)
    (hT : ∀ k, T k ≤ C*(1+(B*r^k)^b)) (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k+1:ℕ):ℝ)*T k) ≤
      C*((n:ℝ)^2+B^b/(1-r^b)^2) := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, ((k+1:ℕ):ℝ)*(C*(1+(B*r^k)^b)) :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hT k) (Nat.cast_nonneg _))
    _ = C*((∑ k ∈ Finset.range n, ((k+1:ℕ):ℝ)) +
      ∑ k ∈ Finset.range n, ((k+1:ℕ):ℝ)*(B*r^k)^b) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ ≤ C*((n:ℝ)^2+B^b/(1-r^b)^2) :=
      mul_le_mul_of_nonneg_left (add_le_add (sum_stage_weights_le_sq n)
        (stage_weighted_power_sum_le hB hr0 hr1 hb n)) hC

/-- Squaring the logarithmic stage count still costs only the prescribed power.
This is the precise absorption required for the representation bound in §5. -/
theorem ceiling_log_sq_le_power {κ b Λ : ℝ} (hκ : 1 < κ) (hb : 0 < b) (hΛ : 1 ≤ Λ) :
    (⌈Real.logb 2 (2*Λ)/(κ-1)⌉₊ : ℝ)^2 ≤
      ((1+1/((b/2)*Real.log 2))/(κ-1)+1)^2*Λ^b := by
  have h := ceiling_log_le_power hκ (show 0 < b/2 by linarith) hΛ
  have hnon : 0 ≤ (⌈Real.logb 2 (2*Λ)/(κ-1)⌉₊ : ℝ) := Nat.cast_nonneg _
  have hpow : (Λ^(b/2))^2 = Λ^b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ Λ)]
    congr 1
    ring
  calc
    _ ≤ (((1+1/((b/2)*Real.log 2))/(κ-1)+1)*Λ^(b/2))^2 :=
      pow_le_pow_left₀ hnon h 2
    _ = ((1+1/((b/2)*Real.log 2))/(κ-1)+1)^2*Λ^b := by rw [mul_pow, hpow]

/-- Complete scalar representation accounting: the extra stage weight preserves
`O(Λ^b)` and introduces no logarithmic loss. -/
theorem stage_weighted_logarithmic_budget_le_power {κ b Λ C K r : ℝ} {T : ℕ → ℝ}
    (hκ : 1 < κ) (hb : 0 < b) (hΛ : 1 ≤ Λ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hT : ∀ k, T k ≤ C*(1+(K*Λ*r^k)^b)) :
    (∑ k ∈ Finset.range ⌈Real.logb 2 (2*Λ)/(κ-1)⌉₊, ((k+1:ℕ):ℝ)*T k) ≤
      C*((((1+1/((b/2)*Real.log 2))/(κ-1)+1)^2+K^b/(1-r^b)^2)*Λ^b) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  calc
    _ ≤ C*((⌈Real.logb 2 (2*Λ)/(κ-1)⌉₊ : ℝ)^2+(K*Λ)^b/(1-r^b)^2) :=
      stage_weighted_budget_sum_le hC (mul_nonneg hK hΛ0) hr0 hr1 hb hT _
    _ ≤ C*((((1+1/((b/2)*Real.log 2))/(κ-1)+1)^2*Λ^b)+(K*Λ)^b/(1-r^b)^2) :=
      mul_le_mul_of_nonneg_left (add_le_add_right (ceiling_log_sq_le_power hκ hb hΛ) _) hC
    _ = C*((((1+1/((b/2)*Real.log 2))/(κ-1)+1)^2+K^b/(1-r^b)^2)*Λ^b) := by
      rw [Real.mul_rpow hK hΛ0]
      ring

/-- Parameter-dependent constant for the historical-atom representation count. -/
noncomputable def representationConstant (C A p κ : ℝ) : ℝ :=
  (C*(1+(2:ℝ)^(κ*beta p κ))+1) *
    (((1+1/((beta p κ/2)*Real.log 2))/(κ-1)+1)^2+
      leadingScale A p κ ^ beta p κ / (1-ratio κ ^ beta p κ)^2)

theorem representationConstant_pos {C A p κ : ℝ} (hC : 0 ≤ C) (hA : 0 < A)
    (hp : 2 ≤ p) (hκ : 1 < κ) : 0 < representationConstant C A p κ := by
  have hb : 0 < beta p κ := beta_pos hp hκ
  have hl : 0 < (beta p κ/2)*Real.log 2 :=
    mul_pos (by linarith) (Real.log_pos (by norm_num))
  have hf : 0 ≤ (2:ℝ)^(κ*beta p κ) := Real.rpow_nonneg (by norm_num) _
  have hout : 0 < C*(1+(2:ℝ)^(κ*beta p κ))+1 := by
    nlinarith [mul_nonneg hC hf]
  have hfirst : 0 < (1+1/((beta p κ/2)*Real.log 2))/(κ-1)+1 :=
    add_pos (div_pos (add_pos zero_lt_one (div_pos zero_lt_one hl))
      (sub_pos.mpr hκ)) zero_lt_one
  have htail : 0 ≤ leadingScale A p κ ^ beta p κ / (1-ratio κ ^ beta p κ)^2 :=
    div_nonneg (Real.rpow_nonneg (le_of_lt (leadingScale_pos hA hp hκ)) _) (sq_nonneg _)
  exact mul_pos hout (add_pos_of_pos_of_nonneg (pow_pos hfirst 2) htail)

/-- Full literal-budget form of the representation bound in §5.
The coefficient depends only on the atom normalization and `p, κ`, together with
its complementary-composite theorem constant, never on `L, R, ε` or dimension. -/
theorem total_stage_weighted_query_budget_le {C A L R p κ ε : ℝ}
    (hC : 0 ≤ C) (hA : 0 < A) (_hL : 0 < L) (hR : 0 < R)
    (hp : 2 ≤ p) (hκlo : 1 < κ) (_hκhi : κ ≤ 2)
    (hε : 0 < ε) (hsmall : ε ≤ L*R^(κ-1)) :
    (∑ n ∈ Finset.range (stageCount L R κ ε),
      ((n+1:ℕ):ℝ)*(queryBudget C A L R p κ ε n : ℝ)) ≤
      representationConstant C A p κ * (L*R^(κ-1)/ε)^beta p κ := by
  let Λ := L*R^(κ-1)/ε
  let K := leadingScale A p κ
  let C' := C*(1+(2:ℝ)^(κ*beta p κ))+1
  have hΛ : 1 ≤ Λ := (le_div_iff₀ hε).2 (by simpa using hsmall)
  have hΛ0 : 0 ≤ Λ := by linarith
  have hK : 0 ≤ K := le_of_lt (leadingScale_pos hA hp hκlo)
  have hr0 : 0 ≤ ratio κ := le_of_lt (ratio_pos κ)
  have hb : 0 < beta p κ := beta_pos hp hκlo
  have hf : 0 ≤ (2:ℝ)^(κ*beta p κ) := Real.rpow_nonneg (by norm_num) _
  have hC' : 0 ≤ C' := by dsimp [C']; nlinarith [mul_nonneg hC hf]
  have hscale (n : ℕ) :
      stageScale L (initialWeight (A*R^(p-1)) (theta p) (ratio κ) ε) (tau p κ) R p κ n =
        K*Λ*ratio κ ^ n := by
    rw [balanced_stageScale hR, calibrated_first_stageScale hA hR (theta_lt_one hp)
      (ratio_lt_one hκlo) hε]
    rfl
  have hT (n : ℕ) :
      (queryBudget C A L R p κ ε n : ℝ) ≤ C'*(1+(K*Λ*ratio κ ^ n)^beta p κ) := by
    have hs0 : 0 ≤ stageScale L (initialWeight (A*R^(p-1)) (theta p) (ratio κ) ε)
        (tau p κ) R p κ n := by
      rw [hscale]
      exact mul_nonneg (mul_nonneg hK hΛ0) (pow_nonneg hr0 _)
    simpa only [queryBudget, hscale] using ceil_budget_le hC hf hs0 (b := beta p κ)
  have hS : stageCount L R κ ε = ⌈Real.logb 2 (2*Λ)/(κ-1)⌉₊ := by
    unfold stageCount
    rw [show 2*L*R^(κ-1)/ε = 2*Λ by dsimp [Λ]; ring]
  rw [hS]
  calc
    _ ≤ C' * ((((1+1/((beta p κ/2)*Real.log 2))/(κ-1)+1)^2+
        K^beta p κ/(1-ratio κ^beta p κ)^2)*Λ^beta p κ) :=
      stage_weighted_logarithmic_budget_le_power hκlo hb hΛ hC' hK hr0 (ratio_lt_one hκlo) hT
    _ = representationConstant C A p κ * (L*R^(κ-1)/ε)^beta p κ := by
      dsimp [representationConstant, C', K, Λ]
      ring

end P31.Schedule
