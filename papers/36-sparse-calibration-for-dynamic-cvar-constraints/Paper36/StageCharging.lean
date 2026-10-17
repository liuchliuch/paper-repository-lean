import Paper36.StageRisk
import Paper36.HybridCharging

/-! The actual B.3 pathwise hybrid bound. The stage-dependent adverse laws and
prefix-density cap come from StageRisk; both weights are precisely the source
stageWsq/stagew definitions. Nominal trajectories/count charges are unchanged. -/
namespace Paper36.StageCharging
noncomputable section
open scoped BigOperators
open Paper36.CVaR Paper36.Simulation Paper36.HybridCharging
variable {S A : Type*} [Fintype S] [Fintype A]

def stageWeight (β : ℕ → ℝ) (H h : ℕ) : ℝ :=
  ((H-h+1 : ℕ) : ℝ)^2 / Weights.prefixMass β (h+1)

theorem stageWeight_nonneg (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (H h : ℕ) : 0 ≤ stageWeight β H h := by
  unfold stageWeight
  exact div_nonneg (sq_nonneg _) (Weights.prefixMass_pos (fun j _ => (hβ j).1)).le

theorem sum_stageWeight (β : ℕ → ℝ) (H : ℕ) :
    (∑ h ∈ Finset.range H, stageWeight β H h) = Weights.stageWsq β (H+1) := by
  unfold Weights.stageWsq
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_bij (fun h _ => h+1)
  · intro h hh
    simp only [Finset.mem_range] at hh
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · intro h hh j hj heq
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.1 hj
    exact ⟨j-1, Finset.mem_range.2 (by omega), by omega⟩
  · intro h hh
    have heq : H+1-(h+1)+1 = H-h+1 := by omega
    simp only [stageWeight, heq]

/-- The source stage maximum is nonnegative under its empty-maximum convention. -/
theorem stagew_nonneg (β : ℕ → ℝ) (H : ℕ) : 0 ≤ Weights.stagew β H := by
  have hs := Finset.le_sup' (Weights.stageLowTerm β H)
    (show 0 ∈ insert 0 (Finset.Icc 1 (H-1)) by simp)
  simpa [Weights.stagew, Weights.stageLowTerm] using hs

theorem stageWsq_nonneg (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (H : ℕ) : 0 ≤ Weights.stageWsq β (H+1) := by
  rw [← sum_stageWeight]
  exact Finset.sum_nonneg (fun h _ => stageWeight_nonneg β hβ H h)


/-- The low coefficient is a member of the exact stage-dependent maximum. -/
theorem low_coefficient_le_stagew (β : ℕ → ℝ) (H h : ℕ) (hh : h < H) :
    ((H-h : ℕ) : ℝ) / β (h+1) * (Weights.prefixMass β h)⁻¹ ≤
      Weights.stagew β (H+1) := by
  have hm : h+1 ∈ insert 0 (Finset.Icc 1 ((H+1)-1)) := by
    apply Finset.mem_insert_of_mem
    simp only [Nat.add_sub_cancel]
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hs := Finset.le_sup' (Weights.stageLowTerm β (H+1)) hm
  have heq : H+1-(h+1) = H-h := by omega
  have hcoef : ((H-h : ℕ) : ℝ) / β (h+1) * (Weights.prefixMass β h)⁻¹ =
      ((H-h : ℕ) : ℝ) / Weights.prefixMass β (h+1) := by
    rw [Weights.prefixMass_succ]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hcoef]
  simpa only [Weights.stagew, Weights.stageLowTerm, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceIte, heq] using hs

/-- The squared high coefficient includes exactly the current mass and every
previous mass, giving the source prefix weight without an off-by-one exponent. -/
theorem high_coefficient_square (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (H h : ℕ) :
    (2 * Real.sqrt 2 * (((H-h : ℕ) : ℝ)+1) / Real.sqrt (β (h+1)))^2 *
      (Weights.prefixMass β h)⁻¹ = 8 * stageWeight β H h := by
  have hs := Weights.stage_high_coefficient (α := β) (((H-h : ℕ) : ℝ)+1)
    (h := h+1) (by omega) (hβ (h+1)).1
  simpa only [Nat.add_sub_cancel, stageWeight, Nat.cast_add, Nat.cast_one,
    div_eq_mul_inv, mul_assoc] using hs

/-- C.7 with the B.3 weights, by instantiating the already proved generic CS. -/
theorem high_count_aggregate_stage (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (K H : ℕ) (Y : ℕ → ℕ → ℝ)
    (hY : ∀ k h, 0 ≤ Y k h) :
    (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
      4 * Real.sqrt (Λ * stageWeight β H h * Y k h)) ≤
      4 * Real.sqrt (Weights.stageWsq β (H+1)) *
        Real.sqrt (Λ * (K : ℝ) * (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, Y k h)) := by
  have hs := high_count_aggregate_generic hΛ K H (stageWeight β H)
    (stageWeight_nonneg β hβ H) Y hY
  simpa only [sum_stageWeight] using hs

/-- A stage of the actual stage-dependent nested risk: local hybrid CVaR,
Jensen and the actual prefix occupancy domination are all applied here. -/
theorem actual_hybrid_stage (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (H k h : ℕ) (hh : h < H)
    (hrow : ∀ s a, H+1 ≤ N k (s,a) →
      hellingerSq (p s a) (q k s a) ≤ 2 * Λ / N k (s,a)) :
    let d := occupancy (StageRisk.adverseKernel β hβ c (π k) p (H+1)) (dirac s₀) h
    expect d.mass (StageRisk.localError β c (π k) p (q k) (H-h) h) ≤
      Weights.stagew β (H+1) * nominalLow π p s₀ N H k h +
      4 * Real.sqrt (Λ * stageWeight β H h * nominalHigh π p s₀ N H k h) := by
  classical
  let d := occupancy (StageRisk.adverseKernel β hβ c (π k) p (H+1)) (dirac s₀) h
  let dn := occupancy (nominal (π k) p) (dirac s₀) h
  let R : ℝ := ((H-h : ℕ) : ℝ)
  let κ : ℝ := (Weights.prefixMass β h)⁻¹
  let X : S → ℝ := fun s => ∑ a, if H+1 ≤ N k (s,a) then
    (π k h s).mass a * hellingerSq (p s a) (q k s a) else 0
  let L : ℝ := (R / β (h+1)) * (∑ s, d.mass s * ∑ a,
    if H+1 ≤ N k (s,a) then 0 else (π k h s).mass a * tv (p s a) (q k s a))
  let C : ℝ := 2 * Real.sqrt 2 * (R+1) / Real.sqrt (β (h+1))
  have hκ : 0 ≤ κ := inv_nonneg.2 (Weights.prefixMass_pos (fun j _ => (hβ j).1)).le
  have hlocal : ∀ s, StageRisk.localError β c (π k) p (q k) (H-h) h s ≤
      (R / β (h+1)) * (∑ a, if H+1 ≤ N k (s,a) then 0 else
        (π k h s).mass a * tv (p s a) (q k s a)) + C * Real.sqrt (X s) := by
    intro s
    have hs := StageRisk.localError_hybrid β hβ c hc (π k) p (q k) (H-h) h s
      (Finset.univ.filter (fun a => H+1 ≤ N k (s,a)))
    simpa [R, C, X] using hs
  have hsim := expect_mono d.nonneg hlocal
  have hsim' : expect d.mass (StageRisk.localError β c (π k) p (q k) (H-h) h) ≤
      L + C * (∑ s, d.mass s * Real.sqrt (X s)) := by
    convert hsim using 1 <;>
      simp only [expect, L, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]
  have hdom : ∀ s a, d.mass s * (π k h s).mass a ≤ κ * (dn.mass s * (π k h s).mass a) :=
    fun s a => StageRisk.distorted_action_domination β hβ c (π k) p (H+1) h s₀ s a
  have hlow := low_stage_domination d dn (π k h) p (q k) (fun s a => N k (s,a)) (H+1)
    (R := R) (α := β (h+1)) (κ := κ) (Nat.cast_nonneg _) (hβ (h+1)).1 hκ
    (low_coefficient_le_stagew β H h hh) hdom
  have hlo : L ≤ Weights.stagew β (H+1) * nominalLow π p s₀ N H k h := by
    convert hlow using 1
    unfold nominalLow nominalMass
    rw [Fintype.sum_prod_type]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro a _
    by_cases hi : H+1 ≤ N k (s,a)
    · simp [hi, Nat.not_lt.mpr hi]
    · simp [hi, Nat.lt_of_not_ge hi, dn]
  have hhigh := high_stage_jensen d dn (π k h) p (q k) (fun s a => N k (s,a)) (H+1)
    (κ := κ) (Λ := Λ) hκ hΛ hdom hrow
  have hhi : (∑ s, d.mass s * Real.sqrt (X s)) ≤
      Real.sqrt (2 * Λ * κ * nominalHigh π p s₀ N H k h) := by
    convert hhigh using 1
    unfold nominalHigh nominalMass
    rw [Fintype.sum_prod_type]
  have hC : 0 ≤ C := by
    dsimp [C, R]
    have hb := (hβ (h+1)).1
    positivity
  have hhi' := mul_le_mul_of_nonneg_left hhi hC
  have hid := high_term_from_square hC hκ (stageWeight_nonneg β hβ H h) hΛ
    (nominalHigh_nonneg π p s₀ N H k h) (high_coefficient_square β hβ H h)
  dsimp only
  linarith

/-- The B.3 pathwise hybrid simulation with the literal stage-dependent risk
and the literal prefix weights. The nominal occupancy/count objects are unchanged. -/
theorem risk_hybrid_sum_bound_stage (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (K H : ℕ) (hrow : ∀ k, k < K → ∀ s a, H+1 ≤ N k (s,a) →
      hellingerSq (p s a) (q k s a) ≤ 2 * Λ / N k (s,a)) :
    (∑ k ∈ Finset.range K,
      (StageRisk.risk β c (π k) p (H+1) 0 s₀ - StageRisk.risk β c (π k) (q k) (H+1) 0 s₀)) ≤
      Weights.stagew β (H+1) * Ylo π p s₀ N K H +
      4 * Real.sqrt (Weights.stageWsq β (H+1)) * Real.sqrt (Λ * (K : ℝ) * Yhi π p s₀ N K H) := by
  have hsum : (∑ k ∈ Finset.range K,
      (StageRisk.risk β c (π k) p (H+1) 0 s₀ - StageRisk.risk β c (π k) (q k) (H+1) 0 s₀)) ≤
      ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
        (Weights.stagew β (H+1) * nominalLow π p s₀ N H k h +
         4 * Real.sqrt (Λ * stageWeight β H h * nominalHigh π p s₀ N H k h)) := by
    apply Finset.sum_le_sum
    intro k hk
    apply (StageRisk.distorted_simulation_transitions β hβ c (π k) p (q k) H s₀).trans
    apply Finset.sum_le_sum
    intro h hh
    exact actual_hybrid_stage β hβ c hc π p q s₀ N hΛ H k h
      (Finset.mem_range.1 hh) (hrow k (Finset.mem_range.1 hk))
  have hhigh := high_count_aggregate_stage β hβ hΛ K H (nominalHigh π p s₀ N H)
    (nominalHigh_nonneg π p s₀ N H)
  simp only [Finset.sum_add_distrib] at hsum
  have hloweq : (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
      Weights.stagew β (H+1) * nominalLow π p s₀ N H k h) =
      Weights.stagew β (H+1) * Ylo π p s₀ N K H := by
    simp only [Ylo, Finset.mul_sum]
  rw [hloweq] at hsum
  change _ ≤ 4 * Real.sqrt (Weights.stageWsq β (H+1)) *
    Real.sqrt (Λ * (K : ℝ) * Yhi π p s₀ N K H) at hhigh
  linarith

/-- Episodewise masking for B.3, preserving the source's separate true-prefix
and posterior-sample failure accounting in expected risk simulation. -/
theorem masked_risk_hybrid_sum_bound_stage (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (K H : ℕ) (good : ℕ → Prop) [DecidablePred good]
    (hrow : ∀ k, k < K → good k → ∀ s a, H+1 ≤ N k (s,a) →
      hellingerSq (p s a) (q k s a) ≤ 2 * Λ / N k (s,a)) :
    (∑ k ∈ Finset.range K, if good k then
      (StageRisk.risk β c (π k) p (H+1) 0 s₀ - StageRisk.risk β c (π k) (q k) (H+1) 0 s₀) else 0) ≤
      Weights.stagew β (H+1) * Ylo π p s₀ N K H +
      4 * Real.sqrt (Weights.stageWsq β (H+1)) * Real.sqrt (Λ * (K : ℝ) * Yhi π p s₀ N K H) := by
  classical
  let q' : ℕ → Kernel S A := fun k => if good k then q k else p
  have hrow' : ∀ k, k < K → ∀ s a, H+1 ≤ N k (s,a) →
      hellingerSq (p s a) (q' k s a) ≤ 2 * Λ / N k (s,a) := by
    intro k hk s a hn
    by_cases hg : good k
    · simpa [q', hg] using hrow k hk hg s a hn
    · simp only [q', if_neg hg, hellingerSq_self]
      positivity
  have hs := risk_hybrid_sum_bound_stage β hβ c hc π p q' s₀ N hΛ K H hrow'
  convert hs using 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hg : good k <;> simp [q', hg]

end
end Paper36.StageCharging
