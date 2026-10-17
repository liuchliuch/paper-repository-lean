import Paper36.Simulation
import Paper36.Weights

/-! The stage-dependent CVaR extension (B.3), with source stage masses β(1),β(2),...
and the actual adverse probability laws. All physical-state policies, kernels,
nominal trajectories and posterior observations remain the same objects. -/
namespace Paper36.StageRisk
open Paper36.CVaR Paper36.Simulation
open scoped BigOperators
noncomputable section
variable {S A : Type*} [Fintype S] [Fintype A]

def risk (β : ℕ → ℝ) (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A) :
    ℕ → ℕ → S → ℝ
  | 0, _, _ => 0
  | n+1, h, s => value (joint (π h s) (p s)) (β (h+1))
      (fun x => c h s x.1 + risk β c π p n (h+1) x.2)

lemma risk_bounds (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Policy S A) (p : Kernel S A) (n h : ℕ) (s : S) :
    0 ≤ risk β c π p n h s ∧ risk β c π p n h s ≤ n := by
  induction n generalizing h s with
  | zero => simp [risk]
  | succ n ih =>
    apply value_bounds _ (hβ (h+1)).1 (hβ (h+1)).2
    · intro x
      exact add_nonneg (hc h s x.1).1 (ih (h+1) x.2).1
    · intro x
      have hi := (ih (h+1) x.2).2
      have hc' := (hc h s x.1).2
      push_cast
      linarith

lemma constant_risk (α : ℝ) (c : ℕ → S → A → ℝ) (π : Policy S A)
    (p : Kernel S A) (n h : ℕ) (s : S) :
    risk (fun _ => α) c π p n h s = Simulation.risk α c π p n h s := by
  induction n generalizing h s with
  | zero => rfl
  | succ n ih => simp only [risk, Simulation.risk]; simp_rw [ih]

def adverse (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (n h : ℕ) (s : S) : Law (A × S) :=
  let ex := exists_optimizer (joint (π h s) (p s)) (hβ (h+1)).1 (hβ (h+1)).2
    (fun x => c h s x.1 + risk β c π p n (h+1) x.2)
  ⟨Classical.choose ex, (Classical.choose_spec ex).1.1,
    (Classical.choose_spec ex).1.2.2⟩

lemma adverse_envelope (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A) (n h : ℕ) (s : S) :
    Envelope (joint (π h s) (p s)) (β (h+1)) (adverse β hβ c π p n h s).mass :=
  (Classical.choose_spec (exists_optimizer (joint (π h s) (p s)) (hβ (h+1)).1 (hβ (h+1)).2
    (fun x => c h s x.1 + risk β c π p n (h+1) x.2))).1

lemma adverse_optimal (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A) (n h : ℕ) (s : S) :
    risk β c π p (n+1) h s = expect (adverse β hβ c π p n h s).mass
      (fun x => c h s x.1 + risk β c π p n (h+1) x.2) :=
  (Classical.choose_spec (exists_optimizer (joint (π h s) (p s)) (hβ (h+1)).1 (hβ (h+1)).2
    (fun x => c h s x.1 + risk β c π p n (h+1) x.2))).2

def adverseKernel (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (H h : ℕ) (s : S) : Law S :=
  stateMarginal (adverse β hβ c π p (H-(h+1)) h s)

lemma adverseKernel_domination (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (H h : ℕ) (s t : S) :
    (adverseKernel β hβ c π p H h s).mass t ≤
      (β (h+1))⁻¹ * (nominal π p h s).mass t := by
  change (∑ a, (adverse β hβ c π p (H-(h+1)) h s).mass (a,t)) ≤
    (β (h+1))⁻¹ * ∑ a, (joint (π h s) (p s)).mass (a,t)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simpa only [div_eq_mul_inv, mul_comm] using
    (adverse_envelope β hβ c π p (H-(h+1)) h s).2.1 (a,t)

/-- The actual state-marginal density cap is exactly the reciprocal prefix product. -/
theorem occupancy_domination (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (H h : ℕ) (s₀ s : S) :
    (occupancy (adverseKernel β hβ c π p H) (dirac s₀) h).mass s ≤
      (Weights.prefixMass β h)⁻¹ * (occupancy (nominal π p) (dirac s₀) h).mass s := by
  induction h generalizing s with
  | zero => simp [occupancy]
  | succ h ih =>
    change (∑ t, (occupancy (adverseKernel β hβ c π p H) (dirac s₀) h).mass t *
        (adverseKernel β hβ c π p H h t).mass s) ≤
      (Weights.prefixMass β (h+1))⁻¹ * ∑ t,
        (occupancy (nominal π p) (dirac s₀) h).mass t * (nominal π p h t).mass s
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    calc
      _ ≤ ((Weights.prefixMass β h)⁻¹ * (occupancy (nominal π p) (dirac s₀) h).mass t) *
          ((β (h+1))⁻¹ * (nominal π p h t).mass s) :=
        mul_le_mul (ih t) (adverseKernel_domination β hβ c π p H h t s)
          ((adverseKernel β hβ c π p H h t).nonneg s)
          (mul_nonneg (inv_nonneg.mpr
            (Weights.prefixMass_pos (fun j _ => (hβ j).1)).le)
            ((occupancy (nominal π p) (dirac s₀) h).nonneg t))
      _ = _ := by rw [Weights.prefixMass_succ, mul_inv]; ring

/-- Multiplication by the same current action row preserves domination, even at zero occupancy. -/
theorem distorted_action_domination (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (H h : ℕ) (s₀ s : S) (a : A) :
    (occupancy (adverseKernel β hβ c π p H) (dirac s₀) h).mass s * (π h s).mass a ≤
      (Weights.prefixMass β h)⁻¹ *
        ((occupancy (nominal π p) (dirac s₀) h).mass s * (π h s).mass a) := by
  have hh := mul_le_mul_of_nonneg_right (occupancy_domination β hβ c π p H h s₀ s)
    ((π h s).nonneg a)
  simpa only [mul_assoc] using hh

def localError (β : ℕ → ℝ) (c : ℕ → S → A → ℝ) (π : Policy S A)
    (p q : Kernel S A) (n h : ℕ) (s : S) : ℝ :=
  |value (joint (π h s) (p s)) (β (h+1))
    (fun x => c h s x.1 + risk β c π q n (h+1) x.2) -
   value (joint (π h s) (q s)) (β (h+1))
    (fun x => c h s x.1 + risk β c π q n (h+1) x.2)|

theorem simulation_step (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A)
    (n h : ℕ) (s : S) :
    risk β c π p (n+1) h s - risk β c π q (n+1) h s ≤
      expect (stateMarginal (adverse β hβ c π p n h s)).mass
        (fun t => risk β c π p n (h+1) t - risk β c π q n (h+1) t) +
      localError β c π p q n h s := by
  have hd := Simulation.optimizer_difference (joint (π h s) (p s)) (β (h+1))
    (hβ (h+1)).1 (hβ (h+1)).2
    (fun x => c h s x.1 + risk β c π p n (h+1) x.2)
    (fun x => c h s x.1 + risk β c π q n (h+1) x.2)
    (adverse β hβ c π p n h s).mass (adverse_envelope β hβ c π p n h s)
    (adverse_optimal β hβ c π p n h s)
  rw [stateMarginal_expect]
  have he : (fun x : A × S => (c h s x.1 + risk β c π p n (h+1) x.2) -
      (c h s x.1 + risk β c π q n (h+1) x.2)) =
      (fun x => risk β c π p n (h+1) x.2 - risk β c π q n (h+1) x.2) := by
    funext x; ring
  rw [he] at hd
  have hab := le_abs_self (value (joint (π h s) (p s)) (β (h+1))
    (fun x => c h s x.1 + risk β c π q n (h+1) x.2) -
    value (joint (π h s) (q s)) (β (h+1))
    (fun x => c h s x.1 + risk β c π q n (h+1) x.2))
  unfold localError
  change value _ _ _ - value _ _ _ ≤ _
  change value _ _ _ - value _ _ _ ≤ _ at hd
  linarith

/-- Distorted simulation is unchanged except for its actual stage-dependent adverse laws. -/
theorem distorted_simulation (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A) (H : ℕ) (s₀ : S) :
    risk β c π p H 0 s₀ - risk β c π q H 0 s₀ ≤
      ∑ h ∈ Finset.range H, expect
        (occupancy (adverseKernel β hβ c π p H) (dirac s₀) h).mass
        (localError β c π p q (H-(h+1)) h) := by
  let δ := fun h s => risk β c π p (H-h) h s - risk β c π q (H-h) h s
  let e := fun h => localError β c π p q (H-(h+1)) h
  have hs (h : ℕ) (hh : h < H) (s : S) : δ h s ≤
      expect (adverseKernel β hβ c π p H h s).mass (δ (h+1)) + e h s := by
    have heq : H-h = (H-(h+1))+1 := by omega
    simpa only [δ, e, adverseKernel, heq] using simulation_step β hβ c π p q (H-(h+1)) h s
  have hu := Simulation.unroll (adverseKernel β hβ c π p H) (dirac s₀) δ e H hs
  rw [expect_dirac] at hu
  have hz : δ H = fun _ => 0 := by funext s; simp [δ, risk]
  rw [hz, expect_const (occupancy (adverseKernel β hβ c π p H) (dirac s₀) H).total] at hu
  simpa only [δ, e, Nat.sub_zero, zero_add] using hu

lemma localError_tv (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Policy S A) (p q : Kernel S A) (n h : ℕ) (s : S) :
    localError β c π p q n h s ≤ (n : ℝ)/β (h+1) *
      ∑ a, (π h s).mass a * tv (p s a) (q s a) :=
  value_joint_tv (π h s) (p s) (q s) (hβ (h+1)).1 (hβ (h+1)).2
    (Nat.cast_nonneg n) (c h s) (risk β c π q n (h+1))
    (fun t => (risk_bounds β hβ c hc π q n (h+1) t).1)
    (fun t => (risk_bounds β hβ c hc π q n (h+1) t).2)

lemma localError_hybrid [DecidableEq A] (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Policy S A) (p q : Kernel S A) (n h : ℕ) (s : S) (I : Finset A) :
    localError β c π p q n h s ≤
      ((n : ℝ)/β (h+1))*(∑ a, if a ∈ I then 0 else (π h s).mass a*tv (p s a) (q s a)) +
      (2*Real.sqrt 2*((n : ℝ)+1)/Real.sqrt (β (h+1)))*
        Real.sqrt (∑ a, if a ∈ I then (π h s).mass a*hellingerSq (p s a) (q s a) else 0) :=
  value_joint_hybrid (π h s) (p s) (q s) (hβ (h+1)).1 (hβ (h+1)).2
    (Nat.cast_nonneg n) (c h s) (risk β c π q n (h+1))
    (fun a => (hc h s a).1) (fun a => (hc h s a).2)
    (fun t => (risk_bounds β hβ c hc π q n (h+1) t).1)
    (fun t => (risk_bounds β hβ c hc π q n (h+1) t).2) I

lemma localError_zero (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A) (h : ℕ) (s : S) :
    localError β c π p q 0 h s = 0 := by
  unfold localError
  simp only [risk, add_zero]
  rw [Simulation.action_only (π h s) (p s) (q s) (β (h+1))
    (hβ (h+1)).1 (hβ (h+1)).2 (c h s)]
  simp

/-- The last stage has no transition error, so precisely H-1 stages contribute. -/
theorem distorted_simulation_transitions (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A) (H : ℕ) (s₀ : S) :
    risk β c π p (H+1) 0 s₀ - risk β c π q (H+1) 0 s₀ ≤
      ∑ h ∈ Finset.range H, expect
        (occupancy (adverseKernel β hβ c π p (H+1)) (dirac s₀) h).mass
        (localError β c π p q (H-h) h) := by
  have hh := distorted_simulation β hβ c π p q (H+1) s₀
  rw [Finset.sum_range_succ] at hh
  have hz : localError β c π p q (H+1-(H+1)) H = fun _ => 0 := by
    funext s
    simpa only [Nat.sub_self] using localError_zero β hβ c π p q H s
  rw [hz, expect_const (occupancy (adverseKernel β hβ c π p (H+1)) (dirac s₀) H).total,
    add_zero] at hh
  have heq (h : ℕ) : H+1-(h+1) = H-h := by omega
  simpa only [heq] using hh

end
end Paper36.StageRisk
