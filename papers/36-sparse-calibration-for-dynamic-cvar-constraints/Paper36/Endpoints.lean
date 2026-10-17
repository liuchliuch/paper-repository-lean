import Paper36.CVaR
import Paper36.Nested
import Paper36.Assembly
import Paper36.Weights

/-! The finite-risk endpoints and the precise limitation of signed debt.
These results use the actual CVaR envelope and actual Nested Markov recursions.
The final counterexample is a one-state, two-action, one-stage MDP with costs
zero and one. Its signed debt is nonpositive at every horizon, while its
positive-part debt grows without bound.
-/
namespace Paper36.Endpoints

open scoped BigOperators
open Set Paper36.Regularity
noncomputable section

section TailOne
variable {Ω : Type*} [Fintype Ω]

/-- At tail mass one the finite risk envelope contains exactly the nominal law. -/
theorem envelope_one_unique (P : CVaR.Law Ω) {w : Ω → ℝ}
    (hw : CVaR.Envelope P 1 w) : w = P.mass := by
  have hn : ∀ i ∈ Finset.univ, 0 ≤ P.mass i - w i := by
    intro i _
    have h := hw.2.1 i
    simp only [div_one] at h
    linarith
  have hs : (∑ i, (P.mass i - w i)) = 0 := by
    rw [Finset.sum_sub_distrib, P.total, hw.2.2]
    ring
  funext i
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).1 hs i (Finset.mem_univ i)
  linarith

/-- The literal envelope CVaR is expectation when α=1 (Remark B.2). -/
theorem cvar_one_eq_expectation (P : CVaR.Law Ω) (X : Ω → ℝ) :
    CVaR.value P 1 X = CVaR.expect P.mass X := by
  obtain ⟨w, hw, hv⟩ := CVaR.exists_optimizer P (α := 1) (by norm_num) le_rfl X
  rw [hv, envelope_one_unique P hw]

/-- No distortion of any nominal probability is available at α=1. -/
theorem distortion_one (P : CVaR.Law Ω) {w : Ω → ℝ}
    (hw : CVaR.Envelope P 1 w) (i : Ω) : w i = P.mass i := by
  rw [envelope_one_unique P hw]

/-- The compact primal used in the Nested recursion agrees with expectation at α=1. -/
theorem compact_one_eq_expectation (B : ℝ) (hB : 0 ≤ B)
    (P : Law Ω) (X : Ω → ℝ) (hX : ∀ i, 0 ≤ X i) :
    compactCVaR 1 B P X = expectation P X := by
  apply le_antisymm
  · apply (compactCVaR_le 1 B hB P X ⟨le_rfl, hB⟩).trans_eq
    have heq : (fun i => max (X i - 0) 0) = X := by
      funext i
      simp [max_eq_left (hX i)]
    change 0 + (1 : ℝ)⁻¹ * expectation P (fun i => max (X i - 0) 0) = expectation P X
    rw [heq]
    norm_num
  · apply le_compactCVaR 1 B hB
    intro z hz
    have hm := expectation_mono P (fun i => le_max_left (X i - z) 0)
    have hs : expectation P (fun i => X i - z) = expectation P X - z := by
      simp only [expectation, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
        law_sum P, one_mul]
    rw [hs] at hm
    simp only [objective, inv_one, one_mul]
    linarith

end TailOne

section MarkovEndpoints
variable {S A : Type*} [Fintype S] [Fintype A]

/-- A joint action-successor expectation factors in the usual Markov way. -/
theorem joint_expectation (l : Law A) (q : A → Law S) (X : A → S → ℝ) :
    expectation (Nested.joint l q) (fun x => X x.1 x.2) =
      ∑ a, l a * ∑ s, q a s * X a s := by
  simp only [expectation, Nested.joint, Subtype.coe_mk, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  change (l a * q a s) * X a s = l a * (q a s * X a s)
  ring

/-- Successor randomness has no effect on an action-only loss. -/
theorem joint_action_expectation (l : Law A) (q : A → Law S) (X : A → ℝ) :
    expectation (Nested.joint l q) (fun x => X x.1) = expectation l X := by
  rw [joint_expectation l q (fun a _ => X a)]
  unfold expectation
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_mul, law_sum (q a), one_mul]

/-- The threshold objective of an action-only loss ignores the transition row. -/
theorem joint_action_objective (α : ℝ) (l : Law A) (q : A → Law S)
    (X : A → ℝ) (z : ℝ) :
    objective α (Nested.joint l q) (fun x => X x.1) z = objective α l X z := by
  simp only [objective]
  rw [joint_action_expectation l q (fun a => max (X a - z) 0)]

theorem joint_action_cvar (α B : ℝ) (l : Law A) (q : A → Law S) (X : A → ℝ) :
    compactCVaR α B (Nested.joint l q) (fun x => X x.1) = compactCVaR α B l X := by
  have hf : objective α (Nested.joint l q) (fun x => X x.1) = objective α l X := by
    funext z
    exact joint_action_objective α l q X z
  simp only [compactCVaR, hf]

/-- At α=1 the entire nested-risk recursion is the ordinary expected cost recursion. -/
theorem nested_one_eq_expected_cost (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (π : Nested.Policy S A) (q : Nested.Kernel S A) (n h : ℕ) (s : S) :
    Nested.risk 1 c π q n h s = Nested.reward c π q n h s := by
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
      rw [Nested.risk]
      have hnonneg : ∀ x : A × S,
          0 ≤ c h s x.1 + Nested.risk 1 c π q n (h + 1) x.2 := by
        intro x
        exact add_nonneg (hc h s x.1).1
          (Nested.risk_bounds 1 (by norm_num) c hc π q n (h + 1) x.2).1
      rw [compact_one_eq_expectation _ (by positivity) _ _ hnonneg,
        joint_expectation (π h s) (q s)
          (fun a t => c h s a + Nested.risk 1 c π q n (h + 1) t)]
      simp_rw [ih]
      rw [Nested.reward]
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
        law_sum (q s a), one_mul]

/-- With one stage, risk contains only the selected action row and known costs. -/
theorem one_stage_risk (α : ℝ) (c : ℕ → S → A → ℝ)
    (π : Nested.Policy S A) (q : Nested.Kernel S A) (h : ℕ) (s : S) :
    Nested.risk α c π q 1 h s = compactCVaR α 1 (π h s) (c h s) := by
  simp only [Nested.risk, Nat.cast_one, add_zero]
  simpa only [Nat.zero_add, Nat.cast_one] using
    joint_action_cvar α 1 (π h s) (q s) (c h s)

/-- With one stage, reward also contains no transition model. -/
theorem one_stage_reward (r : ℕ → S → A → ℝ)
    (π : Nested.Policy S A) (q : Nested.Kernel S A) (h : ℕ) (s : S) :
    Nested.reward r π q 1 h s = expectation (π h s) (r h s) := by
  simp [Nested.reward, expectation]

theorem one_stage_model_independent (α : ℝ) (c r : ℕ → S → A → ℝ)
    (π : Nested.Policy S A) (p q : Nested.Kernel S A) (h : ℕ) (s : S) :
    Nested.risk α c π p 1 h s = Nested.risk α c π q 1 h s ∧
      Nested.reward r π p 1 h s = Nested.reward r π q 1 h s := by
  constructor
  · rw [one_stage_risk, one_stage_risk]
  · rw [one_stage_reward, one_stage_reward]

/-- Exact one-stage sampled-model planning is exact true-model planning. -/
theorem one_stage_exact_oracle (α τ : ℝ) (c r : ℕ → S → A → ℝ)
    (p q : Nested.Kernel S A) (h : ℕ) (s : S) (π comparator : Nested.Policy S A)
    (hcf : Nested.risk α c comparator p 1 h s ≤ τ)
    (hco : ∀ π', Nested.risk α c π' p 1 h s ≤ τ →
      Nested.reward r π' p 1 h s ≤ Nested.reward r comparator p 1 h s)
    (hπf : Nested.risk α c π q 1 h s ≤ τ)
    (hπo : ∀ π', Nested.risk α c π' q 1 h s ≤ τ →
      Nested.reward r π' q 1 h s ≤ Nested.reward r π q 1 h s) :
    Nested.risk α c π p 1 h s - τ ≤ 0 ∧
      Nested.reward r comparator p 1 h s - Nested.reward r π p 1 h s = 0 := by
  have hrπ := (one_stage_model_independent α c r π p q h s).1
  have hvπ := (one_stage_model_independent α c r π p q h s).2
  have hrc := (one_stage_model_independent α c r comparator p q h s).1
  have hvc := (one_stage_model_independent α c r comparator p q h s).2
  have hp : Nested.risk α c π p 1 h s ≤ τ := by rwa [hrπ]
  have hlo := hco π hp
  have hhi := hπo comparator (by rwa [← hrc])
  rw [← hvc, ← hvπ] at hhi
  constructor <;> linarith

/-- Corollary B.1 at H=1: certified errors accumulate without model error. -/
theorem one_stage_approximate_oracles (α τ : ℝ) (c r : ℕ → S → A → ℝ)
    (p : Nested.Kernel S A) (q : ℕ → Nested.Kernel S A)
    (π : ℕ → Nested.Policy S A) (comparator : Nested.Policy S A)
    (h : ℕ) (s : S) (ε ζ : ℕ → ℝ)
    (hcf : Nested.risk α c comparator p 1 h s ≤ τ)
    (hπf : ∀ n, Nested.risk α c (π n) (q n) 1 h s ≤ τ + ε n)
    (hπo : ∀ n π', Nested.risk α c π' (q n) 1 h s ≤ τ →
      Nested.reward r π' (q n) 1 h s ≤ Nested.reward r (π n) (q n) 1 h s + ζ n)
    (K : ℕ) :
    (∑ n ∈ Finset.range K, (Nested.risk α c (π n) p 1 h s - τ)) ≤
      (∑ n ∈ Finset.range K, ε n) ∧
    (∑ n ∈ Finset.range K, (Nested.reward r comparator p 1 h s -
      Nested.reward r (π n) p 1 h s)) ≤ (∑ n ∈ Finset.range K, ζ n) := by
  constructor
  · apply Finset.sum_le_sum
    intro n hn
    have hm := (one_stage_model_independent α c r (π n) p (q n) h s).1
    have hf := hπf n
    rw [← hm] at hf
    linarith
  · apply Finset.sum_le_sum
    intro n hn
    have hcmodel := (one_stage_model_independent α c r comparator p (q n) h s).1
    have hcv := (one_stage_model_independent α c r comparator p (q n) h s).2
    have hpv := (one_stage_model_independent α c r (π n) p (q n) h s).2
    have hh := hπo n comparator (by rwa [← hcmodel])
    rw [← hcv, ← hpv] at hh
    linarith

/-- The exact oracle H=1 endpoint holds on every path, for every horizon. -/
theorem one_stage_exact_oracles (α τ : ℝ) (c r : ℕ → S → A → ℝ)
    (p : Nested.Kernel S A) (q : ℕ → Nested.Kernel S A)
    (π : ℕ → Nested.Policy S A) (comparator : Nested.Policy S A)
    (h : ℕ) (s : S)
    (hcf : Nested.risk α c comparator p 1 h s ≤ τ)
    (hco : ∀ π', Nested.risk α c π' p 1 h s ≤ τ →
      Nested.reward r π' p 1 h s ≤ Nested.reward r comparator p 1 h s)
    (hπf : ∀ n, Nested.risk α c (π n) (q n) 1 h s ≤ τ)
    (hπo : ∀ n π', Nested.risk α c π' (q n) 1 h s ≤ τ →
      Nested.reward r π' (q n) 1 h s ≤ Nested.reward r (π n) (q n) 1 h s)
    (K : ℕ) :
    (∑ n ∈ Finset.range K, (Nested.risk α c (π n) p 1 h s - τ)) ≤ 0 ∧
    (∑ n ∈ Finset.range K, (Nested.reward r comparator p 1 h s -
      Nested.reward r (π n) p 1 h s)) = 0 := by
  constructor
  · apply Finset.sum_nonpos
    intro n hn
    exact (one_stage_exact_oracle α τ c r p (q n) h s (π n) comparator
      hcf hco (hπf n) (hπo n)).1
  · apply Finset.sum_eq_zero
    intro n hn
    exact (one_stage_exact_oracle α τ c r p (q n) h s (π n) comparator
      hcf hco (hπf n) (hπo n)).2

/-- The H=1 Bayesian endpoint on an arbitrary finite probability space. The
latent kernel, posterior kernels and all selected policies may be dependent;
model independence of the one-stage values eliminates every model-error term. -/
theorem one_stage_bayesian_exact {Ξ : Type*} [Fintype Ξ] (P : Law Ξ)
    (α τ : ℝ) (c r : ℕ → S → A → ℝ)
    (p : Ξ → Nested.Kernel S A) (q : ℕ → Ξ → Nested.Kernel S A)
    (π : ℕ → Ξ → Nested.Policy S A) (comparator : Ξ → Nested.Policy S A)
    (h : ℕ) (s : S)
    (hcf : ∀ ω, Nested.risk α c (comparator ω) (p ω) 1 h s ≤ τ)
    (hco : ∀ ω π', Nested.risk α c π' (p ω) 1 h s ≤ τ →
      Nested.reward r π' (p ω) 1 h s ≤ Nested.reward r (comparator ω) (p ω) 1 h s)
    (hπf : ∀ ω n, Nested.risk α c (π n ω) (q n ω) 1 h s ≤ τ)
    (hπo : ∀ ω n π', Nested.risk α c π' (q n ω) 1 h s ≤ τ →
      Nested.reward r π' (q n ω) 1 h s ≤ Nested.reward r (π n ω) (q n ω) 1 h s)
    (K : ℕ) :
    expectation P (fun ω => ∑ n ∈ Finset.range K,
      (Nested.risk α c (π n ω) (p ω) 1 h s - τ)) ≤ 0 ∧
    expectation P (fun ω => ∑ n ∈ Finset.range K,
      (Nested.reward r (comparator ω) (p ω) 1 h s -
        Nested.reward r (π n ω) (p ω) 1 h s)) = 0 := by
  have hp ω := one_stage_exact_oracles α τ c r (p ω) (fun n => q n ω)
    (fun n => π n ω) (comparator ω) h s (hcf ω) (hco ω) (hπf ω) (hπo ω) K
  constructor
  · have hm := expectation_mono P (fun ω => (hp ω).1)
    simpa using hm
  · have heq : (fun ω => ∑ n ∈ Finset.range K,
        (Nested.reward r (comparator ω) (p ω) 1 h s -
          Nested.reward r (π n ω) (p ω) 1 h s)) = fun _ => 0 := by
      funext ω
      exact (hp ω).2
    rw [heq, expectation_const]

/-- Certified H=1 exploitation errors give exactly the cumulative-error bounds
of Corollary B.1, under a genuine finite prior over complete random paths. -/
theorem one_stage_bayesian_approximate {Ξ : Type*} [Fintype Ξ] (P : Law Ξ)
    (α τ : ℝ) (c r : ℕ → S → A → ℝ)
    (p : Ξ → Nested.Kernel S A) (q : ℕ → Ξ → Nested.Kernel S A)
    (π : ℕ → Ξ → Nested.Policy S A) (comparator : Ξ → Nested.Policy S A)
    (h : ℕ) (s : S) (ε ζ : ℕ → ℝ)
    (hcf : ∀ ω, Nested.risk α c (comparator ω) (p ω) 1 h s ≤ τ)
    (hπf : ∀ ω n, Nested.risk α c (π n ω) (q n ω) 1 h s ≤ τ + ε n)
    (hπo : ∀ ω n π', Nested.risk α c π' (q n ω) 1 h s ≤ τ →
      Nested.reward r π' (q n ω) 1 h s ≤ Nested.reward r (π n ω) (q n ω) 1 h s + ζ n)
    (K : ℕ) :
    expectation P (fun ω => ∑ n ∈ Finset.range K,
      (Nested.risk α c (π n ω) (p ω) 1 h s - τ)) ≤
      (∑ n ∈ Finset.range K, ε n) ∧
    expectation P (fun ω => ∑ n ∈ Finset.range K,
      (Nested.reward r (comparator ω) (p ω) 1 h s -
        Nested.reward r (π n ω) (p ω) 1 h s)) ≤ (∑ n ∈ Finset.range K, ζ n) := by
  have hp ω := one_stage_approximate_oracles α τ c r (p ω) (fun n => q n ω)
    (fun n => π n ω) (comparator ω) h s ε ζ (hcf ω) (hπf ω) (hπo ω) K
  constructor
  · have hm := expectation_mono P (fun ω => (hp ω).1)
    simpa using hm
  · have hm := expectation_mono P (fun ω => (hp ω).2)
    simpa using hm

/-- The exact H=1 bank is zero for the actual source weight and target. -/
theorem one_stage_zero_calibration (α s a : ℝ) (d : ℕ → ℝ) (K : ℕ) :
    Bank.bank (BankTarget.paperTarget s a 1 (Weights.W α 1)) d K = 0 ∧
      Bank.count (BankTarget.paperTarget s a 1 (Weights.W α 1)) d K = 0 := by
  have heq : BankTarget.paperTarget s a 1 (Weights.W α 1) = fun _ => 0 := by
    funext n
    simp [BankTarget.paperTarget]
  rw [heq]
  exact Bank.zero_target d K

end MarkovEndpoints

section SignedCounterexample

/-- A fixed known one-state, two-action MDP: safe action costs 0, risky action costs 1. -/
def exampleCost (_h : ℕ) (_s : Unit) (a : Bool) : ℝ := if a then 1 else 0

def exampleKernel : Nested.Kernel Unit Bool := fun _ _ => Nested.pure ()

/-- Low-risk episodes precede high-risk episodes in each two-episode cycle. -/
def alternatingPolicy (n : ℕ) : Nested.Policy Unit Bool :=
  fun _ _ => Nested.pure (decide (n % 2 = 1))

def alternatingRisk (n : ℕ) : ℝ := if n % 2 = 0 then 0 else 1

/-- Deterministic action risk equals its known cost, for every permitted tail mass. -/
theorem pure_action_cvar {A : Type*} [Fintype A] (α B : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hB : 0 ≤ B) (a : A) (X : A → ℝ)
    (hX0 : 0 ≤ X a) (hXB : X a ≤ B) :
    compactCVaR α B (Nested.pure a) X = X a := by
  have he (z : ℝ) : objective α (Nested.pure a) X z =
      z + α⁻¹ * max (X a - z) 0 := by
    classical
    simp [objective, expectation, Nested.pure, stdSimplex.vertex, Pi.single_apply]
  apply le_antisymm
  · exact (compactCVaR_le α B hB _ _ ⟨hX0, hXB⟩).trans_eq (by simp [he])
  · apply le_compactCVaR α B hB
    intro z hz
    rw [he]
    have hi : 1 ≤ α⁻¹ := (one_le_inv₀ hα).2 hα1
    have hm := mul_le_mul_of_nonneg_right hi (le_max_right (X a - z) 0)
    have hx := le_max_left (X a - z) 0
    nlinarith

/-- These are actual nested CVaR values in the fixed MDP, rather than arbitrary signed numbers. -/
theorem alternating_risk_realized (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    Nested.risk α exampleCost (alternatingPolicy n) exampleKernel 1 0 () =
      alternatingRisk n := by
  rw [one_stage_risk]
  change compactCVaR α 1 (Nested.pure (decide (n % 2 = 1)))
    (exampleCost 0 ()) = _
  rw [pure_action_cvar α 1 hα hα1 (by norm_num) _ _ (by simp [exampleCost]; split <;> norm_num)
    (by simp [exampleCost]; split <;> norm_num)]
  unfold exampleCost alternatingRisk
  by_cases hn : n % 2 = 0
  · have hn1 : n % 2 ≠ 1 := by omega
    simp [hn, hn1]
  · have hn1 : n % 2 = 1 := by omega
    simp [hn, hn1]

/-- All the risk values lie in the correct one-stage interval [0,1]. -/
theorem alternating_risk_bounds (n : ℕ) : alternatingRisk n ∈ Icc (0 : ℝ) 1 := by
  unfold alternatingRisk
  split_ifs <;> norm_num

private theorem alternating_even (K : ℕ) : alternatingRisk (2 * K) = 0 := by
  simp [alternatingRisk, Nat.mul_mod]

private theorem alternating_odd (K : ℕ) : alternatingRisk (2 * K + 1) = 1 := by
  simp [alternatingRisk, Nat.add_mod, Nat.mul_mod]

/-- At every even horizon the signed debt is exactly zero for τ=1/2. -/
theorem alternating_signed_even (K : ℕ) :
    (∑ n ∈ Finset.range (2 * K), (alternatingRisk n - (1 : ℝ) / 2)) = 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hnat : 2 * (K + 1) = (2 * K + 1) + 1 := by omega
      rw [hnat, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        alternating_even, alternating_odd]
      ring

/-- In fact a single uniform bound zero holds at every horizon, not only at even horizons. -/
theorem alternating_signed_all (N : ℕ) :
    (∑ n ∈ Finset.range N, (alternatingRisk n - (1 : ℝ) / 2)) ≤ 0 := by
  have hmod : N % 2 = 0 ∨ N % 2 = 1 := by omega
  rcases hmod with hz | ho
  · have hn : N = 2 * (N / 2) := by omega
    rw [hn, alternating_signed_even]
  · have hn : N = 2 * (N / 2) + 1 := by omega
    rw [hn, Finset.sum_range_succ, alternating_signed_even, alternating_even]
    norm_num

/-- Positive-part violations grow linearly while signed debt has the uniform upper bound zero. -/
theorem alternating_positive_even (K : ℕ) :
    (∑ n ∈ Finset.range (2 * K), max (alternatingRisk n - (1 : ℝ) / 2) 0) =
      (K : ℝ) / 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hnat : 2 * (K + 1) = (2 * K + 1) + 1 := by omega
      rw [hnat, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        alternating_even, alternating_odd]
      push_cast
      norm_num
      ring

/-- Remarks 2.2 and 5.7: no bound on signed debt, even at every horizon,
can imply a horizon-independent positive-part bound or per-episode feasibility. -/
theorem signed_guarantee_not_positive_or_safe (α G : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hG : 0 ≤ G) :
    ∃ K : ℕ,
      (∀ n, Nested.risk α exampleCost (alternatingPolicy n) exampleKernel 1 0 () ∈ Icc (0 : ℝ) 1) ∧
      (∀ N, (∑ n ∈ Finset.range N,
        (Nested.risk α exampleCost (alternatingPolicy n) exampleKernel 1 0 () - (1 : ℝ) / 2)) ≤ G) ∧
      G < (∑ n ∈ Finset.range (2 * K), max
        (Nested.risk α exampleCost (alternatingPolicy n) exampleKernel 1 0 () - (1 : ℝ) / 2) 0) ∧
      (1 : ℝ) / 2 < Nested.risk α exampleCost (alternatingPolicy 1) exampleKernel 1 0 () := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * G)
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [alternating_risk_realized α hα hα1]
    exact alternating_risk_bounds n
  · intro N
    simp_rw [alternating_risk_realized α hα hα1]
    exact (alternating_signed_all N).trans hG
  · simp_rw [alternating_risk_realized α hα hα1]
    rw [alternating_positive_even]
    linarith
  · rw [alternating_risk_realized α hα hα1]
    norm_num [alternatingRisk]

end SignedCounterexample
end
end Paper36.Endpoints
