import Paper36.Nested
import Paper36.Tightening
import Paper36.LowerBound
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Paper36.LowerBound
noncomputable section
open Finset Set Paper36.Regularity

/-- Four public states and two branches of `d` depth states.  For `d=H-2`
this is exactly `2H` states. -/
abbrev ChainState (d : ℕ) := Fin 4 ⊕ (Bool × Fin d)

def start {d : ℕ} : ChainState d := Sum.inl 0
def failure {d : ℕ} : ChainState d := Sum.inl 1
def good {d : ℕ} : ChainState d := Sum.inl 2
def bad {d : ℕ} : ChainState d := Sum.inl 3

theorem chain_state_count (H : ℕ) (hH : 2 ≤ H) :
    Fintype.card (ChainState (H-2)) = 2*H := by
  simp only [ChainState, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  omega

/-- Two-point transition law; if the points coincide their masses add. -/
def twoPoint {S : Type*} [Fintype S] (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (x y : S) : Law S :=
  ⟨fun s => α * Nested.pure x s + (1-α) * Nested.pure y s,
   fun s => add_nonneg (mul_nonneg hα ((Nested.pure x).property.1 s))
     (mul_nonneg (by linarith) ((Nested.pure y).property.1 s)), by
      simp only [sum_add_distrib, ← mul_sum, law_sum, mul_one]
      ring⟩

@[simp] theorem twoPoint_apply {S : Type*} [Fintype S] (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (x y s : S) :
    twoPoint α hα hα1 x y s = α*Nested.pure x s + (1-α)*Nested.pure y s := rfl

def endpoint {d : ℕ} (θ a : Bool) : ChainState d := if a = θ then good else bad

/-- The successful successor, including the last model-dependent branch step. -/
def successfulNext {d : ℕ} (hd : 0 < d) (θ a : Bool) : ChainState d → ChainState d
  | Sum.inl i => if i = 0 then Sum.inr (a, ⟨0, hd⟩) else Sum.inl i
  | Sum.inr (i,j) => if hj : j.val+1 < d then Sum.inr (i, ⟨j.val+1, hj⟩) else endpoint θ i

/-- The source's time-homogeneous two-model transition kernel. -/
def chainKernel {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (θ : Bool) : Nested.Kernel (ChainState d) Bool := fun s a =>
  match s with
  | Sum.inl i => if i = 0 then twoPoint α hα hα1 (successfulNext hd θ a s) failure
      else Nested.pure s
  | Sum.inr _ => twoPoint α hα hα1 (successfulNext hd θ a s) failure

/-- Common known rewards: reward one at the initial state and zero elsewhere. -/
def chainReward {d : ℕ} (_h : ℕ) (s : ChainState d) (_a : Bool) : ℝ :=
  if s = start then 1 else 0

/-- The only cost is one at the public bad endpoint at the final stage. -/
def chainCost {d : ℕ} (H h : ℕ) (s : ChainState d) (_a : Bool) : ℝ :=
  if h+1 = H ∧ s = bad then 1 else 0

theorem chainCost_bounds {d : ℕ} (H h : ℕ) (s : ChainState d) (a : Bool) :
    chainCost H h s a ∈ Icc (0:ℝ) 1 := by
  simp only [chainCost]
  split_ifs <;> norm_num

theorem branch_actions_identical {d : ℕ} (hd : 0 < d) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (θ : Bool) (s : ChainState d)
    (hs : s ≠ start) (a a' : Bool) :
    chainKernel hd α hα hα1 θ s a = chainKernel hd α hα hα1 θ s a' := by
  rcases s with i | ⟨i,j⟩
  · have hi : i ≠ 0 := by simpa [start] using hs
    simp [chainKernel, hi]
  · simp [chainKernel, successfulNext]

private theorem pure_apply {S : Type*} [Fintype S] [DecidableEq S] (s t : S) :
    Nested.pure s t = if t = s then 1 else 0 := by
  simp [Nested.pure, stdSimplex.vertex, Pi.single_apply, eq_comm]

/-- The two kernels have identical probability for every non-endpoint next
state, even at the last branch depth.  This includes all failure observations. -/
theorem kernel_feedback_equal {d : ℕ} (hd : 0 < d) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (s t : ChainState d) (a : Bool)
    (htg : t ≠ good) (htb : t ≠ bad) :
    chainKernel hd α hα hα1 false s a t = chainKernel hd α hα hα1 true s a t := by
  rcases s with i | ⟨i,j⟩
  · by_cases hi : i = 0
    · simp [chainKernel, successfulNext, hi, twoPoint]
    · simp [chainKernel, hi]
  · by_cases hj : j.val+1 < d
    · simp [chainKernel, successfulNext, hj, twoPoint]
    · simp only [chainKernel, successfulNext, hj, ↓reduceDIte, twoPoint, Subtype.coe_mk]
      have he (θ : Bool) : Nested.pure (endpoint θ i) t = 0 := by
        unfold endpoint
        split_ifs <;> simp [pure_apply, htg, htb]
      change α*Nested.pure (endpoint false i) t + (1-α)*Nested.pure failure t =
        α*Nested.pure (endpoint true i) t + (1-α)*Nested.pure failure t
      rw [he, he]

/-- A complete trajectory records every physical state, action, and successor.
The likelihood equality below therefore retains the full public feedback. -/
abbrev Trace (d : ℕ) := List (ChainState d × Bool × ChainState d)

def traceLikelihood {d : ℕ} (q : Nested.Kernel (ChainState d) Bool)
    (π : Nested.Policy (ChainState d) Bool) : ℕ → Trace d → ℝ
  | _, [] => 1
  | h, (s,a,t)::xs => π h s a * q s a t * traceLikelihood q π (h+1) xs

/-- No endpoint trace has the same likelihood under both models for every
randomized physical-state Markov policy, including all intermediate actions. -/
theorem full_trace_likelihood_equal {d : ℕ} (hd : 0 < d) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (π : Nested.Policy (ChainState d) Bool)
    (xs : Trace d) (hx : ∀ e ∈ xs, e.2.2 ≠ good ∧ e.2.2 ≠ bad) (h : ℕ) :
    traceLikelihood (chainKernel hd α hα hα1 false) π h xs =
      traceLikelihood (chainKernel hd α hα hα1 true) π h xs := by
  induction xs generalizing h with
  | nil => rfl
  | cons e xs ih =>
    obtain ⟨s,a,t⟩ := e
    have ht := hx (s,a,t) List.mem_cons_self
    have hh : ∀ e ∈ xs, e.2.2 ≠ good ∧ e.2.2 ≠ bad := by
      intro e he
      exact hx e (List.mem_cons_of_mem _ he)
    simp only [traceLikelihood, kernel_feedback_equal hd α hα hα1 s t a ht.1 ht.2,
      ih hh]

/-- The finite-law objective of a Boolean loss depends only on its event mass. -/
theorem indicator_objective {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (f : Ω → Bool) (α z : ℝ) :
    objective α P (fun i => if f i then 1 else 0) z =
      Tightening.bernoulliObjective α 1 (expectation P (fun i => if f i then 1 else 0)) z := by
  have hi (i : Ω) : max ((if f i then (1:ℝ) else 0)-z) 0 =
      max (-z) 0 + (if f i then 1 else 0)*(max (1-z) 0-max (-z) 0) := by
    cases f i <;> simp <;> ring
  have hex : expectation P (fun i => max ((if f i then (1:ℝ) else 0)-z) 0) =
      max (-z) 0 + expectation P (fun i => if f i then 1 else 0) *
        (max (1-z) 0-max (-z) 0) := by
    unfold expectation
    simp only [hi, mul_add, ← mul_assoc, sum_add_distrib, ← sum_mul, law_sum, one_mul]
  unfold objective
  rw [hex]
  unfold Tightening.bernoulliObjective
  ring


/-- Bernoulli CVaR at event mass `α*x`, proved for an arbitrary finite underlying
sample space.  It applies to the joint action-transition law at stage one. -/
theorem indicator_cvar {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (f : Ω → Bool) {α B x : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hB : 0 ≤ B) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hm : expectation P (fun i => if f i then 1 else 0) = α*x) :
    compactCVaR α B P (fun i => if f i then 1 else 0) = x := by
  have hp0 : 0 ≤ α*x := mul_nonneg hα.le hx
  have hp1 : α*x ≤ 1 := by nlinarith
  have hdiv : (α*x)/α = x := by field_simp
  apply le_antisymm
  · apply (compactCVaR_le α B hB P _ (show (0:ℝ) ∈ Icc 0 B from ⟨le_rfl, hB⟩)).trans
    rw [indicator_objective, hm]
    simp [Tightening.bernoulliObjective, hdiv]
  · apply le_compactCVaR α B hB
    intro z _hz
    rw [indicator_objective, hm]
    have hl := Tightening.bernoulli_lower α 1 (α*x) z hα hα1 (by norm_num) hp0 hp1
    simpa [hdiv, min_eq_left hx1] using hl


/-- Expected values under an actual physical two-point transition law. -/
theorem expectation_twoPoint {S : Type*} [Fintype S] (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (u v : S) (X : S → ℝ) :
    expectation (twoPoint α hα hα1 u v) X = α*X u + (1-α)*X v := by
  classical
  change (∑ s, (α*Nested.pure u s+(1-α)*Nested.pure v s)*X s) = _
  simp only [add_mul, sum_add_distrib]
  simp [pure_apply, mul_assoc, mul_ite]

/-- A reusable threshold calculation for the initial mixed action and for every
rare branch step.  Action randomization remains inside the joint CVaR law. -/
theorem joint_twoPoint_objective {S A : Type*} [Fintype S] [Fintype A]
    (l : Law A) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (u : A → S) (v : S) (R : S → ℝ) (f : A → Bool)
    (hu : ∀ a, R (u a) = if f a then 1 else 0) (hv : R v = 0) (z : ℝ) :
    objective α (Nested.joint l (fun a => twoPoint α hα hα1 (u a) v)) (fun x => R x.2) z =
      Tightening.bernoulliObjective α 1
        (α*expectation l (fun a => if f a then 1 else 0)) z := by
  change objective α (Nested.joint l (fun a => twoPoint α hα hα1 (u a) v))
    (fun x => (fun (_a : A) (s : S) => R s) x.1 x.2) z = _
  rw [Nested.objective_joint α l (fun a => twoPoint α hα hα1 (u a) v)
    (fun (_a : A) (s : S) => R s) z]
  have hi (a : A) : max ((if f a then (1:ℝ) else 0)-z) 0 =
      max (-z) 0 + (if f a then 1 else 0)*(max (1-z) 0-max (-z) 0) := by
    cases f a <;> simp
  have hp (a : A) : objective α (twoPoint α hα hα1 (u a) v) R z =
      (z+α⁻¹*max (-z) 0) + (if f a then 1 else 0)*
        ((α⁻¹*α)*(max (1-z) 0-max (-z) 0)) := by
    simp only [objective, expectation_twoPoint, hu, hv, zero_sub, hi]
    ring
  calc
    _ = (z+α⁻¹*max (-z) 0) + expectation l (fun a => if f a then 1 else 0)*
        ((α⁻¹*α)*(max (1-z) 0-max (-z) 0)) := by
      simp only [hp, expectation, mul_add, ← mul_assoc, sum_add_distrib, ← sum_mul,
        law_sum, one_mul]
    _ = _ := by unfold Tightening.bernoulliObjective; ring

theorem compact_bernoulli_of_objective {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (X : Ω → ℝ) {α B x : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hB : 0 ≤ B) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (heq : ∀ z, objective α P X z = Tightening.bernoulliObjective α 1 (α*x) z) :
    compactCVaR α B P X = x := by
  have hp0 : 0 ≤ α*x := mul_nonneg hα.le hx
  have hp1 : α*x ≤ 1 := by nlinarith
  have hdiv : (α*x)/α = x := by field_simp
  apply le_antisymm
  · apply (compactCVaR_le α B hB P X (show (0:ℝ) ∈ Icc 0 B from ⟨le_rfl, hB⟩)).trans
    rw [heq]
    simp [Tightening.bernoulliObjective, hdiv]
  · apply le_compactCVaR α B hB
    intro z _hz
    rw [heq]
    have hl := Tightening.bernoulli_lower α 1 (α*x) z hα hα1 (by norm_num) hp0 hp1
    simpa [hdiv, min_eq_left hx1] using hl

theorem compactCVaR_const {Ω : Type*} [Fintype Ω] (P : Law Ω)
    {α B c : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 ≤ c) (hcB : c ≤ B) :
    compactCVaR α B P (fun _ => c) = c := by
  have hB : 0 ≤ B := hc.trans hcB
  apply le_antisymm
  · apply (compactCVaR_le α B hB P _ (show c ∈ Icc 0 B from ⟨hc, hcB⟩)).trans
    simp [objective]
  · apply le_compactCVaR α B hB
    intro z _hz
    simp only [objective, expectation_const]
    have hi : 1 ≤ α⁻¹ := (one_le_inv₀ hα).2 hα1
    by_cases hzc : z ≤ c
    · rw [max_eq_left (sub_nonneg.mpr hzc)]
      nlinarith
    · rw [max_eq_right (by linarith : c-z ≤ 0)]
      simp only [mul_zero, add_zero]
      linarith


theorem expectation_pure {S : Type*} [Fintype S] (s : S) (X : S → ℝ) :
    expectation (Nested.pure s) X = X s := by
  classical
  simp [expectation, pure_apply]

/-- The zero-cost absorbing failure and good states have zero nested risk. -/
theorem risk_absorbing_zero {S A : Type*} [Fintype S] [Fintype A]
    (α : ℝ) (hα : 0 ≤ α) (c : ℕ → S → A → ℝ) (π : Nested.Policy S A)
    (q : Nested.Kernel S A) (s : S)
    (hc : ∀ h a, c h s a = 0) (hq : ∀ a, q s a = Nested.pure s) (n h : ℕ) :
    Nested.risk α c π q n h s = 0 := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    rw [Nested.risk]
    apply le_antisymm
    · apply (compactCVaR_le α (n+1 : ℕ) (by positivity) _ _
        (show (0:ℝ) ∈ Set.Icc 0 ((n+1 : ℕ) : ℝ) from ⟨le_rfl, by positivity⟩)).trans
      rw [Nested.objective_joint α (π h s) (q s)
        (fun a t => c h s a + Nested.risk α c π q n (h+1) t) 0]
      have he (a : A) :
          objective α (q s a) (fun t => c h s a + Nested.risk α c π q n (h+1) t) 0 = 0 := by
        rw [hq a, hc]
        simp [objective, expectation_pure, ih]
      simp [he]
    · exact compactCVaR_nonneg α _ hα (by positivity) _ _

theorem chain_failure_risk {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool) (H n h : ℕ) :
    Nested.risk α (chainCost H) π (chainKernel hd α hα hα1 θ) n h failure = 0 := by
  apply risk_absorbing_zero α hα
  · intro h a; simp [chainCost, failure, bad]
  · intro a; simp [chainKernel, failure]

theorem chain_good_risk {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool) (H n h : ℕ) :
    Nested.risk α (chainCost H) π (chainKernel hd α hα hα1 θ) n h good = 0 := by
  apply risk_absorbing_zero α hα
  · intro h a; simp [chainCost, good, bad]
  · intro a; simp [chainKernel, good]

theorem chain_bad_terminal {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool) :
    Nested.risk α (chainCost (d+2)) π (chainKernel hd α hα.le hα1 θ) 1 (d+1) bad = 1 := by
  simp only [Nested.risk, chainCost, Nat.add_right_cancel_iff, and_self, ↓reduceIte, add_zero]
  apply compactCVaR_const _ hα hα1 (by norm_num) (by norm_num)


theorem successfulNext_not_start {d : ℕ} (hd : 0 < d) (θ a : Bool) (s : ChainState d) :
    successfulNext hd θ a s ≠ start ∨ s = start := by
  rcases s with i | ⟨i,j⟩
  · by_cases hi : i = 0
    · right; simp [start, hi]
    · left; simpa [successfulNext, hi, start] using hi
  · left
    simp only [successfulNext]
    split_ifs <;> simp [start, endpoint, good, bad, ite_eq_iff]

theorem chainKernel_no_return {d : ℕ} (hd : 0 < d) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (θ a : Bool) (s : ChainState d) :
    chainKernel hd α hα hα1 θ s a start = 0 := by
  rcases s with i | ⟨i,j⟩
  · by_cases hi : i = 0
    · simp [chainKernel, successfulNext, hi, twoPoint_apply, pure_apply, start, failure]
    · simp [chainKernel, hi, pure_apply, start, Ne.symm hi]
  · have hs : successfulNext hd θ a (Sum.inr (i,j)) ≠ start :=
      (successfulNext_not_start hd θ a _).resolve_right (by simp [start])
    change α*Nested.pure (successfulNext hd θ a (Sum.inr (i,j))) start +
      (1-α)*Nested.pure failure start = 0
    rw [pure_apply, if_neg (Ne.symm hs)]
    simp [pure_apply, start, failure]

/-- Every randomized Markov policy earns exactly one from the source initial
state, so reward regret is identically zero, with no optimality assumption. -/
theorem source_reward_one {d : ℕ} (hd : 0 < d) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (θ : Bool) (π : Nested.Policy (ChainState d) Bool)
    (n h : ℕ) (s : ChainState d) :
    Nested.reward chainReward π (chainKernel hd α hα hα1 θ) (n+1) h s =
      if s = start then 1 else 0 := by
  classical
  induction n generalizing h s with
  | zero =>
    rw [Nested.reward]
    simp only [Nested.reward, mul_zero, sum_const_zero, add_zero, chainReward]
    rw [← sum_mul, law_sum, one_mul]
  | succ n ih =>
    rw [Nested.reward]
    simp only [ih, chainReward]
    have he (a : Bool) :
        (∑ t, chainKernel hd α hα hα1 θ s a t * (if t = start then (1:ℝ) else 0)) = 0 := by
      simp [chainKernel_no_return]
    simp only [he, add_zero]
    rw [← sum_mul, law_sum, one_mul]


/-- One exact nested-risk backup for a physical rare transition. -/
theorem rare_step_risk {S A : Type*} [Fintype S] [Fintype A]
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (c : ℕ → S → A → ℝ)
    (π : Nested.Policy S A) (q : Nested.Kernel S A) (n h : ℕ) (s v : S)
    (u : A → S) (f : A → Bool)
    (hc : ∀ a, c h s a = 0)
    (hq : ∀ a, q s a = twoPoint α hα.le hα1 (u a) v)
    (hu : ∀ a, Nested.risk α c π q n (h+1) (u a) = if f a then 1 else 0)
    (hv : Nested.risk α c π q n (h+1) v = 0) :
    Nested.risk α c π q (n+1) h s = expectation (π h s) (fun a => if f a then 1 else 0) := by
  let x := expectation (π h s) (fun a => if f a then 1 else 0)
  have hx : 0 ≤ x := sum_nonneg fun a _ => mul_nonneg ((π h s).property.1 a) (by cases hf : f a <;> simp [hf])
  have hx1 : x ≤ 1 := by
    calc
      x ≤ expectation (π h s) (fun _ => 1) := expectation_mono _ (fun a => by cases hf : f a <;> simp [hf])
      _ = 1 := expectation_const _ _
  rw [Nested.risk]
  have hqfun : q s = fun a => twoPoint α hα.le hα1 (u a) v := funext hq
  rw [hqfun]
  have hX : (fun y : A × S => c h s y.1 + Nested.risk α c π q n (h+1) y.2) =
      (fun y : A × S => Nested.risk α c π q n (h+1) y.2) := by
    funext y
    rw [hc, zero_add]
  rw [hX]
  apply compact_bernoulli_of_objective _ _ hα hα1 (by positivity) hx hx1
  intro z
  exact joint_twoPoint_objective (π h s) α hα.le hα1 u v
    (Nested.risk α c π q n (h+1)) f hu hv z

def badFlag (θ a : Bool) : Bool := decide (a ≠ θ)

theorem badFlag_value (θ a : Bool) : (if badFlag θ a then (1:ℝ) else 0) =
    if a = θ then 0 else 1 := by
  by_cases h : a = θ <;> simp [badFlag, h]

/-- Backward induction through every branch-depth state of the actual kernel. -/
theorem source_depth_risk {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool) (a : Bool)
    (k : ℕ) (j : Fin d) (hjk : j.val+k+1 = d) :
    Nested.risk α (chainCost (d+2)) π (chainKernel hd α hα.le hα1 θ)
      (k+2) (j.val+1) (Sum.inr (a,j)) = if a = θ then 0 else 1 := by
  induction k generalizing j with
  | zero =>
    have hj : ¬ j.val+1 < d := by omega
    have ht : j.val+1+1 = d+1 := by omega
    have hstep := rare_step_risk α hα hα1 (chainCost (d+2)) π
      (chainKernel hd α hα.le hα1 θ) 1 (j.val+1) (Sum.inr (a,j)) failure
      (fun _ => endpoint θ a) (fun _ => badFlag θ a)
      (by intro b; simp [chainCost, bad])
      (by intro b; simp [chainKernel, successfulNext, hj])
      (by
        intro b
        rw [ht, badFlag_value]
        by_cases ha : a = θ
        · simp [endpoint, ha, chain_good_risk]
        · simp [endpoint, ha, chain_bad_terminal hd hα hα1])
      (chain_failure_risk hd hα.le hα1 θ π _ _ _)
    simpa only [expectation_const, badFlag_value] using hstep
  | succ k ih =>
    have hj : j.val+1 < d := by omega
    let j' : Fin d := ⟨j.val+1, hj⟩
    have hk' : j'.val+k+1 = d := by dsimp [j']; omega
    have hstep := rare_step_risk α hα hα1 (chainCost (d+2)) π
      (chainKernel hd α hα.le hα1 θ) (k+2) (j.val+1) (Sum.inr (a,j)) failure
      (fun _ => Sum.inr (a,j')) (fun _ => badFlag θ a)
      (by intro b; simp [chainCost, bad])
      (by intro b; simp [chainKernel, successfulNext, hj, j'])
      (by
        intro b
        rw [badFlag_value]
        simpa only [j', Nat.add_assoc] using ih j' hk')
      (chain_failure_risk hd hα.le hα1 θ π _ _ _)
    simpa only [expectation_const, badFlag_value, Nat.succ_add] using hstep

/-- Equation (F.1) for every source randomized physical-state Markov policy. -/
theorem source_initial_risk {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool) :
    Nested.risk α (chainCost (d+2)) π (chainKernel hd α hα.le hα1 θ)
      (d+2) 0 start = π 0 start (!θ) := by
  have hu (a : Bool) :
      Nested.risk α (chainCost (d+2)) π (chainKernel hd α hα.le hα1 θ)
        (d+1) 1 (Sum.inr (a, ⟨0,hd⟩)) = if badFlag θ a then 1 else 0 := by
    rw [badFlag_value]
    have hh := source_depth_risk hd hα hα1 θ π a (d-1) ⟨0,hd⟩ (by simp only [Fin.val_mk]; omega)
    have hn : d-1+2 = d+1 := by omega
    simpa only [hn, Fin.val_zero, Nat.zero_add] using hh
  have hh := rare_step_risk α hα hα1 (chainCost (d+2)) π
    (chainKernel hd α hα.le hα1 θ) (d+1) 0 start failure
    (fun a => Sum.inr (a, ⟨0,hd⟩)) (badFlag θ)
    (by intro a; simp [chainCost, start, bad])
    (by intro a; simp [chainKernel, successfulNext, start])
    hu (chain_failure_risk hd hα.le hα1 θ π _ _ _)
  have he : expectation (π 0 start) (fun a => if badFlag θ a then (1:ℝ) else 0) = π 0 start (!θ) := by
    cases θ <;> simp [expectation, badFlag]
  simpa only [he] using hh


/-- Exact expectation of a complete physical trajectory.  No transition or
intermediate action is suppressed from the feedback. -/
def run {S A : Type*} [Fintype S] [Fintype A] (q : Nested.Kernel S A)
    (π : Nested.Policy S A) (V : List (S × A × S) → ℝ) :
    ℕ → ℕ → S → List (S × A × S) → ℝ
  | 0, _, _, tr => V tr
  | n+1, h, s, tr => expectation (π h s) (fun a => expectation (q s a)
      (fun t => run q π V n (h+1) t ((s,a,t)::tr)))

theorem expectation_average {Ω : Type*} [Fintype Ω] (P : Law Ω) (f g : Ω → ℝ) :
    (expectation P f + expectation P g)/2 = expectation P (fun i => (f i+g i)/2) := by
  simp only [expectation, div_eq_mul_inv, mul_add, add_mul, ← mul_assoc,
    sum_add_distrib, ← sum_mul]

theorem run_floor {S A : Type*} [Fintype S] [Fintype A] (q : Nested.Kernel S A)
    (π : Nested.Policy S A) (V : List (S × A × S) → ℝ) (b : ℝ)
    (hV : ∀ tr, b ≤ V tr) (n h : ℕ) (s : S) (tr : List (S × A × S)) :
    b ≤ run q π V n h s tr := by
  induction n generalizing h s tr with
  | zero => exact hV tr
  | succ n ih =>
    rw [run]
    calc
      b = expectation (π h s) (fun _ => b) := (expectation_const _ _).symm
      _ ≤ _ := expectation_mono _ (fun a => by
        calc
          b = expectation (q s a) (fun _ => b) := (expectation_const _ _).symm
          _ ≤ _ := expectation_mono _ (fun t => ih _ _ _))

/-- Full feedback at the absorbing failure state remains uninformative, even
though all randomized intermediate actions are retained in the trace. -/
theorem run_pair_absorbing {S A : Type*} [Fintype S] [Fintype A]
    (q0 q1 : Nested.Kernel S A) (π : Nested.Policy S A)
    (V0 V1 : List (S × A × S) → ℝ) (s : S)
    (hq0 : ∀ a, q0 s a = Nested.pure s) (hq1 : ∀ a, q1 s a = Nested.pure s)
    (B : ℝ) (hV : ∀ tr, B ≤ (V0 tr+V1 tr)/2)
    (n h : ℕ) (tr : List (S × A × S)) :
    B ≤ (run q0 π V0 n h s tr + run q1 π V1 n h s tr)/2 := by
  induction n generalizing h tr with
  | zero => exact hV tr
  | succ n ih =>
    simp only [run, hq0, hq1, expectation_pure]
    rw [expectation_average]
    calc
      B = expectation (π h s) (fun _ => B) := (expectation_const _ _).symm
      _ ≤ _ := expectation_mono _ (fun a => ih (h+1) ((s,a,s)::tr))

/-- A single physical rare transition propagates two continuation bounds.
The successor can depend on the latent model, while the failure state cannot. -/
theorem run_pair_twoPoint {S A : Type*} [Fintype S] [Fintype A]
    (q : Bool → Nested.Kernel S A) (π : Nested.Policy S A)
    (V : Bool → List (S × A × S) → ℝ) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (n h : ℕ) (s v : S)
    (u : Bool → A → S) (tr : List (S × A × S)) (B C : ℝ)
    (hq : ∀ θ a, q θ s a = twoPoint α hα hα1 (u θ a) v)
    (hu : ∀ a, C ≤
      (run (q false) π (V false) n (h+1) (u false a) ((s,a,u false a)::tr) +
       run (q true) π (V true) n (h+1) (u true a) ((s,a,u true a)::tr))/2)
    (hv : ∀ a, B ≤
      (run (q false) π (V false) n (h+1) v ((s,a,v)::tr) +
       run (q true) π (V true) n (h+1) v ((s,a,v)::tr))/2) :
    α*C+(1-α)*B ≤
      (run (q false) π (V false) (n+1) h s tr + run (q true) π (V true) (n+1) h s tr)/2 := by
  simp only [run, hq, expectation_twoPoint]
  rw [expectation_average]
  calc
    α*C+(1-α)*B = expectation (π h s) (fun _ => α*C+(1-α)*B) := (expectation_const _ _).symm
    _ ≤ _ := expectation_mono _ (fun a => by
      have hh := mul_le_mul_of_nonneg_left (hu a) hα
      have hf := mul_le_mul_of_nonneg_left (hv a) (show 0 ≤ 1-α by linarith)
      linarith)

/-- Continuation bound through all remaining rare transitions, computed on full
physical traces.  The terminal stage's actions are still simulated. -/
theorem run_depth_lower {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (π : Nested.Policy (ChainState d) Bool) (V : Bool → Trace d → ℝ)
    (B b : ℝ) (hb : ∀ θ tr, b ≤ V θ tr)
    (hB : ∀ tr, B ≤ (V false tr+V true tr)/2)
    (a : Bool) (k : ℕ) (j : Fin d) (hjk : j.val+k+1=d) (tr : Trace d) :
    (1-α^(k+1))*B+α^(k+1)*b ≤
      (run (chainKernel hd α hα hα1 false) π (V false) (k+2) (j.val+1) (Sum.inr (a,j)) tr +
       run (chainKernel hd α hα hα1 true) π (V true) (k+2) (j.val+1) (Sum.inr (a,j)) tr)/2 := by
  induction k generalizing j tr with
  | zero =>
    have hj : ¬ j.val+1<d := by omega
    have hh := run_pair_twoPoint (fun θ => chainKernel hd α hα hα1 θ) π V hα hα1
      1 (j.val+1) (Sum.inr (a,j)) failure (fun θ _ => endpoint θ a) tr B b
      (by intro θ c; simp [chainKernel, successfulNext, hj])
      (by
        intro c
        have h0 := run_floor (chainKernel hd α hα hα1 false) π (V false) b (hb false)
          1 (j.val+1+1) (endpoint false a) ((Sum.inr (a,j),c,endpoint false a)::tr)
        have h1 := run_floor (chainKernel hd α hα hα1 true) π (V true) b (hb true)
          1 (j.val+1+1) (endpoint true a) ((Sum.inr (a,j),c,endpoint true a)::tr)
        linarith)
      (by
        intro c
        apply run_pair_absorbing _ _ π (V false) (V true) failure
        · intro c; simp [chainKernel, failure]
        · intro c; simp [chainKernel, failure]
        · exact hB)
    simpa only [Nat.zero_add, pow_one, add_comm] using hh
  | succ k ih =>
    have hj : j.val+1<d := by omega
    let j' : Fin d := ⟨j.val+1,hj⟩
    have hk' : j'.val+k+1=d := by dsimp [j']; omega
    have hh := run_pair_twoPoint (fun θ => chainKernel hd α hα hα1 θ) π V hα hα1
      (k+2) (j.val+1) (Sum.inr (a,j)) failure (fun _ _ => Sum.inr (a,j')) tr B
      ((1-α^(k+1))*B+α^(k+1)*b)
      (by intro θ c; simp [chainKernel, successfulNext, hj, j'])
      (by intro c; simpa only [j', Nat.add_assoc] using ih j' hk' ((Sum.inr (a,j),c,Sum.inr (a,j'))::tr))
      (by
        intro c
        apply run_pair_absorbing _ _ π (V false) (V true) failure
        · intro c; simp [chainKernel, failure]
        · intro c; simp [chainKernel, failure]
        · exact hB)
    have he : (1-α^(k+1+1))*B+α^(k+1+1)*b =
        α*((1-α^(k+1))*B+α^(k+1)*b)+(1-α)*B := by rw [pow_succ]; ring
    simpa only [he, Nat.succ_add] using hh

/-- The exact common hazard `α^(H-1)` is derived from the original kernel,
without a compressed-experiment equivalence hypothesis. -/
theorem run_initial_lower {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (π : Nested.Policy (ChainState d) Bool) (V : Bool → Trace d → ℝ)
    (B b : ℝ) (hb : ∀ θ tr, b ≤ V θ tr)
    (hB : ∀ tr, B ≤ (V false tr+V true tr)/2) :
    (1-α^(d+1))*B+α^(d+1)*b ≤
      (run (chainKernel hd α hα hα1 false) π (V false) (d+2) 0 start [] +
       run (chainKernel hd α hα hα1 true) π (V true) (d+2) 0 start [])/2 := by
  have hh := run_pair_twoPoint (fun θ => chainKernel hd α hα hα1 θ) π V hα hα1
    (d+1) 0 start failure (fun _ a => Sum.inr (a,⟨0,hd⟩)) [] B ((1-α^d)*B+α^d*b)
    (by intro θ a; simp [chainKernel, successfulNext, start])
    (by
      intro a
      have hh := run_depth_lower hd hα hα1 π V B b hb hB a (d-1) ⟨0,hd⟩
        (by simp only; omega) [(start,a,Sum.inr (a,⟨0,hd⟩))]
      have hn : d-1+1=d := by omega
      have hn' : d-1+2=d+1 := by omega
      simpa only [hn, hn', Fin.val_zero, Nat.zero_add] using hh)
    (by
      intro a
      apply run_pair_absorbing _ _ π (V false) (V true) failure
      · intro a; simp [chainKernel, failure]
      · intro a; simp [chainKernel, failure]
      · exact hB)
  have he : (1-α^(d+1))*B+α^(d+1)*b = α*((1-α^d)*B+α^d*b)+(1-α)*B := by
    rw [pow_succ]; ring
  simpa only [he] using hh


/-- A learner observes the entire list of past complete physical trajectories.
Its chosen object is the source randomized Markov policy, not merely the first
branch probability.  A private random tape will be added as an outer argument. -/
abbrev PhysicalController (d : ℕ) := List (Trace d) → Nested.Policy (ChainState d) Bool

def physicalDebt {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (σ : PhysicalController d) (θ : Bool) (hist : List (Trace d)) : ℕ → ℝ
  | 0 => 0
  | k+1 =>
      Nested.risk α (chainCost (d+2)) (σ hist) (chainKernel hd α hα hα1 θ) (d+2) 0 start - 1/4 +
      run (chainKernel hd α hα hα1 θ) (σ hist)
        (fun tr => physicalDebt hd α hα hα1 σ θ (tr::hist) k) (d+2) 0 start []

def physicalBayesDebt {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (σ : PhysicalController d) (hist : List (Trace d)) (k : ℕ) : ℝ :=
  (physicalDebt hd α hα hα1 σ false hist k + physicalDebt hd α hα hα1 σ true hist k)/2

theorem physicalDebt_floor {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (σ : PhysicalController d) (θ : Bool) (hist : List (Trace d)) (k : ℕ) :
    -(k : ℝ)/4 ≤ physicalDebt hd α hα.le hα1 σ θ hist k := by
  induction k generalizing hist with
  | zero => simp [physicalDebt]
  | succ k ih =>
    have hh := run_floor (chainKernel hd α hα.le hα1 θ) (σ hist)
      (fun tr => physicalDebt hd α hα.le hα1 σ θ (tr::hist) k) (-(k : ℝ)/4)
      (fun tr => ih (tr::hist)) (d+2) 0 start []
    have hr : 0 ≤ (σ hist) 0 start (!θ) := ((σ hist) 0 start).property.1 _
    simp only [physicalDebt, Nat.cast_add, Nat.cast_one]
    rw [source_initial_risk hd hα hα1 θ (σ hist)]
    linarith

/-- Universal lower bound for the original physical feedback process.  There is
no fixed-law compression, posterior hypothesis, or Bayes-optimality premise. -/
theorem physical_learner_lower {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (σ : PhysicalController d) (hist : List (Trace d)) (k : ℕ) :
    bound (α^(d+1)) k ≤ physicalBayesDebt hd α hα.le hα1 σ hist k := by
  induction k generalizing hist with
  | zero => simp [physicalBayesDebt, physicalDebt, bound]
  | succ k ih =>
    let V : Bool → Trace d → ℝ := fun θ tr => physicalDebt hd α hα.le hα1 σ θ (tr::hist) k
    have hh := run_initial_lower hd hα.le hα1 (σ hist) V (bound (α^(d+1)) k) (-(k : ℝ)/4)
      (fun θ tr => physicalDebt_floor hd hα hα1 σ θ (tr::hist) k) (fun tr => ih (tr::hist))
    have ht := law_sum ((σ hist) 0 start)
    simp only [Fintype.sum_bool] at ht
    rw [bound_succ]
    simp only [physicalBayesDebt, physicalDebt]
    rw [source_initial_risk hd hα hα1 false (σ hist), source_initial_risk hd hα hα1 true (σ hist)]
    simp only [Bool.not_false, Bool.not_true]
    dsimp [V] at hh
    linarith

theorem physical_learner_closed {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (σ : PhysicalController d) (k : ℕ) :
    (1-(1-α^(d+1))^k)/(2*α^(d+1))-(k : ℝ)/4 ≤
      physicalBayesDebt hd α hα.le hα1 σ [] k := by
  rw [← bound_closed (pow_pos hα (d+1))]
  exact physical_learner_lower hd hα hα1 σ [] k

/-- Independent private randomness is an arbitrary probability space of random
tapes.  The same tape law is used for both models, and the controller has no
latent-model input.  Integrability is the well-formedness condition for the
source's expectation. -/
def seedBayesDebt {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (σ : Ω → PhysicalController d) (k : ℕ) : ℝ :=
  ∫ ω, physicalBayesDebt hd α hα hα1 (σ ω) [] k ∂μ

/-- The lower bound includes arbitrary independent private random tapes. -/
theorem private_seed_learner_lower {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (σ : Ω → PhysicalController d) (k : ℕ)
    (hσ : MeasureTheory.Integrable (fun ω => physicalBayesDebt hd α hα.le hα1 (σ ω) [] k) μ) :
    bound (α^(d+1)) k ≤ seedBayesDebt μ hd α hα.le hα1 σ k := by
  unfold seedBayesDebt
  calc
    bound (α^(d+1)) k = ∫ _ω : Ω, bound (α^(d+1)) k ∂μ := by simp
    _ ≤ _ := MeasureTheory.integral_mono (MeasureTheory.integrable_const _) hσ
      (fun ω => physical_learner_lower hd hα hα1 (σ ω) [] k)

theorem private_seed_tailored {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα2 : α ≤ 1/2)
    (σ : Ω → PhysicalController d)
    (hσ : MeasureTheory.Integrable
      (fun ω => physicalBayesDebt hd α hα.le (by linarith) (σ ω) [] (K0 (α^(d+1)))) μ) :
    1/(32*α^(d+1)) ≤ seedBayesDebt μ hd α hα.le (by linarith) σ (K0 (α^(d+1))) := by
  have hβ : 0 < α^(d+1) := pow_pos hα _
  have hβ4 : α^(d+1) ≤ 1/4 := by
    have hn : 2 ≤ d+1 := by omega
    have hp := pow_le_pow_of_le_one hα.le (show α ≤ 1 by linarith) hn
    have hs := pow_le_pow_left₀ hα.le hα2 2
    norm_num at hs
    exact hp.trans hs
  exact (tailored_bound hβ hβ4).trans (private_seed_learner_lower μ hd hα (by linarith) σ _ hσ)


/-- A model-dependent feasible comparator has zero source nested risk and
reward one; no common baseline is inserted into the no-fallback family. -/
theorem source_good_comparator {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool) : ∃ π : Nested.Policy (ChainState d) Bool,
      Nested.risk α (chainCost (d+2)) π (chainKernel hd α hα.le hα1 θ) (d+2) 0 start = 0 ∧
      Nested.reward chainReward π (chainKernel hd α hα.le hα1 θ) (d+2) 0 start = 1 := by
  refine ⟨fun _ _ => Nested.pure θ, ?_, ?_⟩
  · rw [source_initial_risk hd hα hα1 θ]
    cases θ <;> simp [pure_apply]
  · simpa only [if_pos rfl] using source_reward_one hd α hα.le hα1 θ (fun _ _ => Nested.pure θ) (d+1) 0 start

theorem source_minimum_risk_zero {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool) : Nested.minimumRisk α (chainCost (d+2)) (d+2) 0 start
      (chainKernel hd α hα.le hα1 θ) = 0 := by
  obtain ⟨π, hπ, _⟩ := source_good_comparator hd hα hα1 θ
  let E := (fun π : Nested.Policy (ChainState d) Bool =>
    Nested.risk α (chainCost (d+2)) π (chainKernel hd α hα.le hα1 θ) (d+2) 0 start) '' Set.univ
  have hn : E.Nonempty := ⟨0, π, Set.mem_univ π, hπ⟩
  have hlo : ∀ x ∈ E, 0 ≤ x := by
    rintro x ⟨π', _, rfl⟩
    change 0 ≤ Nested.risk α (chainCost (d+2)) π' (chainKernel hd α hα.le hα1 θ) (d+2) 0 start
    rw [source_initial_risk hd hα hα1 θ π']
    exact (π' 0 start).property.1 _
  apply le_antisymm
  · exact csInf_le ⟨0, hlo⟩ ⟨π, Set.mem_univ π, hπ⟩
  · exact le_csInf hn hlo

def physicalRewardShortfall {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (σ : PhysicalController d) (θ : Bool) (hist : List (Trace d)) : ℕ → ℝ
  | 0 => 0
  | k+1 => 1-Nested.reward chainReward (σ hist) (chainKernel hd α hα hα1 θ) (d+2) 0 start +
      run (chainKernel hd α hα hα1 θ) (σ hist)
        (fun tr => physicalRewardShortfall hd α hα hα1 σ θ (tr::hist) k) (d+2) 0 start []

theorem run_const {S A : Type*} [Fintype S] [Fintype A] (q : Nested.Kernel S A)
    (π : Nested.Policy S A) (c : ℝ) (n h : ℕ) (s : S) (tr : List (S × A × S)) :
    run q π (fun _ => c) n h s tr = c := by
  induction n generalizing h s tr with
  | zero => rfl
  | succ n ih => simp only [run, ih, expectation_const]

/-- The zero reward-regret assertion includes the complete adaptive learner. -/
theorem physical_reward_shortfall_zero {d : ℕ} (hd : 0 < d) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (σ : PhysicalController d) (θ : Bool)
    (hist : List (Trace d)) (k : ℕ) :
    physicalRewardShortfall hd α hα hα1 σ θ hist k = 0 := by
  induction k generalizing hist with
  | zero => rfl
  | succ k ih =>
    rw [physicalRewardShortfall, source_reward_one hd α hα hα1 θ (σ hist) (d+1) 0 start]
    simp only [ite_true, ih, run_const, sub_self, add_zero]


/-- The endpoint and branch-depth state give the revealed model index. -/
def transitionSignal {d : ℕ} (e : ChainState d × Bool × ChainState d) : Option Bool :=
  match e.1 with
  | Sum.inl _ => none
  | Sum.inr (a,_) => if e.2.2 = good then some a else if e.2.2 = bad then some (!a) else none

def updateKnowledge {d : ℕ} (old : Option Bool) : Trace d → Option Bool
  | [] => old
  | e::tr => (transitionSignal e).orElse (fun _ => updateKnowledge old tr)

def historyKnowledge {d : ℕ} : List (Trace d) → Option Bool
  | [] => none
  | tr::hist => updateKnowledge (historyKnowledge hist) tr

def optimalPhysical {d : ℕ} : PhysicalController d := fun hist _h _s =>
  Nested.pure ((historyKnowledge hist).getD false)

theorem twoPoint_support {S : Type*} [Fintype S] (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (u v t : S) (h : twoPoint α hα hα1 u v t ≠ 0) : t=u ∨ t=v := by
  classical
  by_contra hn
  have hu : t ≠ u := fun hh => hn (Or.inl hh)
  have hv : t ≠ v := fun hh => hn (Or.inr hh)
  exact h (by simp [twoPoint_apply, pure_apply, hu, hv])

/-- The actual physical kernel cannot generate an incorrect model signal. -/
theorem transitionSignal_correct {d : ℕ} (hd : 0 < d) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (θ a : Bool) (s t : ChainState d)
    (hq : chainKernel hd α hα hα1 θ s a t ≠ 0) :
    transitionSignal (s,a,t) = none ∨ transitionSignal (s,a,t) = some θ := by
  rcases s with i | ⟨i,j⟩
  · left; rfl
  · have hsup : t = successfulNext hd θ a (Sum.inr (i,j)) ∨ t = failure :=
      twoPoint_support α hα hα1 _ _ t hq
    rcases hsup with rfl | rfl
    · by_cases hj : j.val+1<d
      · left; simp [transitionSignal, successfulNext, hj, good, bad]
      · right
        cases θ <;> cases i <;> simp [transitionSignal, successfulNext, hj, endpoint, good, bad]
    · left; simp [transitionSignal, failure, good, bad]

theorem updateKnowledge_preserved {d : ℕ} (old : Option Bool) (tr : Trace d)
    (e : ChainState d × Bool × ChainState d) (θ : Bool)
    (hk : updateKnowledge old tr = some θ)
    (he : transitionSignal e = none ∨ transitionSignal e = some θ) :
    updateKnowledge old (e::tr) = some θ := by
  rcases he with he | he <;> simp [updateKnowledge, he, hk]

theorem expectation_eq_of_support {Ω : Type*} [Fintype Ω] (P : Law Ω) (f : Ω → ℝ) (c : ℝ)
    (h : ∀ i, P i ≠ 0 → f i = c) : expectation P f = c := by
  calc
    expectation P f = expectation P (fun _ => c) := by
      apply sum_congr rfl
      intro i _
      by_cases hi : P i = 0
      · simp [hi]
      · rw [h i hi]
    _ = c := expectation_const _ _

/-- A pathwise invariant is sufficient for exact finite trajectory expectation;
zero-probability transitions are discarded algebraically. -/
theorem run_invariant_const {S A : Type*} [Fintype S] [Fintype A]
    (q : Nested.Kernel S A) (π : Nested.Policy S A) (V : List (S × A × S) → ℝ)
    (I : List (S × A × S) → Prop) (c : ℝ)
    (hV : ∀ tr, I tr → V tr = c)
    (hI : ∀ s a t tr, I tr → q s a t ≠ 0 → I ((s,a,t)::tr))
    (n h : ℕ) (s : S) (tr : List (S × A × S)) (htr : I tr) :
    run q π V n h s tr = c := by
  induction n generalizing h s tr with
  | zero => exact hV tr htr
  | succ n ih =>
    rw [run]
    apply expectation_eq_of_support
    intro a _ha
    apply expectation_eq_of_support
    intro t ht
    exact ih (h+1) t ((s,a,t)::tr) (hI s a t tr htr ht)

theorem optimalPhysical_known {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool) (hist : List (Trace d)) (hk : historyKnowledge hist = some θ) (k : ℕ) :
    physicalDebt hd α hα.le hα1 optimalPhysical θ hist k = -(k : ℝ)/4 := by
  induction k generalizing hist with
  | zero => simp [physicalDebt]
  | succ k ih =>
    rw [physicalDebt, source_initial_risk hd hα hα1 θ]
    have hc : run (chainKernel hd α hα.le hα1 θ) (optimalPhysical hist)
        (fun tr => physicalDebt hd α hα.le hα1 optimalPhysical θ (tr::hist) k)
        (d+2) 0 start [] = -(k : ℝ)/4 := by
      apply run_invariant_const _ _ _ (fun tr => updateKnowledge (historyKnowledge hist) tr = some θ)
      · intro tr htr
        exact ih (tr::hist) htr
      · intro s a t tr htr ht
        apply updateKnowledge_preserved _ _ _ θ htr
        exact transitionSignal_correct hd α hα.le hα1 θ a s t ht
      · exact hk
    rw [hc]
    simp [optimalPhysical, hk, pure_apply]
    ring


theorem run_known_const {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool) (V : Trace d → ℝ)
    (old : Option Bool) (b : ℝ) (hV : ∀ tr, updateKnowledge old tr = some θ → V tr = b)
    (n h : ℕ) (s : ChainState d) (tr : Trace d) (htr : updateKnowledge old tr = some θ) :
    run (chainKernel hd α hα hα1 θ) π V n h s tr = b := by
  apply run_invariant_const _ _ _ (fun tr => updateKnowledge old tr = some θ) b hV
  · intro s a t tr htr ht
    exact updateKnowledge_preserved old tr _ θ htr (transitionSignal_correct hd α hα hα1 θ a s t ht)
  · exact htr

theorem run_failure_unknown {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (π : Nested.Policy (ChainState d) Bool) (V : Bool → Trace d → ℝ)
    (old : Option Bool) (B : ℝ)
    (hV : ∀ tr, updateKnowledge old tr = none → (V false tr+V true tr)/2 = B)
    (n h : ℕ) (tr : Trace d) (htr : updateKnowledge old tr = none) :
    (run (chainKernel hd α hα hα1 false) π (V false) n h failure tr +
     run (chainKernel hd α hα hα1 true) π (V true) n h failure tr)/2 = B := by
  induction n generalizing h tr with
  | zero => exact hV tr htr
  | succ n ih =>
    have hq (θ a : Bool) : chainKernel hd α hα hα1 θ failure a = Nested.pure failure := by
      simp [chainKernel, failure]
    simp only [run, hq, expectation_pure]
    rw [expectation_average]
    have he (a : Bool) :
        (run (chainKernel hd α hα hα1 false) π (V false) n (h+1) failure ((failure,a,failure)::tr) +
         run (chainKernel hd α hα hα1 true) π (V true) n (h+1) failure ((failure,a,failure)::tr))/2 = B :=
      ih (h+1) _ (by simpa [updateKnowledge, transitionSignal, failure] using htr)
    simp only [he, expectation_const]

theorem run_pair_twoPoint_eq {S A : Type*} [Fintype S] [Fintype A]
    (q : Bool → Nested.Kernel S A) (π : Nested.Policy S A)
    (V : Bool → List (S × A × S) → ℝ) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (n h : ℕ) (s v : S)
    (u : Bool → A → S) (tr : List (S × A × S)) (B C : ℝ)
    (hq : ∀ θ a, q θ s a = twoPoint α hα hα1 (u θ a) v)
    (hu : ∀ a,
      (run (q false) π (V false) n (h+1) (u false a) ((s,a,u false a)::tr) +
       run (q true) π (V true) n (h+1) (u true a) ((s,a,u true a)::tr))/2 = C)
    (hv : ∀ a,
      (run (q false) π (V false) n (h+1) v ((s,a,v)::tr) +
       run (q true) π (V true) n (h+1) v ((s,a,v)::tr))/2 = B) :
    (run (q false) π (V false) (n+1) h s tr + run (q true) π (V true) (n+1) h s tr)/2 = α*C+(1-α)*B := by
  simp only [run, hq, expectation_twoPoint]
  rw [expectation_average]
  calc
    _ = expectation (π h s) (fun _ => α*C+(1-α)*B) := by
      apply sum_congr rfl
      intro a _
      congr 1
      have hu' := congrArg (fun z : ℝ => α*z) (hu a)
      have hv' := congrArg (fun z : ℝ => (1-α)*z) (hv a)
      dsimp only at *
      linarith only [hu', hv']
    _ = _ := expectation_const _ _

theorem endpoint_transition_signal {d : ℕ} (θ a c : Bool) (j : Fin d) :
    transitionSignal (Sum.inr (a,j),c,endpoint θ a) = some θ := by
  cases θ <;> cases a <;> simp [transitionSignal, endpoint, good, bad]

theorem run_depth_equal {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (π : Nested.Policy (ChainState d) Bool) (V : Bool → Trace d → ℝ)
    (old : Option Bool) (B b : ℝ)
    (hU : ∀ tr, updateKnowledge old tr = none → (V false tr+V true tr)/2 = B)
    (hK : ∀ θ tr, updateKnowledge old tr = some θ → V θ tr = b)
    (a : Bool) (k : ℕ) (j : Fin d) (hjk : j.val+k+1=d) (tr : Trace d)
    (htr : updateKnowledge old tr = none) :
    (run (chainKernel hd α hα hα1 false) π (V false) (k+2) (j.val+1) (Sum.inr (a,j)) tr +
     run (chainKernel hd α hα hα1 true) π (V true) (k+2) (j.val+1) (Sum.inr (a,j)) tr)/2 =
      (1-α^(k+1))*B+α^(k+1)*b := by
  induction k generalizing j tr with
  | zero =>
    have hj : ¬ j.val+1<d := by omega
    have hh := run_pair_twoPoint_eq (fun θ => chainKernel hd α hα hα1 θ) π V hα hα1
      1 (j.val+1) (Sum.inr (a,j)) failure (fun θ _ => endpoint θ a) tr B b
      (by intro θ c; simp [chainKernel, successfulNext, hj])
      (by
        intro c
        have he (θ : Bool) := run_known_const hd α hα hα1 θ π (V θ) old b (hK θ)
          1 (j.val+1+1) (endpoint θ a) ((Sum.inr (a,j),c,endpoint θ a)::tr)
          (by simp [updateKnowledge, endpoint_transition_signal])
        rw [he false, he true]
        ring)
      (by
        intro c
        exact run_failure_unknown hd α hα hα1 π V old B hU 1 _ _
          (by simpa [updateKnowledge, transitionSignal, failure, good, bad] using htr))
    simpa only [Nat.zero_add, pow_one, add_comm] using hh
  | succ k ih =>
    have hj : j.val+1<d := by omega
    let j' : Fin d := ⟨j.val+1,hj⟩
    have hk' : j'.val+k+1=d := by dsimp [j']; omega
    have hh := run_pair_twoPoint_eq (fun θ => chainKernel hd α hα hα1 θ) π V hα hα1
      (k+2) (j.val+1) (Sum.inr (a,j)) failure (fun _ _ => Sum.inr (a,j')) tr B
      ((1-α^(k+1))*B+α^(k+1)*b)
      (by intro θ c; simp [chainKernel, successfulNext, hj, j'])
      (by
        intro c
        simpa only [j', Nat.add_assoc] using ih j' hk' ((Sum.inr (a,j),c,Sum.inr (a,j'))::tr)
          (by simpa [updateKnowledge, transitionSignal, good, bad] using htr))
      (by
        intro c
        exact run_failure_unknown hd α hα hα1 π V old B hU _ _ _
          (by simpa [updateKnowledge, transitionSignal, failure, good, bad] using htr))
    have he : (1-α^(k+1+1))*B+α^(k+1+1)*b =
        α*((1-α^(k+1))*B+α^(k+1)*b)+(1-α)*B := by rw [pow_succ]; ring
    simpa only [he, Nat.succ_add] using hh

theorem run_initial_equal {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (π : Nested.Policy (ChainState d) Bool) (V : Bool → Trace d → ℝ) (B b : ℝ)
    (hU : ∀ tr, updateKnowledge none tr = none → (V false tr+V true tr)/2 = B)
    (hK : ∀ θ tr, updateKnowledge none tr = some θ → V θ tr = b) :
    (run (chainKernel hd α hα hα1 false) π (V false) (d+2) 0 start [] +
     run (chainKernel hd α hα hα1 true) π (V true) (d+2) 0 start [])/2 =
      (1-α^(d+1))*B+α^(d+1)*b := by
  have hh := run_pair_twoPoint_eq (fun θ => chainKernel hd α hα hα1 θ) π V hα hα1
    (d+1) 0 start failure (fun _ a => Sum.inr (a,⟨0,hd⟩)) [] B ((1-α^d)*B+α^d*b)
    (by intro θ a; simp [chainKernel, successfulNext, start])
    (by
      intro a
      have hh := run_depth_equal hd hα hα1 π V none B b hU hK a (d-1) ⟨0,hd⟩
        (by simp only; omega) [(start,a,Sum.inr (a,⟨0,hd⟩))]
        (by simp [updateKnowledge, transitionSignal, start])
      have hn : d-1+1=d := by omega
      have hn' : d-1+2=d+1 := by omega
      simpa only [hn, hn', Fin.val_zero, Nat.zero_add] using hh)
    (by
      intro a
      exact run_failure_unknown hd α hα hα1 π V none B hU _ _ _
        (by simp [updateKnowledge, transitionSignal, start]))
  have he : (1-α^(d+1))*B+α^(d+1)*b = α*((1-α^d)*B+α^d*b)+(1-α)*B := by
    rw [pow_succ]; ring
  simpa only [he] using hh

theorem optimalPhysical_unknown {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hist : List (Trace d)) (hk : historyKnowledge hist = none) (k : ℕ) :
    physicalBayesDebt hd α hα.le hα1 optimalPhysical hist k = bound (α^(d+1)) k := by
  induction k generalizing hist with
  | zero => simp [physicalBayesDebt, physicalDebt, bound]
  | succ k ih =>
    let V : Bool → Trace d → ℝ := fun θ tr => physicalDebt hd α hα.le hα1 optimalPhysical θ (tr::hist) k
    have hh := run_initial_equal hd hα.le hα1 (optimalPhysical hist) V (bound (α^(d+1)) k) (-(k : ℝ)/4)
      (by
        intro tr htr
        exact ih (tr::hist) (by simpa [historyKnowledge, hk] using htr))
      (by
        intro θ tr htr
        exact optimalPhysical_known hd hα hα1 θ (tr::hist) (by simpa [historyKnowledge, hk] using htr) k)
    have ht := law_sum ((optimalPhysical hist) 0 start)
    simp only [Fintype.sum_bool] at ht
    rw [bound_succ]
    simp only [physicalBayesDebt, physicalDebt]
    rw [source_initial_risk hd hα hα1 false, source_initial_risk hd hα hα1 true]
    simp only [Bool.not_false, Bool.not_true]
    dsimp [V] at hh
    linarith

/-- Theorem 7.1's exact optimum over full-trajectory physical controllers. -/
theorem physical_exact_optimum {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (k : ℕ) : IsLeast {v : ℝ | ∃ σ : PhysicalController d,
      v = physicalBayesDebt hd α hα.le hα1 σ [] k}
      ((1-(1-α^(d+1))^k)/(2*α^(d+1))-(k : ℝ)/4) := by
  rw [← bound_closed (pow_pos hα (d+1))]
  constructor
  · exact ⟨optimalPhysical, (optimalPhysical_unknown hd hα hα1 [] rfl k).symm⟩
  · rintro v ⟨σ,rfl⟩
    exact physical_learner_lower hd hα hα1 σ [] k


/-- The exact Bayes optimum also ranges over private randomized learners, with
an arbitrary fixed probability law of independent random tapes. -/
theorem private_seed_exact_optimum {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) :
    IsLeast {v : ℝ | ∃ σ : Ω → PhysicalController d,
      MeasureTheory.Integrable (fun ω => physicalBayesDebt hd α hα.le hα1 (σ ω) [] k) μ ∧
      v = seedBayesDebt μ hd α hα.le hα1 σ k}
      ((1-(1-α^(d+1))^k)/(2*α^(d+1))-(k : ℝ)/4) := by
  rw [← bound_closed (pow_pos hα (d+1))]
  constructor
  · refine ⟨fun _ => optimalPhysical, ?_, ?_⟩
    · simpa only [optimalPhysical_unknown hd hα hα1 [] rfl k] using
        (MeasureTheory.integrable_const (bound (α^(d+1)) k) :
          MeasureTheory.Integrable (fun _ω : Ω => bound (α^(d+1)) k) μ)
    · unfold seedBayesDebt
      simp only [optimalPhysical_unknown hd hα hα1 [] rfl k]
      simp
  · rintro v ⟨σ,hσ,rfl⟩
    exact private_seed_learner_lower μ hd hα hα1 σ k hσ


/-- The common fallback is `none`; it has reward zero and goes to failure.
At every other state it duplicates branch action `false`, exactly as in 7.2. -/
def fallbackKernel {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (θ : Bool) : Nested.Kernel (ChainState d) (Option Bool) := fun s a =>
  if s = start then twoPoint α hα hα1
    (match a with | none => failure | some i => Sum.inr (i,⟨0,hd⟩)) failure
  else chainKernel hd α hα hα1 θ s (a.getD false)

def fallbackCost {d : ℕ} (H h : ℕ) (s : ChainState d) (_a : Option Bool) : ℝ := chainCost H h s false

def fallbackReward {d : ℕ} (_h : ℕ) (s : ChainState d) (a : Option Bool) : ℝ :=
  if s = start then if a = none then 0 else 1 else 0

def fallbackFlag (θ : Bool) : Option Bool → Bool
  | none => false
  | some a => badFlag θ a

theorem fallback_action_count : Fintype.card (Option Bool) = 3 := by simp

theorem twoPoint_self {S : Type*} [Fintype S] (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (s : S) :
    twoPoint α hα hα1 s s = Nested.pure s := by
  apply Subtype.ext
  funext t
  change α*Nested.pure s t+(1-α)*Nested.pure s t = Nested.pure s t
  ring

theorem fallback_known_safe_transition {d : ℕ} (hd : 0 < d) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (θ : Bool) :
    fallbackKernel hd α hα hα1 θ start none = Nested.pure failure := by
  simp [fallbackKernel, twoPoint_self]

theorem fallback_failure_risk {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) (Option Bool)) (H n h : ℕ) :
    Nested.risk α (fallbackCost H) π (fallbackKernel hd α hα hα1 θ) n h failure = 0 := by
  apply risk_absorbing_zero α hα
  · intro h a; simp [fallbackCost, chainCost, failure, bad]
  · intro a; simp [fallbackKernel, chainKernel, failure, start]

theorem fallback_good_risk {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) (Option Bool)) (H n h : ℕ) :
    Nested.risk α (fallbackCost H) π (fallbackKernel hd α hα hα1 θ) n h good = 0 := by
  apply risk_absorbing_zero α hα
  · intro h a; simp [fallbackCost, chainCost, good, bad]
  · intro a; simp [fallbackKernel, chainKernel, good, start]

theorem fallback_bad_terminal {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) (Option Bool)) :
    Nested.risk α (fallbackCost (d+2)) π (fallbackKernel hd α hα.le hα1 θ) 1 (d+1) bad = 1 := by
  simp only [Nested.risk, fallbackCost, chainCost, and_self, ↓reduceIte, add_zero]
  apply compactCVaR_const _ hα hα1 (by norm_num) (by norm_num)
theorem fallback_depth_risk {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) (Option Bool)) (a : Bool)
    (k : ℕ) (j : Fin d) (hjk : j.val+k+1 = d) :
    Nested.risk α (fallbackCost (d+2)) π (fallbackKernel hd α hα.le hα1 θ)
      (k+2) (j.val+1) (Sum.inr (a,j)) = if a = θ then 0 else 1 := by
  induction k generalizing j with
  | zero =>
    have hj : ¬ j.val+1 < d := by omega
    have ht : j.val+1+1 = d+1 := by omega
    have hstep := rare_step_risk α hα hα1 (fallbackCost (d+2)) π
      (fallbackKernel hd α hα.le hα1 θ) 1 (j.val+1) (Sum.inr (a,j)) failure
      (fun _ => endpoint θ a) (fun _ => badFlag θ a)
      (by intro b; simp [fallbackCost, chainCost, bad])
      (by intro b; simp [fallbackKernel, chainKernel, start, successfulNext, hj])
      (by
        intro b
        rw [ht, badFlag_value]
        by_cases ha : a = θ
        · simp [endpoint, ha, fallback_good_risk]
        · simp [endpoint, ha, fallback_bad_terminal hd hα hα1])
      (fallback_failure_risk hd hα.le hα1 θ π _ _ _)
    simpa only [expectation_const, badFlag_value] using hstep
  | succ k ih =>
    have hj : j.val+1 < d := by omega
    let j' : Fin d := ⟨j.val+1, hj⟩
    have hk' : j'.val+k+1 = d := by dsimp [j']; omega
    have hstep := rare_step_risk α hα hα1 (fallbackCost (d+2)) π
      (fallbackKernel hd α hα.le hα1 θ) (k+2) (j.val+1) (Sum.inr (a,j)) failure
      (fun _ => Sum.inr (a,j')) (fun _ => badFlag θ a)
      (by intro b; simp [fallbackCost, chainCost, bad])
      (by intro b; simp [fallbackKernel, chainKernel, start, successfulNext, hj, j'])
      (by
        intro b
        rw [badFlag_value]
        simpa only [j', Nat.add_assoc] using ih j' hk')
      (fallback_failure_risk hd hα.le hα1 θ π _ _ _)
    simpa only [expectation_const, badFlag_value, Nat.succ_add] using hstep


/-- Equation F.1 with a third, known common safe action. -/
theorem fallback_initial_risk {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) (Option Bool)) :
    Nested.risk α (fallbackCost (d+2)) π (fallbackKernel hd α hα.le hα1 θ)
      (d+2) 0 start = π 0 start (some (!θ)) := by
  have hu (a : Option Bool) :
      Nested.risk α (fallbackCost (d+2)) π (fallbackKernel hd α hα.le hα1 θ) (d+1) 1
        (match a with | none => failure | some i => Sum.inr (i,⟨0,hd⟩)) =
          if fallbackFlag θ a then 1 else 0 := by
    cases a with
    | none => simp [fallbackFlag, fallback_failure_risk]
    | some a =>
      rw [fallbackFlag, badFlag_value]
      have hh := fallback_depth_risk hd hα hα1 θ π a (d-1) ⟨0,hd⟩ (by simp only; omega)
      have hn : d-1+2=d+1 := by omega
      simpa only [hn, Fin.val_zero, Nat.zero_add] using hh
  have hh := rare_step_risk α hα hα1 (fallbackCost (d+2)) π
    (fallbackKernel hd α hα.le hα1 θ) (d+1) 0 start failure
    (fun a => match a with | none => failure | some i => Sum.inr (i,⟨0,hd⟩)) (fallbackFlag θ)
    (by intro a; simp [fallbackCost, chainCost, start, bad])
    (by intro a; simp [fallbackKernel]) hu (fallback_failure_risk hd hα.le hα1 θ π _ _ _)
  have he : expectation (π 0 start) (fun a => if fallbackFlag θ a then (1:ℝ) else 0) = π 0 start (some (!θ)) := by
    cases θ <;> simp [expectation, fallbackFlag, badFlag]
  simpa only [he] using hh

abbrev FallbackTrace (d : ℕ) := List (ChainState d × Option Bool × ChainState d)
abbrev FallbackController (d : ℕ) := List (FallbackTrace d) → Nested.Policy (ChainState d) (Option Bool)

theorem fallbackKernel_no_return {d : ℕ} (hd : 0 < d) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (θ : Bool) (a : Option Bool) (s : ChainState d) :
    fallbackKernel hd α hα hα1 θ s a start = 0 := by
  by_cases hs : s = start
  · subst s
    cases a <;> simp [fallbackKernel, twoPoint_apply, pure_apply, start, failure]
  · simpa only [fallbackKernel, if_neg hs] using chainKernel_no_return hd α hα hα1 θ (a.getD false) s

theorem fallback_source_reward {d : ℕ} (hd : 0 < d) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (θ : Bool) (π : Nested.Policy (ChainState d) (Option Bool))
    (n h : ℕ) (s : ChainState d) :
    Nested.reward fallbackReward π (fallbackKernel hd α hα hα1 θ) (n+1) h s =
      if s = start then 1-(π h s) none else 0 := by
  classical
  induction n generalizing h s with
  | zero =>
    rw [Nested.reward]
    simp only [Nested.reward, mul_zero, sum_const_zero, add_zero, fallbackReward]
    have ht := law_sum (π h s)
    simp only [Fintype.sum_option, Fintype.sum_bool] at ht
    by_cases hs : s = start
    · simp [hs]
      simpa only [hs] using (show (π h s) (some true)+(π h s) (some false) = 1-(π h s) none by linarith)
    · simp [hs]
  | succ n ih =>
    rw [Nested.reward]
    simp only [ih]
    have he (a : Option Bool) :
        (∑ t, fallbackKernel hd α hα hα1 θ s a t *
          (if t = start then 1-(π (h+1) t) none else 0)) = 0 := by
      simp [fallbackKernel_no_return]
    simp only [he, add_zero, fallbackReward]
    have ht := law_sum (π h s)
    simp only [Fintype.sum_option, Fintype.sum_bool] at ht
    by_cases hs : s = start
    · simp [hs]
      simpa only [hs] using (show (π h s) (some true)+(π h s) (some false) = 1-(π h s) none by linarith)
    · simp [hs]
theorem fallback_run_depth_lower {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (π : Nested.Policy (ChainState d) (Option Bool)) (V : Bool → FallbackTrace d → ℝ)
    (B b : ℝ) (hb : ∀ θ tr, b ≤ V θ tr)
    (hB : ∀ tr, B ≤ (V false tr+V true tr)/2)
    (a : Bool) (k : ℕ) (j : Fin d) (hjk : j.val+k+1=d) (tr : FallbackTrace d) :
    (1-α^(k+1))*B+α^(k+1)*b ≤
      (run (fallbackKernel hd α hα hα1 false) π (V false) (k+2) (j.val+1) (Sum.inr (a,j)) tr +
       run (fallbackKernel hd α hα hα1 true) π (V true) (k+2) (j.val+1) (Sum.inr (a,j)) tr)/2 := by
  induction k generalizing j tr with
  | zero =>
    have hj : ¬ j.val+1<d := by omega
    have hh := run_pair_twoPoint (fun θ => fallbackKernel hd α hα hα1 θ) π V hα hα1
      1 (j.val+1) (Sum.inr (a,j)) failure (fun θ _ => endpoint θ a) tr B b
      (by intro θ c; simp [fallbackKernel, chainKernel, start, successfulNext, hj])
      (by
        intro c
        have h0 := run_floor (fallbackKernel hd α hα hα1 false) π (V false) b (hb false)
          1 (j.val+1+1) (endpoint false a) ((Sum.inr (a,j),c,endpoint false a)::tr)
        have h1 := run_floor (fallbackKernel hd α hα hα1 true) π (V true) b (hb true)
          1 (j.val+1+1) (endpoint true a) ((Sum.inr (a,j),c,endpoint true a)::tr)
        linarith)
      (by
        intro c
        apply run_pair_absorbing _ _ π (V false) (V true) failure
        · intro c; simp [fallbackKernel, chainKernel, start, failure]
        · intro c; simp [fallbackKernel, chainKernel, start, failure]
        · exact hB)
    simpa only [Nat.zero_add, pow_one, add_comm] using hh
  | succ k ih =>
    have hj : j.val+1<d := by omega
    let j' : Fin d := ⟨j.val+1,hj⟩
    have hk' : j'.val+k+1=d := by dsimp [j']; omega
    have hh := run_pair_twoPoint (fun θ => fallbackKernel hd α hα hα1 θ) π V hα hα1
      (k+2) (j.val+1) (Sum.inr (a,j)) failure (fun _ _ => Sum.inr (a,j')) tr B
      ((1-α^(k+1))*B+α^(k+1)*b)
      (by intro θ c; simp [fallbackKernel, chainKernel, start, successfulNext, hj, j'])
      (by intro c; simpa only [j', Nat.add_assoc] using ih j' hk' ((Sum.inr (a,j),c,Sum.inr (a,j'))::tr))
      (by
        intro c
        apply run_pair_absorbing _ _ π (V false) (V true) failure
        · intro c; simp [fallbackKernel, chainKernel, start, failure]
        · intro c; simp [fallbackKernel, chainKernel, start, failure]
        · exact hB)
    have he : (1-α^(k+1+1))*B+α^(k+1+1)*b =
        α*((1-α^(k+1))*B+α^(k+1)*b)+(1-α)*B := by rw [pow_succ]; ring
    simpa only [he, Nat.succ_add] using hh


/-- The fallback may postpone revelation, so its full-feedback continuation is
bounded by the same rare-event expression. -/
theorem fallback_run_initial_lower {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (π : Nested.Policy (ChainState d) (Option Bool)) (V : Bool → FallbackTrace d → ℝ)
    (B b : ℝ) (hb : ∀ θ tr, b ≤ V θ tr)
    (hB : ∀ tr, B ≤ (V false tr+V true tr)/2) (hBb : b ≤ B) :
    (1-α^(d+1))*B+α^(d+1)*b ≤
      (run (fallbackKernel hd α hα hα1 false) π (V false) (d+2) 0 start [] +
       run (fallbackKernel hd α hα hα1 true) π (V true) (d+2) 0 start [])/2 := by
  have hf (a : Option Bool) (n h : ℕ) (tr : FallbackTrace d) :
      B ≤ (run (fallbackKernel hd α hα hα1 false) π (V false) n h failure tr +
        run (fallbackKernel hd α hα hα1 true) π (V true) n h failure tr)/2 := by
    apply run_pair_absorbing _ _ π (V false) (V true) failure
    · intro a; simp [fallbackKernel, chainKernel, failure, start]
    · intro a; simp [fallbackKernel, chainKernel, failure, start]
    · exact hB
  have hh := run_pair_twoPoint (fun θ => fallbackKernel hd α hα hα1 θ) π V hα hα1
    (d+1) 0 start failure
    (fun _ a => match a with | none => failure | some i => Sum.inr (i,⟨0,hd⟩)) []
    B ((1-α^d)*B+α^d*b)
    (by intro θ a; simp [fallbackKernel])
    (by
      intro a
      cases a with
      | none =>
        have hh := hf none (d+1) 1 [(start,none,failure)]
        have hp := mul_nonneg (pow_nonneg hα d) (sub_nonneg.mpr hBb)
        linarith
      | some a =>
        have hh := fallback_run_depth_lower hd hα hα1 π V B b hb hB a (d-1) ⟨0,hd⟩
          (by simp only; omega) [(start,some a,Sum.inr (a,⟨0,hd⟩))]
        have hn : d-1+1=d := by omega
        have hn' : d-1+2=d+1 := by omega
        simpa only [hn, hn', Fin.val_zero, Nat.zero_add] using hh)
    (by intro a; exact hf a _ _ _)
  have he : (1-α^(d+1))*B+α^(d+1)*b = α*((1-α^d)*B+α^d*b)+(1-α)*B := by
    rw [pow_succ]; ring
  simpa only [he] using hh


def fallbackRiskScore {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) (Option Bool)) : ℝ :=
  Nested.risk α (fallbackCost (d+2)) π (fallbackKernel hd α hα hα1 θ) (d+2) 0 start - 1/4

def fallbackRewardScore {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) (Option Bool)) : ℝ :=
  1-Nested.reward fallbackReward π (fallbackKernel hd α hα hα1 θ) (d+2) 0 start

def fallbackValue {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (score : Bool → Nested.Policy (ChainState d) (Option Bool) → ℝ)
    (σ : FallbackController d) (θ : Bool) (hist : List (FallbackTrace d)) : ℕ → ℝ
  | 0 => 0
  | k+1 => score θ (σ hist) +
      run (fallbackKernel hd α hα hα1 θ) (σ hist)
        (fun tr => fallbackValue hd α hα hα1 score σ θ (tr::hist) k) (d+2) 0 start []

def fallbackBayes {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (score : Bool → Nested.Policy (ChainState d) (Option Bool) → ℝ)
    (σ : FallbackController d) (hist : List (FallbackTrace d)) (k : ℕ) : ℝ :=
  (fallbackValue hd α hα hα1 score σ false hist k + fallbackValue hd α hα hα1 score σ true hist k)/2

theorem expectation_affine {Ω : Type*} [Fintype Ω] (P : Law Ω) (f g : Ω → ℝ) (c : ℝ) :
    expectation P (fun i => f i+c*g i) = expectation P f+c*expectation P g := by
  simp only [expectation, mul_add, sum_add_distrib, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

theorem run_affine {S A : Type*} [Fintype S] [Fintype A] (q : Nested.Kernel S A)
    (π : Nested.Policy S A) (V W : List (S × A × S) → ℝ) (c : ℝ)
    (n h : ℕ) (s : S) (tr : List (S × A × S)) :
    run q π (fun tr => V tr+c*W tr) n h s tr =
      run q π V n h s tr+c*run q π W n h s tr := by
  induction n generalizing h s tr with
  | zero => rfl
  | succ n ih => simp only [run, ih, expectation_affine]

theorem fallbackValue_affine {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (f g : Bool → Nested.Policy (ChainState d) (Option Bool) → ℝ)
    (σ : FallbackController d) (c : ℝ) (θ : Bool) (hist : List (FallbackTrace d)) (k : ℕ) :
    fallbackValue hd α hα hα1 (fun θ π => f θ π+c*g θ π) σ θ hist k =
      fallbackValue hd α hα hα1 f σ θ hist k+c*fallbackValue hd α hα hα1 g σ θ hist k := by
  induction k generalizing hist with
  | zero => simp [fallbackValue]
  | succ k ih =>
    simp only [fallbackValue, ih, run_affine]
    ring

theorem fallbackBayes_affine {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (f g : Bool → Nested.Policy (ChainState d) (Option Bool) → ℝ)
    (σ : FallbackController d) (c : ℝ) (hist : List (FallbackTrace d)) (k : ℕ) :
    fallbackBayes hd α hα hα1 (fun θ π => f θ π+c*g θ π) σ hist k =
      fallbackBayes hd α hα hα1 f σ hist k+c*fallbackBayes hd α hα hα1 g σ hist k := by
  simp only [fallbackBayes, fallbackValue_affine]
  ring

theorem fallbackValue_floor {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (score : Bool → Nested.Policy (ChainState d) (Option Bool) → ℝ)
    (hs : ∀ θ π, -(1:ℝ)/4 ≤ score θ π) (σ : FallbackController d)
    (θ : Bool) (hist : List (FallbackTrace d)) (k : ℕ) :
    -(k : ℝ)/4 ≤ fallbackValue hd α hα hα1 score σ θ hist k := by
  induction k generalizing hist with
  | zero => simp [fallbackValue]
  | succ k ih =>
    have hh := run_floor (fallbackKernel hd α hα hα1 θ) (σ hist)
      (fun tr => fallbackValue hd α hα hα1 score σ θ (tr::hist) k) (-(k : ℝ)/4)
      (fun tr => ih (tr::hist)) (d+2) 0 start []
    have hs' := hs θ (σ hist)
    simp only [fallbackValue, Nat.cast_add, Nat.cast_one]
    linarith

theorem fallback_combined_lower {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (σ : FallbackController d) (hist : List (FallbackTrace d)) (k : ℕ) :
    bound (α^(d+1)) k ≤
      fallbackBayes hd α hα.le hα1 (fallbackRiskScore hd α hα.le hα1) σ hist k +
        (1/2)*fallbackBayes hd α hα.le hα1 (fallbackRewardScore hd α hα.le hα1) σ hist k := by
  let score := fun θ π => fallbackRiskScore hd α hα.le hα1 θ π +
    (1/2)*fallbackRewardScore hd α hα.le hα1 θ π
  have hs : ∀ θ π, -(1:ℝ)/4 ≤ score θ π := by
    intro θ π
    dsimp [score, fallbackRiskScore, fallbackRewardScore]
    rw [fallback_initial_risk hd hα hα1 θ π, fallback_source_reward hd α hα.le hα1 θ π (d+1) 0 start]
    simp only [ite_true]
    have h0 : (0:ℝ) ≤ π 0 start (some (!θ)) := (π 0 start).property.1 (some (!θ))
    have h1 : (0:ℝ) ≤ π 0 start none := (π 0 start).property.1 none
    linarith
  have hl : bound (α^(d+1)) k ≤ fallbackBayes hd α hα.le hα1 score σ hist k := by
    induction k generalizing hist with
    | zero => simp [fallbackBayes, fallbackValue, bound]
    | succ k ih =>
      let V : Bool → FallbackTrace d → ℝ := fun θ tr => fallbackValue hd α hα.le hα1 score σ θ (tr::hist) k
      have hh := fallback_run_initial_lower hd hα.le hα1 (σ hist) V
        (bound (α^(d+1)) k) (-(k : ℝ)/4)
        (fun θ tr => fallbackValue_floor hd α hα.le hα1 score hs σ θ (tr::hist) k)
        (fun tr => ih (tr::hist)) (bound_floor (pow_le_one₀ hα.le hα1) k)
      have ht := law_sum ((σ hist) 0 start)
      simp only [Fintype.sum_option, Fintype.sum_bool] at ht
      have he (θ : Bool) : score θ (σ hist) =
          (σ hist) 0 start (some (!θ)) - 1/4 + (1/2)*((σ hist) 0 start none) := by
        dsimp [score, fallbackRiskScore, fallbackRewardScore]
        rw [fallback_initial_risk hd hα hα1 θ, fallback_source_reward hd α hα.le hα1 θ (σ hist) (d+1) 0 start]
        simp
      rw [bound_succ]
      simp only [fallbackBayes, fallbackValue, he, Bool.not_false, Bool.not_true]
      dsimp [V] at hh
      linarith
  simpa only [score, fallbackBayes_affine] using hl

def seedFallback {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (score : Bool → Nested.Policy (ChainState d) (Option Bool) → ℝ)
    (σ : Ω → FallbackController d) (k : ℕ) : ℝ :=
  ∫ ω, fallbackBayes hd α hα hα1 score (σ ω) [] k ∂μ

/-- The complete source Corollary 7.2 inequality, including independent private
randomness and full uncompressed trajectory feedback. -/
theorem private_seed_fallback_tradeoff {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (σ : Ω → FallbackController d) (k : ℕ)
    (hρ : MeasureTheory.Integrable
      (fun ω => fallbackBayes hd α hα.le hα1 (fallbackRiskScore hd α hα.le hα1) (σ ω) [] k) μ)
    (hr : MeasureTheory.Integrable
      (fun ω => fallbackBayes hd α hα.le hα1 (fallbackRewardScore hd α hα.le hα1) (σ ω) [] k) μ) :
    bound (α^(d+1)) k ≤
      seedFallback μ hd α hα.le hα1 (fallbackRiskScore hd α hα.le hα1) σ k +
      (1/2)*seedFallback μ hd α hα.le hα1 (fallbackRewardScore hd α hα.le hα1) σ k := by
  unfold seedFallback
  calc
    bound (α^(d+1)) k = ∫ _ω : Ω, bound (α^(d+1)) k ∂μ := by simp
    _ ≤ ∫ ω, (fallbackBayes hd α hα.le hα1 (fallbackRiskScore hd α hα.le hα1) (σ ω) [] k +
        (1/2)*fallbackBayes hd α hα.le hα1 (fallbackRewardScore hd α hα.le hα1) (σ ω) [] k) ∂μ :=
      MeasureTheory.integral_mono (MeasureTheory.integrable_const _) (hρ.add (hr.const_mul (1/2)))
        (fun ω => fallback_combined_lower hd hα hα1 (σ ω) [] k)
    _ = _ := by rw [MeasureTheory.integral_add hρ (hr.const_mul (1/2)), MeasureTheory.integral_const_mul]

/-- Both model-dependent branch comparators and the known common fallback are
exhibited in the actual three-action physical model. -/
theorem fallback_comparators {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ θ : Bool,
      Nested.risk α (fallbackCost (d+2)) (fun _ _ => Nested.pure (some θ))
        (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start = 0 ∧
      Nested.reward fallbackReward (fun _ _ => Nested.pure (some θ))
        (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start = 1) ∧
    (∀ θ : Bool,
      Nested.risk α (fallbackCost (d+2)) (fun _ _ => Nested.pure none)
        (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start = 0 ∧
      Nested.reward fallbackReward (fun _ _ => Nested.pure none)
        (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start = 0) := by
  constructor
  · intro θ
    constructor
    · rw [fallback_initial_risk hd hα hα1 θ]
      cases θ <;> simp [pure_apply]
    · rw [fallback_source_reward hd α hα.le hα1 θ _ (d+1) 0 start]
      simp [pure_apply]
  · intro θ
    constructor
    · rw [fallback_initial_risk hd hα hα1 θ]
      simp [pure_apply]
    · rw [fallback_source_reward hd α hα.le hα1 θ _ (d+1) 0 start]
      simp [pure_apply]

/-- Equation (7.4) for arbitrary private randomized source learners. -/
theorem private_seed_fallback_pareto {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα2 : α ≤ 1/2)
    (σ : Ω → FallbackController d) {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hρi : ∀ k, MeasureTheory.Integrable
      (fun ω => fallbackBayes hd α hα.le (by linarith) (fallbackRiskScore hd α hα.le (by linarith)) (σ ω) [] k) μ)
    (hri : ∀ k, MeasureTheory.Integrable
      (fun ω => fallbackBayes hd α hα.le (by linarith) (fallbackRewardScore hd α hα.le (by linarith)) (σ ω) [] k) μ)
    (hρ : ∀ k, seedFallback μ hd α hα.le (by linarith)
      (fallbackRiskScore hd α hα.le (by linarith)) σ k ≤ G)
    (hr : ∀ k, seedFallback μ hd α hα.le (by linarith)
      (fallbackRewardScore hd α hα.le (by linarith)) σ k ≤ F*Real.sqrt (k : ℝ)) :
    1/(64*α^(d+1)) ≤ G ∨ Real.sqrt 2/(32*Real.sqrt (α^(d+1))) ≤ F := by
  have hβ : 0 < α^(d+1) := pow_pos hα _
  have hβ4 : α^(d+1) ≤ 1/4 := by
    have hn : 2 ≤ d+1 := by omega
    have hp := pow_le_pow_of_le_one hα.le (show α ≤ 1 by linarith) hn
    have hs := pow_le_pow_left₀ hα.le hα2 2
    norm_num at hs
    exact hp.trans hs
  apply pareto_coefficients hβ hβ4 hF hG
  have hl := (tailored_bound hβ hβ4).trans
    (private_seed_fallback_tradeoff μ hd hα (by linarith) σ (K0 (α^(d+1)))
      (hρi (K0 (α^(d+1)))) (hri (K0 (α^(d+1)))))
  have hrr := hr (K0 (α^(d+1)))
  have hρρ := hρ (K0 (α^(d+1)))
  linarith

end
end Paper36.LowerBound
