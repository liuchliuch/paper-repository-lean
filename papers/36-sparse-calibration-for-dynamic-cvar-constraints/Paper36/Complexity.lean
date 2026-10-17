import Paper36.RiskBridge
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Planning complexity: the analytic core of the Subset-Sum reduction

This file formalizes Appendix E, equation (E.1), including the integrality
argument.  Complexity-class conclusions are deliberately not encoded as
assumptions: the finite reduction proved here can be combined with the external
NP-completeness theorem for binary-encoded Subset-Sum.
-/

namespace Paper36.Complexity

open scoped BigOperators

noncomputable section

/-- Upper-tail risk multiplier of a Bernoulli take action. -/
def bernoulliTail (α x : ℝ) : ℝ := min (x / α) 1

/-- For a tail mass below one, Bernoulli upper-tail risk dominates its mean. -/
theorem le_bernoulliTail {α x : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : x ≤ bernoulliTail α x := by
  unfold bernoulliTail
  apply le_min
  · apply (le_div_iff₀ hα).2
    nlinarith
  · exact hx1

/-- The domination is strict at every genuinely randomized take probability. -/
theorem bernoulliTail_eq_iff {α x : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : bernoulliTail α x = x ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro he
    unfold bernoulliTail at he
    rcases le_total (x / α) 1 with h | h
    · rw [min_eq_left h] at he
      have : x = x * α := (div_eq_iff hα.ne').1 he
      left
      nlinarith
    · rw [min_eq_right h] at he
      exact Or.inr he.symm
  · rintro (rfl | rfl)
    · simp [bernoulliTail]
    · unfold bernoulliTail
      have h : (1 : ℝ) ≤ 1 / α := (le_div_iff₀ hα).2 (by simpa using hα1.le)
      rw [min_eq_right h]

/-- Expected reward of the one-state take/skip construction. -/
def linearReward {ι : Type*} [Fintype ι] (w x : ι → ℝ) : ℝ := ∑ i, w i * x i

/-- Nested risk after deterministic self-loop translation has been unfolded. -/
def reducedRisk {ι : Type*} [Fintype ι] (α : ℝ) (w x : ι → ℝ) : ℝ :=
  ∑ i, w i * bernoulliTail α (x i)

theorem linearReward_le_reducedRisk {ι : Type*} [Fintype ι]
    {α : ℝ} {w x : ι → ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    linearReward w x ≤ reducedRisk α w x := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (le_bernoulliTail hα hα1 (hx i) (hx1 i)) (hw i)

/-- Positive weights make equality of total risk and reward force deterministic actions. -/
theorem reducedRisk_eq_reward_iff {ι : Type*} [Fintype ι]
    {α : ℝ} {w x : ι → ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    reducedRisk α w x = linearReward w x ↔ ∀ i, x i = 0 ∨ x i = 1 := by
  constructor
  · intro he i
    have hnonneg : ∀ j, 0 ≤ w j * (bernoulliTail α (x j) - x j) := by
      intro j
      exact mul_nonneg (hw j).le (sub_nonneg.2 (le_bernoulliTail hα hα1 (hx j) (hx1 j)))
    have hsum : ∑ j, w j * (bernoulliTail α (x j) - x j) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 he
    have hi : w i * (bernoulliTail α (x i) - x i) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).1 hsum i (Finset.mem_univ i)
    have ht : bernoulliTail α (x i) = x i := by
      rcases mul_eq_zero.1 hi with h | h
      · exact False.elim ((hw i).ne' h)
      · exact sub_eq_zero.1 h
    exact (bernoulliTail_eq_iff hα hα1 (hx i) (hx1 i)).1 ht
  · intro hb
    apply Finset.sum_congr rfl
    intro i _
    rw [(bernoulliTail_eq_iff hα hα1 (hx i) (hx1 i)).2 (hb i)]

/-- The two opposite target inequalities are exactly integrality plus the target equality. -/
theorem reduced_feasible_iff {ι : Type*} [Fintype ι]
    {α B : ℝ} {w x : ι → ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    (reducedRisk α w x ≤ B ∧ B ≤ linearReward w x) ↔
      (∀ i, x i = 0 ∨ x i = 1) ∧ linearReward w x = B := by
  constructor
  · rintro ⟨hr, hv⟩
    have hvr := linearReward_le_reducedRisk hα hα1 (fun i => (hw i).le) hx hx1
    have he : reducedRisk α w x = linearReward w x := le_antisymm (hr.trans hv) hvr
    exact ⟨(reducedRisk_eq_reward_iff hα hα1 hw hx hx1).1 he, le_antisymm (hvr.trans hr) hv⟩
  · rintro ⟨hb, he⟩
    rw [(reducedRisk_eq_reward_iff hα hα1 hw hx hx1).2 hb, he]
    exact ⟨le_rfl, le_rfl⟩

/-- Finite binary controls and a subset of stages are equivalent encodings. -/
theorem binary_reward_iff_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (B : ℝ) :
    (∃ x : ι → ℝ, (∀ i, x i = 0 ∨ x i = 1) ∧ linearReward w x = B) ↔
      ∃ s : Finset ι, ∑ i ∈ s, w i = B := by
  constructor
  · rintro ⟨x, hb, he⟩
    refine ⟨Finset.univ.filter (fun i => x i = 1), ?_⟩
    have hsum : linearReward w x = ∑ i ∈ Finset.univ.filter (fun i => x i = 1), w i := by
      unfold linearReward
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      rcases hb i with h | h <;> simp [h]
    exact hsum.symm.trans he
  · rintro ⟨s, hs⟩
    refine ⟨fun i => if i ∈ s then 1 else 0, ?_, ?_⟩
    · intro i
      by_cases hi : i ∈ s <;> simp [hi]
    · simpa [linearReward, Finset.sum_ite_irrel, Finset.sum_ite_mem] using hs

/-- Exact finite reduction equivalence; no integrality assumption is added to the planner. -/
theorem exists_reduced_feasible_iff_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α B : ℝ} {w : ι → ℝ} (hα : 0 < α) (hα1 : α < 1) (hw : ∀ i, 0 < w i) :
    (∃ x : ι → ℝ, (∀ i, 0 ≤ x i) ∧ (∀ i, x i ≤ 1) ∧
      reducedRisk α w x ≤ B ∧ B ≤ linearReward w x) ↔
      ∃ s : Finset ι, ∑ i ∈ s, w i = B := by
  rw [← binary_reward_iff_subset]
  constructor
  · rintro ⟨x, hx, hx1, hf⟩
    exact ⟨x, (reduced_feasible_iff hα hα1 hw hx hx1).1 hf⟩
  · rintro ⟨x, hb, he⟩
    have hx : ∀ i, 0 ≤ x i := fun i => by rcases hb i with h | h <;> simp [h]
    have hx1 : ∀ i, x i ≤ 1 := fun i => by rcases hb i with h | h <;> simp [h]
    exact ⟨x, hx, hx1, (reduced_feasible_iff hα hα1 hw hx hx1).2 ⟨hb, he⟩⟩

/-- A positive total weight allows the rational normalization in Appendix E. -/
theorem normalized_subset_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℕ) (B : ℕ) {C : ℝ} (hC : 0 < C) :
    (∃ s : Finset ι, ∑ i ∈ s, (w i : ℝ) / C = (B : ℝ) / C) ↔
      ∃ s : Finset ι, ∑ i ∈ s, w i = B := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [← Finset.sum_div] at hs
    have hr : (∑ i ∈ s, (w i : ℝ)) = (B : ℝ) := (div_left_inj' hC.ne').1 hs
    exact_mod_cast hr
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [← Finset.sum_div]
    have hr : (∑ i ∈ s, (w i : ℝ)) = (B : ℝ) := by exact_mod_cast hs
    rw [hr]

/-- Subset-Sum maps to the one-state risk/reward inequalities using exactly wᵢ/C. -/
theorem subset_sum_reduction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℕ) (B : ℕ) {α C : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hw : ∀ i, 0 < w i) (hC : 0 < C) :
    (∃ x : ι → ℝ, (∀ i, 0 ≤ x i) ∧ (∀ i, x i ≤ 1) ∧
      reducedRisk α (fun i => (w i : ℝ) / C) x ≤ (B : ℝ) / C ∧
      (B : ℝ) / C ≤ linearReward (fun i => (w i : ℝ) / C) x) ↔
      ∃ s : Finset ι, ∑ i ∈ s, w i = B := by
  rw [exists_reduced_feasible_iff_subset hα hα1]
  · exact normalized_subset_iff w B hC
  · intro i
    exact div_pos (by exact_mod_cast hw i) hC

/-- The explicitly given all-skip policy has risk zero and is strictly feasible for B > 0. -/
theorem all_skip_strictly_feasible {ι : Type*} [Fintype ι]
    (w : ι → ℝ) {α B C : ℝ} (hB : 0 < B) (hC : 0 < C) :
    reducedRisk α w (fun _ => 0) = 0 ∧ reducedRisk α w (fun _ => 0) < B / C := by
  simp only [reducedRisk, bernoulliTail, zero_div, min_eq_left zero_le_one,
    mul_zero, Finset.sum_const_zero]
  exact ⟨trivial, div_pos hB hC⟩

/-- A dummy stage of weight `B+1` can never be selected in a subset of total B. -/
def dummyWeight {ι : Type*} (w : ι → ℕ) (B : ℕ) : Option ι → ℕ
  | none => B + 1
  | some i => w i

theorem dummy_subset_sum_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℕ) (B : ℕ) :
    (∃ s : Finset (Option ι), ∑ i ∈ s, dummyWeight w B i = B) ↔
      ∃ s : Finset ι, ∑ i ∈ s, w i = B := by
  constructor
  · rintro ⟨s, hs⟩
    have hn : none ∉ s := by
      intro hn
      have hh := Finset.single_le_sum (f := dummyWeight w B) (fun i _ => Nat.zero_le _) hn
      rw [hs] at hh
      change B + 1 ≤ B at hh
      omega
    let t := Finset.univ.filter (fun i => some i ∈ s)
    have heq : t.image Option.some = s := by
      ext o
      cases o with
      | none => simp [hn]
      | some i => simp [t]
    refine ⟨t, ?_⟩
    rw [← heq, Finset.sum_image] at hs
    · exact hs
    · exact fun i _ j _ h => Option.some.inj h
  · rintro ⟨s, hs⟩
    refine ⟨s.image Option.some, ?_⟩
    rw [Finset.sum_image]
    · exact hs
    · exact fun i _ j _ h => Option.some.inj h

/-- The appended instance has total weight strictly larger than its target. -/
theorem dummy_total_exceeds_target {ι : Type*} [Fintype ι] (w : ι → ℕ) (B : ℕ) :
    B < ∑ i, dummyWeight w B i := by
  rw [univ_option, Finset.sum_insertNone]
  simp only [dummyWeight]
  omega

/-- After normalizing by the total, every stage cost is in [0,1]. -/
theorem normalized_weight_bounds {ι : Type*} [Fintype ι]
    (w : ι → ℕ) {C : ℝ} (hC : 0 < C) (htot : C = ∑ i, (w i : ℝ)) (i : ι) :
    0 ≤ (w i : ℝ) / C ∧ (w i : ℝ) / C ≤ 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hC.le
  · apply (div_le_one hC).2
    rw [htot]
    exact Finset.single_le_sum (fun j _ => Nat.cast_nonneg (w j)) (Finset.mem_univ i)

/-! ## Explicit rational degree-two encoding of (E.2)--(E.5) -/

/-- Variables are tagged so policy, reward, risk, threshold and positive-part
coordinates can never be accidentally identified. -/
inductive PlanningVar (H : ℕ) (S A : Type*)
  | policy : Fin H → S → A → PlanningVar H S A
  | reward : Fin (H + 1) → S → PlanningVar H S A
  | risk : Fin (H + 1) → S → PlanningVar H S A
  | threshold : Fin H → S → PlanningVar H S A
  | positive : Fin H → S → A → S → PlanningVar H S A
  deriving DecidableEq, Fintype

inductive PlanningConstraint (H : ℕ) (S A : Type*)
  | policyNonneg : Fin H → S → A → PlanningConstraint H S A
  | policyTotal : Fin H → S → PlanningConstraint H S A
  | terminalReward : S → PlanningConstraint H S A
  | terminalRisk : S → PlanningConstraint H S A
  | rewardStep : Fin H → S → PlanningConstraint H S A
  | positiveNonneg : Fin H → S → A → S → PlanningConstraint H S A
  | positiveGap : Fin H → S → A → S → PlanningConstraint H S A
  | riskStep : Fin H → S → PlanningConstraint H S A
  | budget : PlanningConstraint H S A
  | target : PlanningConstraint H S A
  deriving DecidableEq, Fintype

variable {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]

/-- The five arrays in the existential-real witness of Appendix E. -/
structure PlanningWitness (H : ℕ) (S A : Type*) where
  policy : Fin H → S → A → ℝ
  reward : Fin (H + 1) → S → ℝ
  risk : Fin (H + 1) → S → ℝ
  threshold : Fin H → S → ℝ
  positive : Fin H → S → A → S → ℝ

def PlanningWitness.assignment (W : PlanningWitness H S A) : PlanningVar H S A → ℝ
  | .policy h s a => W.policy h s a
  | .reward h s => W.reward h s
  | .risk h s => W.risk h s
  | .threshold h s => W.threshold h s
  | .positive h s a t => W.positive h s a t

/-- Literal numerical constraints (E.2)--(E.5), including the policy simplices. -/
structure PlanningConditions (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) (W : PlanningWitness H S A) : Prop where
  policy_nonneg : ∀ h s a, 0 ≤ W.policy h s a
  policy_total : ∀ h s, ∑ a, W.policy h s a = 1
  terminal_reward : ∀ s, W.reward (Fin.last H) s = 0
  terminal_risk : ∀ s, W.risk (Fin.last H) s = 0
  reward_step : ∀ h s, W.reward h.castSucc s =
    ∑ a, W.policy h s a * ((r h s a : ℝ) + ∑ t, (p s a t : ℝ) * W.reward h.succ t)
  positive_nonneg : ∀ h s a t, 0 ≤ W.positive h s a t
  positive_gap : ∀ h s a t,
    (c h s a : ℝ) + W.risk h.succ t - W.threshold h s ≤ W.positive h s a t
  risk_step : ∀ h s,
    W.threshold h s + (α : ℝ)⁻¹ *
      (∑ a, ∑ t, W.policy h s a * (p s a t : ℝ) * W.positive h s a t) ≤ W.risk h.castSucc s
  budget : W.risk 0 s₀ ≤ (τ : ℝ)
  target : (target : ℝ) ≤ W.reward 0 s₀

open MvPolynomial

/-- A conjunction over this finite family is the actual rational semialgebraic
system. Division occurs only in its rational coefficients, never in variables. -/
def planningPolynomial (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) : PlanningConstraint H S A → MvPolynomial (PlanningVar H S A) ℚ
  | .policyNonneg h s a => X (.policy h s a)
  | .policyTotal h s => (∑ a, X (.policy h s a)) - C 1
  | .terminalReward s => X (.reward (Fin.last H) s)
  | .terminalRisk s => X (.risk (Fin.last H) s)
  | .rewardStep h s => X (.reward h.castSucc s) -
      ∑ a, X (.policy h s a) * (C (r h s a) + ∑ t, C (p s a t) * X (.reward h.succ t))
  | .positiveNonneg h s a t => X (.positive h s a t)
  | .positiveGap h s a t => X (.positive h s a t) - C (c h s a) -
      X (.risk h.succ t) + X (.threshold h s)
  | .riskStep h s => X (.risk h.castSucc s) - X (.threshold h s) -
      ∑ a, ∑ t, C (p s a t / α) * X (.policy h s a) * X (.positive h s a t)
  | .budget => C τ - X (.risk 0 s₀)
  | .target => X (.reward 0 s₀) - C target

def PlanningConstraint.isEquality : PlanningConstraint H S A → Bool
  | .policyTotal .. | .terminalReward .. | .terminalRisk .. | .rewardStep .. => true
  | _ => false

def polynomialSatisfaction (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) (x : PlanningVar H S A → ℝ) : Prop :=
  ∀ k : PlanningConstraint H S A,
    let y := MvPolynomial.eval₂ (Rat.castHom ℝ) x (planningPolynomial r c p α τ target s₀ k)
    if k.isEquality then y = 0 else 0 ≤ y

private theorem degree_add_le {V : Type*} {f g : MvPolynomial V ℚ} {d : ℕ}
    (hf : f.totalDegree ≤ d) (hg : g.totalDegree ≤ d) : (f + g).totalDegree ≤ d :=
  (totalDegree_add _ _).trans (max_le hf hg)

private theorem degree_sub_le {V : Type*} {f g : MvPolynomial V ℚ} {d : ℕ}
    (hf : f.totalDegree ≤ d) (hg : g.totalDegree ≤ d) : (f - g).totalDegree ≤ d :=
  (totalDegree_sub _ _).trans (max_le hf hg)

private theorem degree_const_mul_le {V : Type*} (q : ℚ) (f : MvPolynomial V ℚ) {d : ℕ}
    (hf : f.totalDegree ≤ d) : (C q * f).totalDegree ≤ d := by
  exact (totalDegree_mul _ _).trans (by simpa using hf)

/-- Every polynomial in the complete planning encoding has total degree at most two. -/
theorem planningPolynomial_degree (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) (k : PlanningConstraint H S A) :
    (planningPolynomial r c p α τ target s₀ k).totalDegree ≤ 2 := by
  have hx (v : PlanningVar H S A) : (X v : MvPolynomial _ ℚ).totalDegree ≤ 1 := by simp
  have hx2 (v : PlanningVar H S A) : (X v : MvPolynomial _ ℚ).totalDegree ≤ 2 := by simp
  have hc2 (q : ℚ) : (C q : MvPolynomial (PlanningVar H S A) ℚ).totalDegree ≤ 2 := by simp
  cases k with
  | policyNonneg => exact hx2 _
  | policyTotal h s =>
    exact degree_sub_le (totalDegree_finsetSum_le fun a _ => hx2 _) (hc2 _)
  | terminalReward => exact hx2 _
  | terminalRisk => exact hx2 _
  | rewardStep h s =>
    apply degree_sub_le (hx2 _)
    apply totalDegree_finsetSum_le
    intro a _
    apply (totalDegree_mul _ _).trans
    have hinner : (C (r h s a) + ∑ t, C (p s a t) * X (PlanningVar.reward (A := A) h.succ t)).totalDegree ≤ 1 := by
      apply degree_add_le (by simp)
      exact totalDegree_finsetSum_le (fun t _ => degree_const_mul_le _ _ (hx _))
    exact (Nat.add_le_add (hx _) hinner)
  | positiveNonneg => exact hx2 _
  | positiveGap => exact degree_add_le (degree_sub_le (degree_sub_le (hx2 _) (hc2 _)) (hx2 _)) (hx2 _)
  | riskStep h s =>
    apply degree_sub_le (degree_sub_le (hx2 _) (hx2 _))
    apply totalDegree_finsetSum_le
    intro a _
    apply totalDegree_finsetSum_le
    intro t _
    apply (totalDegree_mul _ _).trans
    exact Nat.add_le_add (degree_const_mul_le _ _ (hx _)) (hx _)
  | budget => exact degree_sub_le (hc2 _) (hx2 _)
  | target => exact degree_sub_le (hx2 _) (hc2 _)

/-- Number of existential real coordinates in the displayed construction. -/
theorem planning_variable_count : Fintype.card (PlanningVar H S A) =
    H * Fintype.card S * Fintype.card A +
      (H + 1) * Fintype.card S + (H + 1) * Fintype.card S +
      H * Fintype.card S + H * Fintype.card S * Fintype.card A * Fintype.card S := by
  rw [← Fintype.card_congr (PlanningVar.proxyTypeEquiv H S A)]
  simp
  ring

/-- Number of atomic constraints; all families have polynomial size. -/
theorem planning_constraint_count : Fintype.card (PlanningConstraint H S A) =
    H * Fintype.card S * Fintype.card A + H * Fintype.card S +
      Fintype.card S + Fintype.card S + H * Fintype.card S +
      H * Fintype.card S * Fintype.card A * Fintype.card S +
      H * Fintype.card S * Fintype.card A * Fintype.card S +
      H * Fintype.card S + 2 := by
  rw [← Fintype.card_congr (PlanningConstraint.proxyTypeEquiv H S A)]
  simp
  ring

private theorem divided_sum_rearrangement (α : ℝ) (p : A → S → ℝ)
    (u : A → ℝ) (t : A → S → ℝ) :
    (∑ a, ∑ s, p a s / α * u a * t a s) =
      α⁻¹ * (∑ a, ∑ s, u a * p a s * t a s) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The polynomial system has exactly the numerical meaning displayed in Appendix E. -/
theorem polynomialSatisfaction_iff (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) (W : PlanningWitness H S A) :
    polynomialSatisfaction r c p α τ target s₀ W.assignment ↔
      PlanningConditions r c p α τ target s₀ W := by
  have hrisk (h : Fin H) (s : S) :
      MvPolynomial.eval₂ (Rat.castHom ℝ) W.assignment
          (planningPolynomial r c p α τ target s₀ (.riskStep h s)) =
        W.risk h.castSucc s - (W.threshold h s + (α : ℝ)⁻¹ *
          (∑ a, ∑ t, W.policy h s a * (p s a t : ℝ) * W.positive h s a t)) := by
    simp only [planningPolynomial, eval₂_sub, eval₂_X, eval₂_sum, eval₂_mul,
      eval₂_C, Rat.coe_castHom, Rat.cast_div, PlanningWitness.assignment]
    rw [divided_sum_rearrangement]
    ring
  constructor
  · intro hk
    have hsimple := hk
    simp only [polynomialSatisfaction] at hsimple
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h s a
      simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment]
        using hsimple (.policyNonneg h s a)
    · intro h s
      simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment,
        sub_eq_zero] using hsimple (.policyTotal h s)
    · intro s
      simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment]
        using hsimple (.terminalReward s)
    · intro s
      simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment]
        using hsimple (.terminalRisk s)
    · intro h s
      simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment,
        sub_eq_zero] using hsimple (.rewardStep h s)
    · intro h s a t
      simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment]
        using hsimple (.positiveNonneg h s a t)
    · intro h s a t
      have hh := hsimple (.positiveGap h s a t)
      simp [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment] at hh
      linarith
    · intro h s
      have hh := hsimple (.riskStep h s)
      simp only [PlanningConstraint.isEquality, Bool.false_eq_true, ↓reduceIte] at hh
      rw [hrisk] at hh
      exact sub_nonneg.1 hh
    · simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment,
        sub_nonneg] using hsimple .budget
    · simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment,
        sub_nonneg] using hsimple .target
  · intro hW k
    cases k with
    | policyNonneg h s a =>
      simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment]
        using hW.policy_nonneg h s a
    | policyTotal h s =>
      simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment,
        sub_eq_zero] using hW.policy_total h s
    | terminalReward s =>
      simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment]
        using hW.terminal_reward s
    | terminalRisk s =>
      simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment]
        using hW.terminal_risk s
    | rewardStep h s =>
      simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment,
        sub_eq_zero] using hW.reward_step h s
    | positiveNonneg h s a t =>
      simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment]
        using hW.positive_nonneg h s a t
    | positiveGap h s a t =>
      have hh := hW.positive_gap h s a t
      simp [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment]
      linarith
    | riskStep h s =>
      simp only [PlanningConstraint.isEquality, Bool.false_eq_true, ↓reduceIte]
      rw [hrisk]
      exact sub_nonneg.2 (hW.risk_step h s)
    | budget =>
      simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment,
        sub_nonneg] using hW.budget
    | target =>
      simpa [planningPolynomial, PlanningConstraint.isEquality, PlanningWitness.assignment,
        sub_nonneg] using hW.target

/-! ## The two affine pieces used by the restricted NP certificate -/

/-- A piece-domain inequality is linear in the one-stage action probability. -/
def activePiece (α y : ℝ) (upper : Bool) : Prop :=
  if upper then α ≤ y else y ≤ α

/-- On either active domain the tail formula is affine. -/
def affineTailPiece (α y : ℝ) (upper : Bool) : ℝ :=
  if upper then 1 else y / α

theorem tail_eq_active_piece {α y : ℝ} (ha : 0 < α) (b : Bool)
    (hb : activePiece α y b) : bernoulliTail α y = affineTailPiece α y b := by
  cases b with
  | false => exact min_eq_left ((div_le_one ha).2 hb)
  | true => exact min_eq_right ((one_le_div ha).2 hb)

theorem exists_active_piece (α y : ℝ) : ∃ b : Bool, activePiece α y b := by
  rcases le_total y α with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

/-- Which action is more costly is determined entirely by the rational input data. -/
def expensiveProbability (d₀ d₁ x : ℝ) : ℝ := if d₀ ≤ d₁ then x else 1-x

/-- The one-state two-action CVaR formula in Appendix E, with both cost orders. -/
def twoActionRisk (α d₀ d₁ x : ℝ) : ℝ :=
  min d₀ d₁ + |d₁-d₀| * bernoulliTail α (expensiveProbability d₀ d₁ x)

def affineRiskPiece (α d₀ d₁ x : ℝ) (upper : Bool) : ℝ :=
  min d₀ d₁ + |d₁-d₀| * affineTailPiece α (expensiveProbability d₀ d₁ x) upper

theorem twoActionRisk_eq_of_le {α d₀ d₁ x : ℝ} (h : d₀ ≤ d₁) :
    twoActionRisk α d₀ d₁ x = d₀ + (d₁-d₀) * min (x/α) 1 := by
  simp [twoActionRisk, expensiveProbability, h,
    abs_of_nonneg (sub_nonneg.2 h), bernoulliTail]

theorem twoActionRisk_eq_of_ge {α d₀ d₁ x : ℝ} (h : d₁ ≤ d₀) :
    twoActionRisk α d₀ d₁ x = d₁ + (d₀-d₁) * min ((1-x)/α) 1 := by
  by_cases he : d₀ = d₁
  · simp [he, twoActionRisk]
  · have hn : ¬ d₀ ≤ d₁ := fun hh => he (le_antisymm hh h)
    simp [twoActionRisk, expensiveProbability, hn, min_eq_right h,
      abs_of_nonpos (sub_nonpos.2 h), bernoulliTail, neg_sub]

/-- Once the active pieces are guessed, the risk constraint is the sum of affine
functions, with the explicit linear piece-domain inequalities. -/
theorem one_state_piece_certificate {ι : Type*} [Fintype ι]
    (α : ℝ) (ha : 0 < α) (d₀ d₁ x : ι → ℝ) (τ : ℝ) :
    (∑ i, twoActionRisk α (d₀ i) (d₁ i) (x i)) ≤ τ ↔
      ∃ b : ι → Bool,
        (∀ i, activePiece α (expensiveProbability (d₀ i) (d₁ i) (x i)) (b i)) ∧
        (∑ i, affineRiskPiece α (d₀ i) (d₁ i) (x i) (b i)) ≤ τ := by
  constructor
  · intro hr
    have he : ∀ i, ∃ b : Bool, activePiece α (expensiveProbability (d₀ i) (d₁ i) (x i)) b :=
      fun i => exists_active_piece _ _
    choose b hb using he
    refine ⟨b, hb, ?_⟩
    convert hr using 1
    apply Finset.sum_congr rfl
    intro i _
    unfold affineRiskPiece twoActionRisk
    rw [tail_eq_active_piece ha (b i) (hb i)]
  · rintro ⟨b, hb, hr⟩
    convert hr using 1
    apply Finset.sum_congr rfl
    intro i _
    unfold affineRiskPiece twoActionRisk
    rw [tail_eq_active_piece ha (b i) (hb i)]


/-! ## Binary size of the rational data in the Subset-Sum construction -/

/-- Binary numerator/denominator payload, with a delimiter/sign allowance. -/
def fractionPayloadBits (a d : ℕ) : ℕ := a.size + d.size + 2

/-- A source length accounting for each positive integer and the target. -/
def subsetInputBits {ι : Type*} [Fintype ι] (w : ι → ℕ) (B : ℕ) : ℕ :=
  B.size + 1 + ∑ i, ((w i).size + 1)

private theorem size_add_bound (a b : ℕ) : (a+b).size ≤ a.size + b.size + 1 := by
  apply Nat.size_le.2
  have ha : a < 2 ^ (a.size + b.size) :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hb : b < 2 ^ (a.size + b.size) :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.pow_succ]
  omega

theorem sum_weight_size_bound {ι : Type*} [DecidableEq ι] (w : ι → ℕ) (s : Finset ι) :
    (∑ i ∈ s, w i).size ≤ ∑ i ∈ s, ((w i).size + 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have h := size_add_bound (w i) (∑ j ∈ s, w j)
    omega

/-- All unreduced rational pairs (wᵢ,C) and (B,C) have linear bit length in
the original Subset-Sum input, despite the potentially large numeric value C. -/
theorem normalized_fraction_payload_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℕ) (B : ℕ) :
    (∀ i, fractionPayloadBits (w i) (∑ j, w j) ≤ 2 * subsetInputBits w B + 2) ∧
      fractionPayloadBits B (∑ j, w j) ≤ 2 * subsetInputBits w B + 2 := by
  have hC := sum_weight_size_bound w Finset.univ
  have hB : B.size ≤ subsetInputBits w B := by unfold subsetInputBits; omega
  have hi (i : ι) : (w i).size ≤ subsetInputBits w B := by
    have h := Finset.single_le_sum (f := fun j => (w j).size + 1)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    change (w i).size + 1 ≤ ∑ j, ((w j).size + 1) at h
    unfold subsetInputBits
    omega
  constructor
  · intro i
    unfold fractionPayloadBits subsetInputBits at *
    have hh := hi i
    omega
  · unfold fractionPayloadBits subsetInputBits at *
    omega

/-- Repeating these pairs for the reward/cost arrays still has quadratic payload
size. This makes explicit the encoding-size part of the finite reduction. -/
theorem reduction_payload_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℕ) (B : ℕ) :
    (∑ i, 4 * fractionPayloadBits (w i) (∑ j, w j)) +
      2 * fractionPayloadBits B (∑ j, w j) ≤
      12 * (subsetInputBits w B + 1)^2 := by
  let L := subsetInputBits w B
  have hb := normalized_fraction_payload_bound w B
  have hn : Fintype.card ι ≤ L := by
    have h := Finset.sum_le_sum (s := Finset.univ) (f := fun _ : ι => 1)
      (g := fun i => (w i).size + 1) (fun i _ => Nat.succ_le_succ (Nat.zero_le _))
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
    dsimp [L, subsetInputBits]
    omega
  have hs : (∑ i, 4 * fractionPayloadBits (w i) (∑ j, w j)) ≤
      Fintype.card ι * (4 * (2*L+2)) := by
    calc
      _ ≤ ∑ _i : ι, 4 * (2*L+2) := Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left 4 (hb.1 i))
      _ = _ := by simp [Finset.sum_const]
  have ht : 2 * fractionPayloadBits B (∑ j, w j) ≤ 2*(2*L+2) := Nat.mul_le_mul_left 2 hb.2
  have hnprod := Nat.mul_le_mul_right (4 * (2*L+2)) hn
  change _ ≤ 12 * (L+1)^2
  nlinarith

/-! ## Exactness of the epigraph witnesses for the source Markov model -/

open Set Paper36.Regularity Paper36.Nested

/-- Convert finite rational stage data into the natural-stage representation of
`Nested`. Values after the horizon are zero and never enter the target query. -/
def realStages (f : Fin H → S → A → ℚ) (h : ℕ) (s : S) (a : A) : ℝ :=
  if hh : h < H then (f ⟨h, hh⟩ s a : ℝ) else 0

omit [Fintype S] [Fintype A] in
@[simp] theorem realStages_at (f : Fin H → S → A → ℚ) (h : Fin H) (s : S) (a : A) :
    realStages f h s a = (f h s a : ℝ) := by
  simp [realStages, h.isLt]

omit [Fintype S] [Fintype A] in
theorem realStages_bounds (c : Fin H → S → A → ℚ)
    (hc : ∀ h s a, (c h s a : ℝ) ∈ Icc 0 1) :
    ∀ h s a, realStages c h s a ∈ Icc 0 1 := by
  intro h s a
  unfold realStages
  split_ifs with hh
  · exact hc _ _ _
  · exact ⟨le_rfl, zero_le_one⟩

private theorem compact_le_objective (α B : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (hB : 0 ≤ B) (P : Regularity.Law S) (X : S → ℝ)
    (hX : ∀ i, X i ∈ Icc 0 B) (z : ℝ) :
    compactCVaR α B P X ≤ objective α P X z := by
  by_cases hz : z < 0
  · exact (compactCVaR_le α B hB P X ⟨le_rfl, hB⟩).trans
      (objective_below_zero α ha ha1 P X (fun i => (hX i).1) hz.le)
  · by_cases hzB : B < z
    · exact (compactCVaR_le α B hB P X ⟨hB, le_rfl⟩).trans
        (objective_above_bound α B P X (fun i => (hX i).2) hzB.le)
    · exact compactCVaR_le α B hB P X ⟨le_of_not_gt hz, le_of_not_gt hzB⟩

/-- Positive-part variables in (E.3) majorize the actual positive parts. -/
theorem positive_part_le_witness (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) (W : PlanningWitness H S A)
    (hW : PlanningConditions r c p α τ target s₀ W) (h : Fin H) (s : S) (a : A) (t : S) :
    max ((c h s a : ℝ) + W.risk h.succ t - W.threshold h s) 0 ≤ W.positive h s a t :=
  max_le (hW.positive_gap h s a t) (hW.positive_nonneg h s a t)

/-- Backward induction for the reward equations (E.2). -/
theorem witness_reward_eq (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) (W : PlanningWitness H S A)
    (hW : PlanningConditions r c p α τ target s₀ W)
    (π : Nested.Policy S A) (q : Nested.Kernel S A)
    (hπ : ∀ h : Fin H, ∀ s a, π h s a = W.policy h s a)
    (hq : ∀ s a t, q s a t = (p s a t : ℝ))
    (n h : ℕ) (hnh : h + n = H) (s : S) :
    Nested.reward (realStages r) π q n h s = W.reward ⟨h, by omega⟩ s := by
  induction n generalizing h s with
  | zero =>
    have hh : h = H := by omega
    subst h
    simpa [Nested.reward] using (hW.terminal_reward s).symm
  | succ n ih =>
    have hh : h < H := by omega
    rw [Nested.reward]
    have hfin : (⟨h, by omega⟩ : Fin (H+1)) = (⟨h, hh⟩ : Fin H).castSucc := by
      apply Fin.ext
      rfl
    rw [hfin, hW.reward_step]
    apply Finset.sum_congr rfl
    intro a _
    rw [hπ ⟨h, hh⟩ s a]
    have hr : realStages r h s a = (r ⟨h, hh⟩ s a : ℝ) := by simp [realStages, hh]
    rw [hr]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [hq, ih (h + 1) (by omega) t]
    rfl

/-- Soundness of (E.3)--(E.4): no epigraph witness can understate nested risk. -/
theorem witness_risk_dominates (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) (W : PlanningWitness H S A)
    (hW : PlanningConditions r c p α τ target s₀ W)
    (ha : 0 < (α : ℝ)) (ha1 : (α : ℝ) ≤ 1)
    (hc : ∀ h s a, (c h s a : ℝ) ∈ Icc 0 1)
    (π : Nested.Policy S A) (q : Nested.Kernel S A)
    (hπ : ∀ h : Fin H, ∀ s a, π h s a = W.policy h s a)
    (hq : ∀ s a t, q s a t = (p s a t : ℝ))
    (n h : ℕ) (hnh : h + n = H) (s : S) :
    Nested.risk (α : ℝ) (realStages c) π q n h s ≤ W.risk ⟨h, by omega⟩ s := by
  induction n generalizing h s with
  | zero =>
    have hh : h = H := by omega
    subst h
    simpa [Nested.risk] using (hW.terminal_risk s).symm.le
  | succ n ih =>
    have hh : h < H := by omega
    let h' : Fin H := ⟨h, hh⟩
    let P := Nested.joint (π h s) (q s)
    let X : A × S → ℝ := fun x => realStages c h s x.1 +
      Nested.risk (α : ℝ) (realStages c) π q n (h + 1) x.2
    have hX : ∀ x, X x ∈ Icc (0 : ℝ) ((n + 1 : ℕ) : ℝ) := by
      intro x
      have hr := Nested.risk_bounds (α : ℝ) ha.le _ (realStages_bounds c hc) π q n (h+1) x.2
      have hcost := realStages_bounds c hc h s x.1
      dsimp [X]
      constructor <;> push_cast <;> linarith [hr.1, hr.2, hcost.1, hcost.2]
    have hpart : ∀ x : A × S, max (X x - W.threshold h' s) 0 ≤ W.positive h' s x.1 x.2 := by
      intro x
      apply max_le _ (hW.positive_nonneg h' s x.1 x.2)
      have hi := ih (h+1) (by omega) x.2
      have hg := hW.positive_gap h' s x.1 x.2
      have hcost : realStages c h s x.1 = (c h' s x.1 : ℝ) := by simp [realStages, hh, h']
      dsimp [X]
      rw [hcost]
      change _ ≤ W.risk h'.succ x.2 at hi
      linarith
    calc
      Nested.risk (α : ℝ) (realStages c) π q (n+1) h s = compactCVaR (α : ℝ) (n+1 : ℕ) P X := rfl
      _ ≤ objective (α : ℝ) P X (W.threshold h' s) :=
        compact_le_objective (α : ℝ) _ ha ha1 (by positivity) P X hX _
      _ ≤ W.threshold h' s + (α : ℝ)⁻¹ *
          (∑ a, ∑ t, W.policy h' s a * (p s a t : ℝ) * W.positive h' s a t) := by
        unfold objective
        apply add_le_add_left
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 ha.le)
        calc
          expectation P (fun x => max (X x - W.threshold h' s) 0) ≤
              expectation P (fun x => W.positive h' s x.1 x.2) := expectation_mono P hpart
          _ = _ := by
            change (∑ x : A × S, (π h s x.1 * q s x.1 x.2) * W.positive h' s x.1 x.2) = _
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro t _
            have hpa : π h s a = W.policy h' s a := hπ h' s a
            rw [hpa, hq]
      _ ≤ W.risk h'.castSucc s := hW.risk_step h' s

/-- With a fixed actual Markov policy, numerical feasibility implies the source target query. -/
theorem witness_implies_feasible (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) (W : PlanningWitness H S A)
    (hW : PlanningConditions r c p α τ target s₀ W)
    (ha : 0 < (α : ℝ)) (ha1 : (α : ℝ) ≤ 1)
    (hc : ∀ h s a, (c h s a : ℝ) ∈ Icc 0 1)
    (π : Nested.Policy S A) (q : Nested.Kernel S A)
    (hπ : ∀ h : Fin H, ∀ s a, π h s a = W.policy h s a)
    (hq : ∀ s a t, q s a t = (p s a t : ℝ)) :
    Nested.risk (α : ℝ) (realStages c) π q H 0 s₀ ≤ (τ : ℝ) ∧
      (target : ℝ) ≤ Nested.reward (realStages r) π q H 0 s₀ := by
  constructor
  · exact (witness_risk_dominates r c p α τ target s₀ W hW ha ha1 hc π q hπ hq H 0 (by omega) s₀).trans hW.budget
  · rw [witness_reward_eq r c p α τ target s₀ W hW π q hπ hq H 0 (by omega) s₀]
    exact hW.target

/-- A feasible actual policy supplies exact values, optimizing thresholds and exact
positive parts, as asserted in Appendix E. -/
theorem feasible_implies_witness (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S)
    (π : Nested.Policy S A) (q : Nested.Kernel S A)
    (hq : ∀ s a t, q s a t = (p s a t : ℝ))
    (hf : Nested.risk (α : ℝ) (realStages c) π q H 0 s₀ ≤ (τ : ℝ) ∧
      (target : ℝ) ≤ Nested.reward (realStages r) π q H 0 s₀) :
    ∃ W : PlanningWitness H S A, PlanningConditions r c p α τ target s₀ W ∧
      ∀ h : Fin H, ∀ s a, π h s a = W.policy h s a := by
  let V : Fin (H+1) → S → ℝ := fun h s =>
    Nested.reward (realStages r) π q (H-h.val) h.val s
  let R : Fin (H+1) → S → ℝ := fun h s =>
    Nested.risk (α : ℝ) (realStages c) π q (H-h.val) h.val s
  have hstep (h : Fin H) (s : S) : R h.castSucc s =
      compactCVaR (α : ℝ) (H-h.val : ℕ) (Nested.joint (π h s) (q s))
        (fun x => (c h s x.1 : ℝ) + R h.succ x.2) := by
    have hn : H - h.val = (H - (h.val+1)) + 1 := by omega
    dsimp [R]
    rw [hn, Nested.risk]
    simp [realStages, h.isLt]
  have hmin : ∀ (h : Fin H) (s : S), ∃ z : ℝ,
      R h.castSucc s = objective (α : ℝ) (Nested.joint (π h s) (q s))
        (fun x => (c h s x.1 : ℝ) + R h.succ x.2) z := by
    intro h s
    obtain ⟨z, _, he⟩ := exists_compact_minimizer (α : ℝ) (H-h.val : ℕ)
      (by positivity) (Nested.joint (π h s) (q s)) (fun x => (c h s x.1 : ℝ) + R h.succ x.2)
    exact ⟨z, (hstep h s).trans he⟩
  choose z hz using hmin
  let W : PlanningWitness H S A :=
    { policy := fun h s a => π h s a
      reward := V
      risk := R
      threshold := z
      positive := fun h s a t => max ((c h s a : ℝ) + R h.succ t - z h s) 0 }
  refine ⟨W, ?_, fun _ _ _ => rfl⟩
  constructor
  · intro h s a
    exact (π h s).property.1 a
  · intro h s
    exact (π h s).property.2
  · intro s
    simp [W, V, Nested.reward]
  · intro s
    simp [W, R, Nested.risk]
  · intro h s
    change V h.castSucc s = _
    have hn : H - h.val = (H - (h.val+1)) + 1 := by omega
    dsimp [V, W]
    rw [hn, Nested.reward]
    simp [realStages, h.isLt, hq]
  · intro h s a t
    exact le_max_right _ _
  · intro h s a t
    exact le_max_left _ _
  · intro h s
    change z h s + (α : ℝ)⁻¹ *
      (∑ a, ∑ t, π h s a * (p s a t : ℝ) * max ((c h s a : ℝ) + R h.succ t - z h s) 0) ≤ R h.castSucc s
    rw [hz h s]
    apply le_of_eq
    change z h s + (α : ℝ)⁻¹ * (∑ a, ∑ t,
      π h s a * (p s a t : ℝ) * max ((c h s a : ℝ) + R h.succ t - z h s) 0) =
        z h s + (α : ℝ)⁻¹ * (∑ x : A × S,
          (π h s x.1 * q s x.1 x.2) * max ((c h s x.1 : ℝ) + R h.succ x.2 - z h s) 0)
    rw [Fintype.sum_prod_type]
    simp only [hq]
  · exact hf.1
  · exact hf.2

/-- A witness's simplex coordinates extend to a physical-state Markov policy. -/
def policyOfWitness [Nonempty A] (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) (W : PlanningWitness H S A)
    (hW : PlanningConditions r c p α τ target s₀ W) : Nested.Policy S A :=
  fun n s => if hn : n < H then
    ⟨W.policy ⟨n, hn⟩ s, hW.policy_nonneg ⟨n, hn⟩ s, hW.policy_total ⟨n, hn⟩ s⟩
  else Nested.pure (Classical.arbitrary A)

@[simp] theorem policyOfWitness_at [Nonempty A] (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) (W : PlanningWitness H S A)
    (hW : PlanningConditions r c p α τ target s₀ W) (h : Fin H) (s : S) (a : A) :
    policyOfWitness r c p α τ target s₀ W hW h s a = W.policy h s a := by
  simp only [policyOfWitness, dif_pos h.isLt]
  rfl

/-- Exact existential equivalence of the actual Markov planning query and the
finite E.2--E.5 witness system. -/
theorem planning_epigraph_exact [Nonempty A]
    (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S)
    (ha : 0 < (α : ℝ)) (ha1 : (α : ℝ) ≤ 1)
    (hc : ∀ h s a, (c h s a : ℝ) ∈ Icc 0 1)
    (q : Nested.Kernel S A) (hq : ∀ s a t, q s a t = (p s a t : ℝ)) :
    (∃ W : PlanningWitness H S A, PlanningConditions r c p α τ target s₀ W) ↔
      ∃ π : Nested.Policy S A,
        Nested.risk (α : ℝ) (realStages c) π q H 0 s₀ ≤ (τ : ℝ) ∧
        (target : ℝ) ≤ Nested.reward (realStages r) π q H 0 s₀ := by
  constructor
  · rintro ⟨W, hW⟩
    exact ⟨policyOfWitness r c p α τ target s₀ W hW,
      witness_implies_feasible r c p α τ target s₀ W hW ha ha1 hc _ q
        (policyOfWitness_at r c p α τ target s₀ W hW) hq⟩
  · rintro ⟨π, hf⟩
    obtain ⟨W, hW, _⟩ := feasible_implies_witness r c p α τ target s₀ π q hq hf
    exact ⟨W, hW⟩

def PlanningWitness.ofAssignment (x : PlanningVar H S A → ℝ) : PlanningWitness H S A where
  policy h s a := x (.policy h s a)
  reward h s := x (.reward h s)
  risk h s := x (.risk h s)
  threshold h s := x (.threshold h s)
  positive h s a t := x (.positive h s a t)

omit [Fintype S] [Fintype A] in
@[simp] theorem assignment_ofAssignment (x : PlanningVar H S A → ℝ) :
    (PlanningWitness.ofAssignment x).assignment = x := by
  funext v
  cases v <;> rfl

/-- The complete rational quadratic system is feasible exactly for feasible
randomized physical-state Markov planning targets. -/
theorem planning_polynomial_exact [Nonempty A]
    (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S)
    (ha : 0 < (α : ℝ)) (ha1 : (α : ℝ) ≤ 1)
    (hc : ∀ h s a, (c h s a : ℝ) ∈ Icc 0 1)
    (q : Nested.Kernel S A) (hq : ∀ s a t, q s a t = (p s a t : ℝ)) :
    (∃ x : PlanningVar H S A → ℝ, polynomialSatisfaction r c p α τ target s₀ x) ↔
      ∃ π : Nested.Policy S A,
        Nested.risk (α : ℝ) (realStages c) π q H 0 s₀ ≤ (τ : ℝ) ∧
        (target : ℝ) ≤ Nested.reward (realStages r) π q H 0 s₀ := by
  rw [← planning_epigraph_exact r c p α τ target s₀ ha ha1 hc q hq]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨PlanningWitness.ofAssignment x,
      (polynomialSatisfaction_iff r c p α τ target s₀ _).1 (by simpa using hx)⟩
  · rintro ⟨W, hW⟩
    exact ⟨W.assignment, (polynomialSatisfaction_iff r c p α τ target s₀ W).2 hW⟩

/-- Definition 6.1's rational input, with an explicit finite table for each
stage and the stochastic-kernel equations as input validity conditions. -/
structure RationalPlanningInput (S A : Type*) [Fintype S] [Fintype A] where
  horizon : ℕ
  transition : S → A → S → ℚ
  transition_nonneg : ∀ s a t, 0 ≤ transition s a t
  transition_total : ∀ s a, ∑ t, transition s a t = 1
  reward : Fin horizon → S → A → ℚ
  cost : Fin horizon → S → A → ℚ
  cost_bounds : ∀ h s a, (cost h s a : ℝ) ∈ Icc 0 1
  tailMass : ℚ
  tailMass_pos : 0 < tailMass
  tailMass_le_one : tailMass ≤ 1
  budget : ℚ
  target : ℚ
  initial : S

def RationalPlanningInput.kernel (I : RationalPlanningInput S A) : Nested.Kernel S A :=
  fun s a => ⟨fun t => (I.transition s a t : ℝ),
    (fun t => by
      change 0 ≤ (I.transition s a t : ℝ)
      exact_mod_cast I.transition_nonneg s a t),
    (by
      change (∑ t, (I.transition s a t : ℝ)) = 1
      exact_mod_cast I.transition_total s a)⟩

@[simp] theorem RationalPlanningInput.kernel_apply (I : RationalPlanningInput S A) (s : S) (a : A) (t : S) :
    I.kernel s a t = (I.transition s a t : ℝ) := by
  rfl

/-- The source decision query quantifies over the full randomized physical-state
Markov class. It does not assume that a solution is deterministic. -/
def RationalPlanningInput.Feasible (I : RationalPlanningInput S A) : Prop :=
  ∃ π : Nested.Policy S A,
    Nested.risk (I.tailMass : ℝ) (realStages I.cost) π I.kernel I.horizon 0 I.initial ≤ (I.budget : ℝ) ∧
    (I.target : ℝ) ≤ Nested.reward (realStages I.reward) π I.kernel I.horizon 0 I.initial

/-- Exact degree-two existential-real encoding of Definition 6.1. -/
theorem rational_planning_encoding_exact [Nonempty A] (I : RationalPlanningInput S A) :
    (∃ x : PlanningVar I.horizon S A → ℝ,
      polynomialSatisfaction I.reward I.cost I.transition I.tailMass I.budget I.target I.initial x) ↔
      I.Feasible := by
  exact planning_polynomial_exact I.reward I.cost I.transition I.tailMass I.budget I.target I.initial
    (by exact_mod_cast I.tailMass_pos) (by exact_mod_cast I.tailMass_le_one)
    I.cost_bounds I.kernel (RationalPlanningInput.kernel_apply I)

/-! ## The Subset-Sum formulas are actual one-state nested CVaR values -/

/-- One state, two actions, and deterministic self-loop, exactly as in Appendix E. -/
def oneStateKernel : Nested.Kernel Unit Bool := fun _ _ => Nested.pure ()

def takeSkipCost (d : ℕ → ℝ) (h : ℕ) (_ : Unit) (a : Bool) : ℝ :=
  if a then d h else 0

theorem takeSkipCost_bounds (d : ℕ → ℝ) (hd : ∀ h, d h ∈ Icc 0 1) :
    ∀ h s a, takeSkipCost d h s a ∈ Icc 0 1 := by
  intro h s a
  cases a <;> simp [takeSkipCost, hd h]

@[simp] theorem oneStateKernel_apply (s t : Unit) (a : Bool) : oneStateKernel s a t = 1 := by
  cases s
  cases t
  have ht := (oneStateKernel () a).property.2
  change (∑ x : Unit, oneStateKernel () a x) = 1 at ht
  simpa only [Fintype.sum_unique] using ht

/-- Single-step identity behind (E.1), including randomized actions inside CVaR. -/
theorem one_state_risk_step (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (d : ℕ → ℝ) (hd : ∀ h, d h ∈ Icc 0 1)
    (π : Nested.Policy Unit Bool) (n h : ℕ) :
    Nested.risk α (takeSkipCost d) π oneStateKernel (n+1) h () =
      d h * bernoulliTail α (π h () true) +
        Nested.risk α (takeSkipCost d) π oneStateKernel n (h+1) () := by
  rw [Nested.risk_step_eq_primal α ha ha1 _ (takeSkipCost_bounds d hd)]
  rw [← RiskBridge.value_eq_regular α ha ha1]
  let P := RiskBridge.ofRegular (Nested.joint (π h ()) (oneStateKernel ()))
  have he : (fun x : Bool × Unit => takeSkipCost d h () x.1 +
      Nested.risk α (takeSkipCost d) π oneStateKernel n (h+1) x.2) =
      (fun x : Bool × Unit => (if x.1 = true then d h else 0) +
        Nested.risk α (takeSkipCost d) π oneStateKernel n (h+1) ()) := by
    funext x
    rcases x with ⟨a, t⟩
    cases t
    cases a <;> rfl
  rw [he, CVaR.value_add_const _ ha ha1]
  rw [CVaR.value_indicator _ ha ha1 (hd h).1 (fun x : Bool × Unit => x.1 = true)]
  have hp : (∑ x : Bool × Unit,
      if x.1 = true then P.mass x else 0) = π h () true := by
    change (∑ x : Bool × Unit, if x.1 = true then π h () x.1 * oneStateKernel () x.1 x.2 else 0) = _
    simp [Fintype.sum_prod_type]
  change d h * min ((∑ x : Bool × Unit, if x.1 = true then P.mass x else 0)/α) 1 + _ = _
  rw [hp]
  rfl

/-- Equation (E.1) for nested risk, before normalizing the weights. -/
theorem one_state_risk_sum (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (d : ℕ → ℝ) (hd : ∀ h, d h ∈ Icc 0 1)
    (π : Nested.Policy Unit Bool) (n h : ℕ) :
    Nested.risk α (takeSkipCost d) π oneStateKernel n h () =
      ∑ i ∈ Finset.range n, d (h+i) * bernoulliTail α (π (h+i) () true) := by
  induction n generalizing h with
  | zero => simp [Nested.risk]
  | succ n ih =>
    rw [one_state_risk_step α ha ha1 d hd π, ih, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have he : h + 1 + i = h + (i + 1) := by omega
    rw [he]

/-- Equation (E.1) for ordinary expected rewards. -/
theorem one_state_reward_sum (d : ℕ → ℝ) (π : Nested.Policy Unit Bool) (n h : ℕ) :
    Nested.reward (takeSkipCost d) π oneStateKernel n h () =
      ∑ i ∈ Finset.range n, d (h+i) * π (h+i) () true := by
  induction n generalizing h with
  | zero => simp [Nested.reward]
  | succ n ih =>
    have ht : π h () true + π h () false = 1 := by
      simpa only [Fintype.sum_bool] using (π h ()).property.2
    rw [Nested.reward]
    simp only [Fintype.sum_bool, takeSkipCost, Bool.false_eq_true, ↓reduceIte,
      oneStateKernel_apply, Fintype.sum_unique, one_mul, zero_add, ih]
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have he : (∑ i ∈ Finset.range n, d (h+1+i) * π (h+1+i) () true) =
      ∑ i ∈ Finset.range n, d (h+(i+1)) * π (h+(i+1)) () true := by
      apply Finset.sum_congr rfl
      intro i _
      have he : h + 1 + i = h + (i + 1) := by omega
      rw [he]
    rw [he]
    have hm := congrArg (fun z : ℝ => z * (∑ i ∈ Finset.range n, d (h+(i+1)) * π (h+(i+1)) () true)) ht
    nlinarith [hm]

/-- The Bernoulli law of any real take probability in [0,1]. -/
def bernoulliLaw (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : Regularity.Law Bool :=
  ⟨fun a => if a then x else 1-x,
    (by intro a; cases a <;> dsimp <;> linarith),
    (by change (∑ a : Bool, if a then x else 1-x) = 1
        rw [Fintype.sum_bool]
        simp)⟩

@[simp] theorem bernoulliLaw_true (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    bernoulliLaw x hx hx1 true = x := rfl

def bernoulliPolicy (x : Fin H → ℝ) (hx : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    Nested.Policy Unit Bool := fun h _ =>
  if hh : h < H then bernoulliLaw (x ⟨h,hh⟩) (hx ⟨h,hh⟩) (hx1 ⟨h,hh⟩)
  else bernoulliLaw 0 le_rfl zero_le_one

@[simp] theorem bernoulliPolicy_at (x : Fin H → ℝ) (hx : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (i : Fin H) : bernoulliPolicy x hx hx1 i () true = x i := by
  simp only [bernoulliPolicy, dif_pos i.isLt, bernoulliLaw_true]

theorem bool_probability_bounds (P : Regularity.Law Bool) (a : Bool) : 0 ≤ P a ∧ P a ≤ 1 := by
  constructor
  · exact P.property.1 a
  · have htotal := P.property.2
    rw [Fintype.sum_bool] at htotal
    have ht := P.property.1 true
    have hf := P.property.1 false
    change P true + P false = 1 at htotal
    change 0 ≤ P true at ht
    change 0 ≤ P false at hf
    cases a <;> linarith

/-- The finite normalized weights, extended by zero beyond the horizon. -/
def normalizedStages (w : Fin H → ℕ) (C : ℝ) (h : ℕ) : ℝ :=
  if hh : h < H then (w ⟨h,hh⟩ : ℝ)/C else 0

@[simp] theorem normalizedStages_at (w : Fin H → ℕ) (C : ℝ) (h : Fin H) :
    normalizedStages w C h = (w h : ℝ)/C := by simp [normalizedStages, h.isLt]

theorem normalizedStages_bounds (w : Fin H → ℕ) {C : ℝ} (hC : 0 < C)
    (htot : C = ∑ i, (w i : ℝ)) : ∀ h, normalizedStages w C h ∈ Icc 0 1 := by
  intro h
  unfold normalizedStages
  split_ifs with hh
  · exact normalized_weight_bounds w hC htot _
  · exact ⟨le_rfl, zero_le_one⟩

theorem normalized_risk_eq_reduced (w : Fin H → ℕ) {α C : ℝ}
    (ha : 0 < α) (ha1 : α ≤ 1) (hC : 0 < C) (htot : C = ∑ i, (w i : ℝ))
    (π : Nested.Policy Unit Bool) :
    Nested.risk α (takeSkipCost (normalizedStages w C)) π oneStateKernel H 0 () =
      reducedRisk α (fun i => (w i : ℝ)/C) (fun i : Fin H => π i () true) := by
  rw [one_state_risk_sum α ha ha1 _ (normalizedStages_bounds w hC htot),
    ← Fin.sum_univ_eq_sum_range]
  simp [reducedRisk]

theorem normalized_reward_eq_linear (w : Fin H → ℕ) (C : ℝ)
    (π : Nested.Policy Unit Bool) :
    Nested.reward (takeSkipCost (normalizedStages w C)) π oneStateKernel H 0 () =
      linearReward (fun i => (w i : ℝ)/C) (fun i : Fin H => π i () true) := by
  rw [one_state_reward_sum, ← Fin.sum_univ_eq_sum_range]
  simp [linearReward]

/-- The mathematical reduction is to the actual randomized Markov planner,
with its action randomness inside nested CVaR. Determinism is a conclusion. -/
theorem actual_one_state_subset_sum_reduction (w : Fin H → ℕ) (B : ℕ) {α C : ℝ}
    (ha : 0 < α) (ha1 : α < 1) (hw : ∀ i, 0 < w i)
    (hC : 0 < C) (htot : C = ∑ i, (w i : ℝ)) :
    (∃ π : Nested.Policy Unit Bool,
      Nested.risk α (takeSkipCost (normalizedStages w C)) π oneStateKernel H 0 () ≤ (B : ℝ)/C ∧
      (B : ℝ)/C ≤ Nested.reward (takeSkipCost (normalizedStages w C)) π oneStateKernel H 0 ()) ↔
      ∃ s : Finset (Fin H), ∑ i ∈ s, w i = B := by
  rw [← subset_sum_reduction w B ha ha1 hw hC]
  constructor
  · rintro ⟨π, hf⟩
    refine ⟨fun i => π i () true, ?_, ?_, ?_⟩
    · intro i
      exact (bool_probability_bounds (π i ()) true).1
    · intro i
      exact (bool_probability_bounds (π i ()) true).2
    · simpa only [normalized_risk_eq_reduced w ha ha1.le hC htot,
        normalized_reward_eq_linear] using hf
  · rintro ⟨x, hx, hx1, hf⟩
    refine ⟨bernoulliPolicy x hx hx1, ?_⟩
    simpa only [normalized_risk_eq_reduced w ha ha1.le hC htot,
      normalized_reward_eq_linear, bernoulliPolicy_at] using hf

/-- The known all-skip Markov policy is strictly feasible whenever the target is positive. -/
theorem actual_all_skip_strictly_feasible (w : Fin H → ℕ) (B : ℕ) {α C : ℝ}
    (ha : 0 < α) (ha1 : α ≤ 1) (hB : 0 < B)
    (hC : 0 < C) (htot : C = ∑ i, (w i : ℝ)) :
    Nested.risk α (takeSkipCost (normalizedStages w C))
      (bernoulliPolicy (fun _ : Fin H => 0) (fun _ => le_rfl) (fun _ => zero_le_one))
      oneStateKernel H 0 () < (B : ℝ)/C := by
  rw [normalized_risk_eq_reduced w ha ha1 hC htot]
  simp only [bernoulliPolicy_at]
  exact (all_skip_strictly_feasible _ (by exact_mod_cast hB) hC).2

/-- The second action probability determines the first one through the simplex equation. -/
theorem bool_probability_false (P : Regularity.Law Bool) : P false = 1 - P true := by
  have ht := P.property.2
  change (∑ a : Bool, P a) = 1 at ht
  rw [Fintype.sum_bool] at ht
  linarith

private theorem one_state_indicator (α d : ℝ) (ha : 0 < α) (ha1 : α ≤ 1) (hd : 0 ≤ d)
    (P : Regularity.Law Bool) (b : Bool) :
    CVaR.value (RiskBridge.ofRegular (Nested.joint P (oneStateKernel ()))) α
      (fun x : Bool × Unit => if x.1 = b then d else 0) = d * bernoulliTail α (P b) := by
  rw [CVaR.value_indicator _ ha ha1 hd (fun x : Bool × Unit => x.1 = b)]
  have hm : (∑ x : Bool × Unit, if x.1 = b then
      (RiskBridge.ofRegular (Nested.joint P (oneStateKernel ()))).mass x else 0) = P b := by
    change (∑ x : Bool × Unit, if x.1 = b then P x.1 * oneStateKernel () x.1 x.2 else 0) = _
    cases b <;> simp [Fintype.sum_prod_type]
  rw [hm]
  rfl

def twoActionCost (d₀ d₁ : ℕ → ℝ) (h : ℕ) (_ : Unit) (a : Bool) : ℝ :=
  if a then d₁ h else d₀ h

theorem twoActionCost_bounds (d₀ d₁ : ℕ → ℝ)
    (hd₀ : ∀ h, d₀ h ∈ Icc 0 1) (hd₁ : ∀ h, d₁ h ∈ Icc 0 1) :
    ∀ h s a, twoActionCost d₀ d₁ h s a ∈ Icc 0 1 := by
  intro h s a
  cases a <;> simp [twoActionCost, hd₀ h, hd₁ h]

/-- Both arbitrary two-action cost orders in Appendix E are actual nested-CVaR steps. -/
theorem one_state_two_action_step (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (d₀ d₁ : ℕ → ℝ) (hd₀ : ∀ h, d₀ h ∈ Icc 0 1) (hd₁ : ∀ h, d₁ h ∈ Icc 0 1)
    (π : Nested.Policy Unit Bool) (n h : ℕ) :
    Nested.risk α (twoActionCost d₀ d₁) π oneStateKernel (n+1) h () =
      twoActionRisk α (d₀ h) (d₁ h) (π h () true) +
        Nested.risk α (twoActionCost d₀ d₁) π oneStateKernel n (h+1) () := by
  rw [Nested.risk_step_eq_primal α ha ha1 _ (twoActionCost_bounds d₀ d₁ hd₀ hd₁)]
  rw [← RiskBridge.value_eq_regular α ha ha1]
  let R := Nested.risk α (twoActionCost d₀ d₁) π oneStateKernel n (h+1) ()
  by_cases hl : d₀ h ≤ d₁ h
  · have he : (fun x : Bool × Unit => twoActionCost d₀ d₁ h () x.1 +
        Nested.risk α (twoActionCost d₀ d₁) π oneStateKernel n (h+1) x.2) =
        (fun x => (if x.1 = true then d₁ h - d₀ h else 0) + (d₀ h + R)) := by
      funext x
      rcases x with ⟨a,t⟩
      cases t
      cases a <;> dsimp [twoActionCost, R] <;> ring
    rw [he, CVaR.value_add_const _ ha ha1,
      one_state_indicator α _ ha ha1 (sub_nonneg.2 hl), twoActionRisk_eq_of_le hl]
    unfold bernoulliTail
    dsimp [R]
    ring
  · have hl' : d₁ h ≤ d₀ h := le_of_not_ge hl
    have he : (fun x : Bool × Unit => twoActionCost d₀ d₁ h () x.1 +
        Nested.risk α (twoActionCost d₀ d₁) π oneStateKernel n (h+1) x.2) =
        (fun x => (if x.1 = false then d₀ h - d₁ h else 0) + (d₁ h + R)) := by
      funext x
      rcases x with ⟨a,t⟩
      cases t
      cases a <;> dsimp [twoActionCost, R] <;> ring
    rw [he, CVaR.value_add_const _ ha ha1,
      one_state_indicator α _ ha ha1 (sub_nonneg.2 hl'), twoActionRisk_eq_of_ge hl',
      bool_probability_false]
    unfold bernoulliTail
    dsimp [R]
    ring

theorem one_state_two_action_risk_sum (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (d₀ d₁ : ℕ → ℝ) (hd₀ : ∀ h, d₀ h ∈ Icc 0 1) (hd₁ : ∀ h, d₁ h ∈ Icc 0 1)
    (π : Nested.Policy Unit Bool) (n h : ℕ) :
    Nested.risk α (twoActionCost d₀ d₁) π oneStateKernel n h () =
      ∑ i ∈ Finset.range n, twoActionRisk α (d₀ (h+i)) (d₁ (h+i)) (π (h+i) () true) := by
  induction n generalizing h with
  | zero => simp [Nested.risk]
  | succ n ih =>
    rw [one_state_two_action_step α ha ha1 d₀ d₁ hd₀ hd₁ π, ih, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have he : h + 1 + i = h + (i+1) := by omega
    rw [he]

/-- The actual restricted planner's risk test has a certificate consisting of
H active pieces and their linear piece-domain/risk inequalities. -/
theorem actual_one_state_piece_certificate (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (d₀ d₁ : ℕ → ℝ) (hd₀ : ∀ h, d₀ h ∈ Icc 0 1) (hd₁ : ∀ h, d₁ h ∈ Icc 0 1)
    (π : Nested.Policy Unit Bool) (τ : ℝ) :
    Nested.risk α (twoActionCost d₀ d₁) π oneStateKernel H 0 () ≤ τ ↔
      ∃ b : Fin H → Bool,
        (∀ h : Fin H, activePiece α (expensiveProbability (d₀ h) (d₁ h) (π h () true)) (b h)) ∧
        (∑ h : Fin H, affineRiskPiece α (d₀ h) (d₁ h) (π h () true) (b h)) ≤ τ := by
  rw [one_state_two_action_risk_sum α ha ha1 d₀ d₁ hd₀ hd₁ π,
    ← Fin.sum_univ_eq_sum_range]
  simp only [Nat.zero_add]
  exact one_state_piece_certificate α ha _ _ _ τ

/-- Every chosen risk piece has rational affine coefficients for rational data. -/
theorem affineRiskPiece_rational (α d₀ d₁ : ℚ) (b : Bool) :
    ∃ intercept slope : ℚ, ∀ x : ℝ,
      affineRiskPiece (α : ℝ) (d₀ : ℝ) (d₁ : ℝ) x b = (intercept : ℝ) + (slope : ℝ) * x := by
  by_cases h : d₀ ≤ d₁
  · have hr : (d₀ : ℝ) ≤ (d₁ : ℝ) := by exact_mod_cast h
    cases b with
    | false =>
      refine ⟨d₀, (d₁-d₀)/α, ?_⟩
      intro x
      simp only [affineRiskPiece, min_eq_left hr, abs_of_nonneg (sub_nonneg.2 hr),
        expensiveProbability, if_pos hr, affineTailPiece, Bool.false_eq_true, ↓reduceIte]
      push_cast
      ring
    | true =>
      refine ⟨d₁, 0, ?_⟩
      intro x
      simp [affineRiskPiece, hr, abs_of_nonneg (sub_nonneg.2 hr), affineTailPiece]
  · have hr : (d₁ : ℝ) ≤ (d₀ : ℝ) := by exact_mod_cast (le_of_not_ge h)
    have hn : ¬ (d₀ : ℝ) ≤ (d₁ : ℝ) := by exact_mod_cast h
    cases b with
    | false =>
      refine ⟨d₁ + (d₀-d₁)/α, -(d₀-d₁)/α, ?_⟩
      intro x
      simp only [affineRiskPiece, min_eq_right hr, abs_of_nonpos (sub_nonpos.2 hr),
        expensiveProbability, if_neg hn, affineTailPiece, Bool.false_eq_true, ↓reduceIte]
      push_cast
      ring
    | true =>
      refine ⟨d₀, 0, ?_⟩
      intro x
      simp [affineRiskPiece, hr, abs_of_nonpos (sub_nonpos.2 hr), affineTailPiece]

/-- The concrete rational one-state instance produced from a Subset-Sum list. -/
def subsetSumPlanningInput (w : Fin H → ℕ) (B : ℕ) (α : ℚ)
    (ha : 0 < α) (ha1 : α < 1) (hC : 0 < ∑ i, w i) : RationalPlanningInput Unit Bool where
  horizon := H
  transition := fun _ _ _ => 1
  transition_nonneg := by intros; exact zero_le_one
  transition_total := by intros; simp
  reward := fun h _ a => if a then (w h : ℚ)/(∑ i, (w i : ℚ)) else 0
  cost := fun h _ a => if a then (w h : ℚ)/(∑ i, (w i : ℚ)) else 0
  cost_bounds := by
    intro h s a
    have hCr : (0 : ℝ) < ∑ i, (w i : ℝ) := by exact_mod_cast hC
    have hb := normalized_weight_bounds w hCr rfl h
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, Rat.cast_zero,
      Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]
    · exact ⟨le_rfl, zero_le_one⟩
    · exact hb
  tailMass := α
  tailMass_pos := ha
  tailMass_le_one := ha1.le
  budget := (B : ℚ)/(∑ i, (w i : ℚ))
  target := (B : ℚ)/(∑ i, (w i : ℚ))
  initial := ()

theorem subsetSumPlanningInput_kernel (w : Fin H → ℕ) (B : ℕ) (α : ℚ)
    (ha : 0 < α) (ha1 : α < 1) (hC : 0 < ∑ i, w i) :
    (subsetSumPlanningInput w B α ha ha1 hC).kernel = oneStateKernel := by
  funext s a
  apply Subtype.ext
  funext t
  change (subsetSumPlanningInput w B α ha ha1 hC).kernel s a t = oneStateKernel s a t
  rw [RationalPlanningInput.kernel_apply, oneStateKernel_apply]
  norm_num [subsetSumPlanningInput]

theorem subsetSumPlanningInput_cost (w : Fin H → ℕ) (B : ℕ) (α : ℚ)
    (ha : 0 < α) (ha1 : α < 1) (hC : 0 < ∑ i, w i) :
    realStages (subsetSumPlanningInput w B α ha ha1 hC).cost =
      takeSkipCost (normalizedStages w (∑ i, (w i : ℝ))) := by
  funext h s a
  by_cases hh : h < H <;> cases a <;>
    simp [realStages, subsetSumPlanningInput, takeSkipCost, normalizedStages, hh]

/-- Exact reduction from integer Subset-Sum to Definition 6.1 itself. -/
theorem subsetSumPlanningInput_feasible_iff (w : Fin H → ℕ) (B : ℕ) (α : ℚ)
    (ha : 0 < α) (ha1 : α < 1) (hw : ∀ i, 0 < w i) (hC : 0 < ∑ i, w i) :
    (subsetSumPlanningInput w B α ha ha1 hC).Feasible ↔
      ∃ s : Finset (Fin H), ∑ i ∈ s, w i = B := by
  let I := subsetSumPlanningInput w B α ha ha1 hC
  have hCreal : (0 : ℝ) < ∑ i, (w i : ℝ) := by exact_mod_cast hC
  have har : (0 : ℝ) < (α : ℝ) := by exact_mod_cast ha
  have ha1r : (α : ℝ) < 1 := by exact_mod_cast ha1
  have hc := subsetSumPlanningInput_cost w B α ha ha1 hC
  have hr : realStages I.reward = takeSkipCost (normalizedStages w (∑ i, (w i : ℝ))) := hc
  unfold RationalPlanningInput.Feasible
  rw [subsetSumPlanningInput_kernel, hc, hr]
  have he := actual_one_state_subset_sum_reduction w B har ha1r hw hCreal rfl
  simpa only [subsetSumPlanningInput, Rat.cast_div, Rat.cast_natCast, Rat.cast_sum] using he

/-! ## Complete restricted-subclass linear certificate, including expected reward -/

/-- Ordinary expected rewards for arbitrary two-action reward tables. -/
theorem one_state_two_action_reward_sum (r₀ r₁ : ℕ → ℝ)
    (π : Nested.Policy Unit Bool) (n h : ℕ) :
    Nested.reward (twoActionCost r₀ r₁) π oneStateKernel n h () =
      ∑ i ∈ Finset.range n, (r₀ (h+i)+(r₁ (h+i)-r₀ (h+i))*π (h+i) () true) := by
  induction n generalizing h with
  | zero => simp [Nested.reward]
  | succ n ih =>
    have ht : π h () true + π h () false = 1 := by
      simpa only [Fintype.sum_bool] using (π h ()).property.2
    rw [Nested.reward]
    simp only [Fintype.sum_bool, twoActionCost, Bool.false_eq_true, ↓reduceIte,
      oneStateKernel_apply, Fintype.sum_unique, one_mul, ih]
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have he : (∑ i ∈ Finset.range n, (r₀ (h+1+i)+(r₁ (h+1+i)-r₀ (h+1+i))*π (h+1+i) () true)) =
      ∑ i ∈ Finset.range n, (r₀ (h+(i+1))+(r₁ (h+(i+1))-r₀ (h+(i+1)))*π (h+(i+1)) () true) := by
      apply Finset.sum_congr rfl
      intro i _
      have he : h+1+i = h+(i+1) := by omega
      rw [he]
    rw [he]
    have hm := congrArg (fun z : ℝ => z * (r₀ h + ∑ i ∈ Finset.range n,
      (r₀ (h+(i+1))+(r₁ (h+(i+1))-r₀ (h+(i+1)))*π (h+(i+1)) () true))) ht
    nlinarith [hm]

def finiteScalar (f : Fin H → ℚ) (h : ℕ) : ℝ :=
  if hh : h < H then (f ⟨h,hh⟩ : ℝ) else 0

@[simp] theorem finiteScalar_at (f : Fin H → ℚ) (h : Fin H) : finiteScalar f h = (f h : ℝ) := by
  simp [finiteScalar, h.isLt]

theorem finiteScalar_bounds (f : Fin H → ℚ) (hf : ∀ h, (f h : ℝ) ∈ Icc 0 1) :
    ∀ h, finiteScalar f h ∈ Icc 0 1 := by
  intro h
  unfold finiteScalar
  split_ifs
  · exact hf _
  · exact ⟨le_rfl, zero_le_one⟩

structure OneStatePieceConditions (α τ target : ℚ) (c₀ c₁ r₀ r₁ : Fin H → ℚ)
    (x : Fin H → ℝ) (b : Fin H → Bool) : Prop where
  lower : ∀ h, 0 ≤ x h
  upper : ∀ h, x h ≤ 1
  active : ∀ h, activePiece (α : ℝ)
    (expensiveProbability (c₀ h : ℝ) (c₁ h : ℝ) (x h)) (b h)
  risk : (∑ h, affineRiskPiece (α : ℝ) (c₀ h : ℝ) (c₁ h : ℝ) (x h) (b h)) ≤ (τ : ℝ)
  reward : (target : ℝ) ≤ ∑ h, ((r₀ h : ℝ)+((r₁ h : ℝ)-(r₀ h : ℝ))*x h)

/-- The complete restricted planning query, not just its risk test, is exactly
an existential choice of H probabilities and H affine pieces. -/
theorem one_state_piece_planning_exact (α τ target : ℚ) (c₀ c₁ r₀ r₁ : Fin H → ℚ)
    (ha : 0 < (α : ℝ)) (ha1 : (α : ℝ) ≤ 1)
    (hc₀ : ∀ h, (c₀ h : ℝ) ∈ Icc 0 1) (hc₁ : ∀ h, (c₁ h : ℝ) ∈ Icc 0 1) :
    (∃ π : Nested.Policy Unit Bool,
      Nested.risk (α : ℝ) (twoActionCost (finiteScalar c₀) (finiteScalar c₁)) π oneStateKernel H 0 () ≤ (τ : ℝ) ∧
      (target : ℝ) ≤ Nested.reward (twoActionCost (finiteScalar r₀) (finiteScalar r₁)) π oneStateKernel H 0 ()) ↔
      ∃ x : Fin H → ℝ, ∃ b : Fin H → Bool, OneStatePieceConditions α τ target c₀ c₁ r₀ r₁ x b := by
  have hre (π : Nested.Policy Unit Bool) :
      Nested.reward (twoActionCost (finiteScalar r₀) (finiteScalar r₁)) π oneStateKernel H 0 () =
        ∑ h : Fin H, ((r₀ h : ℝ)+((r₁ h : ℝ)-(r₀ h : ℝ))*π h () true) := by
    rw [one_state_two_action_reward_sum, ← Fin.sum_univ_eq_sum_range]
    simp only [Nat.zero_add, finiteScalar_at]
  have hri (π : Nested.Policy Unit Bool) := actual_one_state_piece_certificate (H := H) (α : ℝ) ha ha1
    (finiteScalar c₀) (finiteScalar c₁) (finiteScalar_bounds c₀ hc₀) (finiteScalar_bounds c₁ hc₁) π (τ : ℝ)
  constructor
  · rintro ⟨π, hrisk, hrew⟩
    obtain ⟨b, hb, hr⟩ := (hri π).1 hrisk
    refine ⟨fun h => π h () true, b, ?_⟩
    refine ⟨fun h => (bool_probability_bounds (π h ()) true).1,
      fun h => (bool_probability_bounds (π h ()) true).2, ?_, ?_, ?_⟩
    · simpa only [finiteScalar_at] using hb
    · simpa only [finiteScalar_at] using hr
    · simpa only [hre] using hrew
  · rintro ⟨x,b,hx⟩
    let π := bernoulliPolicy x hx.lower hx.upper
    refine ⟨π, ?_, ?_⟩
    · apply (hri π).2
      refine ⟨b, ?_, ?_⟩
      · simpa only [π, finiteScalar_at, bernoulliPolicy_at] using hx.active
      · simpa only [π, finiteScalar_at, bernoulliPolicy_at] using hx.risk
    · simpa only [hre, π, bernoulliPolicy_at] using hx.reward

/-- Explicit rational affine coefficients, computed using constant-many input
comparisons and rational arithmetic operations. -/
def riskIntercept (α d₀ d₁ : ℚ) (b : Bool) : ℚ :=
  if d₀ ≤ d₁ then (if b then d₁ else d₀)
  else (if b then d₀ else d₁+(d₀-d₁)/α)

def riskSlope (α d₀ d₁ : ℚ) (b : Bool) : ℚ :=
  if d₀ ≤ d₁ then (if b then 0 else (d₁-d₀)/α)
  else (if b then 0 else -(d₀-d₁)/α)

theorem risk_coefficients (α d₀ d₁ : ℚ) (b : Bool) (x : ℝ) :
    affineRiskPiece (α : ℝ) (d₀ : ℝ) (d₁ : ℝ) x b =
      (riskIntercept α d₀ d₁ b : ℝ)+(riskSlope α d₀ d₁ b : ℝ)*x := by
  by_cases h : d₀ ≤ d₁
  · have hr : (d₀ : ℝ) ≤ (d₁ : ℝ) := by exact_mod_cast h
    cases b <;> simp [riskIntercept, riskSlope, affineRiskPiece, affineTailPiece,
      expensiveProbability, h, hr, abs_of_nonneg (sub_nonneg.2 hr)]; ring
  · have hr : (d₁ : ℝ) ≤ (d₀ : ℝ) := by exact_mod_cast (le_of_not_ge h)
    have hn : ¬ (d₀ : ℝ) ≤ (d₁ : ℝ) := by exact_mod_cast h
    cases b <;> simp [riskIntercept, riskSlope, affineRiskPiece, affineTailPiece,
      expensiveProbability, h, hr, hn, abs_of_nonpos (sub_nonpos.2 hr)]; ring

inductive OneStateLinearAtom (H : ℕ)
  | lower : Fin H → OneStateLinearAtom H
  | upper : Fin H → OneStateLinearAtom H
  | active : Fin H → OneStateLinearAtom H
  | risk : OneStateLinearAtom H
  | reward : OneStateLinearAtom H
  deriving DecidableEq, Fintype

def activeSlope (_α d₀ d₁ : ℚ) (b : Bool) : ℚ :=
  if d₀ ≤ d₁ then (if b then -1 else 1) else (if b then 1 else -1)

def activeBound (α d₀ d₁ : ℚ) (b : Bool) : ℚ :=
  if d₀ ≤ d₁ then (if b then -α else α) else (if b then 1-α else α-1)

theorem active_affine_iff (α d₀ d₁ : ℚ) (b : Bool) (x : ℝ) :
    activePiece (α : ℝ) (expensiveProbability (d₀ : ℝ) (d₁ : ℝ) x) b ↔
      (activeSlope α d₀ d₁ b : ℝ)*x ≤ (activeBound α d₀ d₁ b : ℝ) := by
  by_cases h : d₀ ≤ d₁
  · have hr : (d₀ : ℝ) ≤ (d₁ : ℝ) := by exact_mod_cast h
    cases b <;> simp [activePiece, expensiveProbability, activeSlope, activeBound, h, hr]
  · have hr : ¬ (d₀ : ℝ) ≤ (d₁ : ℝ) := by exact_mod_cast h
    cases b <;> simp [activePiece, expensiveProbability, activeSlope, activeBound, h, hr]
    constructor <;> intro hh <;> linarith

def oneStateLinearCoefficients (α : ℚ) (c₀ c₁ r₀ r₁ : Fin H → ℚ) (b : Fin H → Bool) :
    OneStateLinearAtom H → Fin H → ℚ
  | .lower h, j => if j=h then -1 else 0
  | .upper h, j => if j=h then 1 else 0
  | .active h, j => if j=h then activeSlope α (c₀ h) (c₁ h) (b h) else 0
  | .risk, j => riskSlope α (c₀ j) (c₁ j) (b j)
  | .reward, j => -(r₁ j-r₀ j)

def oneStateLinearBound (α τ target : ℚ) (c₀ c₁ r₀ _r₁ : Fin H → ℚ) (b : Fin H → Bool) :
    OneStateLinearAtom H → ℚ
  | .lower _ => 0
  | .upper _ => 1
  | .active h => activeBound α (c₀ h) (c₁ h) (b h)
  | .risk => τ-∑ h, riskIntercept α (c₀ h) (c₁ h) (b h)
  | .reward => (∑ h, r₀ h)-target

def oneStateLinearSystem (α τ target : ℚ) (c₀ c₁ r₀ r₁ : Fin H → ℚ)
    (b : Fin H → Bool) (x : Fin H → ℝ) : Prop :=
  ∀ k, (∑ j, (oneStateLinearCoefficients α c₀ c₁ r₀ r₁ b k j : ℝ)*x j) ≤
    (oneStateLinearBound α τ target c₀ c₁ r₀ r₁ b k : ℝ)

/-- For each guessed H-bit piece vector, the actual source query is literally a
finite rational linear system, including reward and probability box constraints. -/
theorem one_state_linear_system_iff (α τ target : ℚ) (c₀ c₁ r₀ r₁ : Fin H → ℚ)
    (b : Fin H → Bool) (x : Fin H → ℝ) :
    oneStateLinearSystem α τ target c₀ c₁ r₀ r₁ b x ↔
      OneStatePieceConditions α τ target c₀ c₁ r₀ r₁ x b := by
  have hactive (h : Fin H) := active_affine_iff α (c₀ h) (c₁ h) (b h) (x h)
  have hrisk : ((∑ j, (riskSlope α (c₀ j) (c₁ j) (b j) : ℝ)*x j) ≤
      ((τ-∑ j, riskIntercept α (c₀ j) (c₁ j) (b j) : ℚ) : ℝ)) ↔
      (∑ j, affineRiskPiece (α : ℝ) (c₀ j : ℝ) (c₁ j : ℝ) (x j) (b j)) ≤ (τ : ℝ) := by
    simp only [risk_coefficients, Finset.sum_add_distrib, Rat.cast_sub, Rat.cast_sum]
    constructor <;> intro hh <;> linarith
  have hreward : (∑ j, ((-(r₁ j-r₀ j) : ℚ) : ℝ)*x j) ≤ (((∑ j, r₀ j)-target : ℚ) : ℝ) ↔
      (target : ℝ) ≤ ∑ j, ((r₀ j : ℝ)+((r₁ j : ℝ)-(r₀ j : ℝ))*x j) := by
    simp only [Rat.cast_neg, Rat.cast_sub, Rat.cast_sum, neg_mul,
      Finset.sum_neg_distrib, Finset.sum_add_distrib]
    constructor <;> intro hh <;> linarith
  constructor
  · intro hs
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h
      have hh := hs (.lower h)
      simpa [oneStateLinearCoefficients, oneStateLinearBound, apply_ite, ite_mul] using hh
    · intro h
      have hh := hs (.upper h)
      simpa [oneStateLinearCoefficients, oneStateLinearBound, apply_ite, ite_mul] using hh
    · intro h
      apply (hactive h).2
      simpa [oneStateLinearCoefficients, oneStateLinearBound, apply_ite, ite_mul] using hs (.active h)
    · exact hrisk.1 (hs .risk)
    · exact hreward.1 (hs .reward)
  · intro hx k
    cases k with
    | lower h => simpa [oneStateLinearCoefficients, oneStateLinearBound, apply_ite, ite_mul] using hx.lower h
    | upper h => simpa [oneStateLinearCoefficients, oneStateLinearBound, apply_ite, ite_mul] using hx.upper h
    | active h =>
      simpa [oneStateLinearCoefficients, oneStateLinearBound, apply_ite, ite_mul] using (hactive h).1 (hx.active h)
    | risk => exact hrisk.2 hx.risk
    | reward => exact hreward.2 hx.reward

/-- Restricted planning is a union over H-bit choices of explicitly rational LPs. -/
theorem one_state_LP_certificate_exact (α τ target : ℚ) (c₀ c₁ r₀ r₁ : Fin H → ℚ)
    (ha : 0 < (α : ℝ)) (ha1 : (α : ℝ) ≤ 1)
    (hc₀ : ∀ h, (c₀ h : ℝ) ∈ Icc 0 1) (hc₁ : ∀ h, (c₁ h : ℝ) ∈ Icc 0 1) :
    (∃ π : Nested.Policy Unit Bool,
      Nested.risk (α : ℝ) (twoActionCost (finiteScalar c₀) (finiteScalar c₁)) π oneStateKernel H 0 () ≤ (τ : ℝ) ∧
      (target : ℝ) ≤ Nested.reward (twoActionCost (finiteScalar r₀) (finiteScalar r₁)) π oneStateKernel H 0 ()) ↔
      ∃ b : Fin H → Bool, ∃ x : Fin H → ℝ, oneStateLinearSystem α τ target c₀ c₁ r₀ r₁ b x := by
  rw [one_state_piece_planning_exact α τ target c₀ c₁ r₀ r₁ ha ha1 hc₀ hc₁]
  constructor
  · rintro ⟨x,b,hx⟩
    exact ⟨b,x,(one_state_linear_system_iff α τ target c₀ c₁ r₀ r₁ b x).2 hx⟩
  · rintro ⟨b,x,hx⟩
    exact ⟨x,b,(one_state_linear_system_iff α τ target c₀ c₁ r₀ r₁ b x).1 hx⟩

/-- Exactly three stage-indexed inequality families and two target inequalities. -/
theorem one_state_linear_atom_count : Fintype.card (OneStateLinearAtom H) = 3*H+2 := by
  rw [← Fintype.card_congr (OneStateLinearAtom.proxyTypeEquiv H)]
  simp
  ring

/-- The piece choice is an H-bit vector, as required by the nondeterministic certificate. -/
theorem one_state_piece_choice_count : Fintype.card (Fin H → Bool) = 2^H := by simp

/-! ## Fully composed positive-target reduction, including the dummy stage -/

def paddedWeights (w : Fin H → ℕ) (B : ℕ) : Fin (H+1) → ℕ := Fin.cons (B+1) w

theorem padded_total_exceeds (w : Fin H → ℕ) (B : ℕ) : B < ∑ i, paddedWeights w B i := by
  simp only [paddedWeights, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  omega

theorem padded_weights_positive (w : Fin H → ℕ) (B : ℕ) (hw : ∀ i, 0 < w i) :
    ∀ i, 0 < paddedWeights w B i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [paddedWeights]
  · simpa [paddedWeights] using hw j

theorem padded_subset_sum_iff (w : Fin H → ℕ) (B : ℕ) :
    (∃ s : Finset (Fin (H+1)), ∑ i ∈ s, paddedWeights w B i = B) ↔
      ∃ s : Finset (Fin H), ∑ i ∈ s, w i = B := by
  constructor
  · rintro ⟨s,hs⟩
    have hn : (0 : Fin (H+1)) ∉ s := by
      intro hi
      have hh := Finset.single_le_sum (f := paddedWeights w B) (fun _ _ => Nat.zero_le _) hi
      rw [hs] at hh
      change B+1 ≤ B at hh
      omega
    let t := Finset.univ.filter (fun i : Fin H => i.succ ∈ s)
    have he : t.image Fin.succ = s := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hn]
      · simp [t, Fin.succ_inj]
    refine ⟨t, ?_⟩
    rw [← he, Finset.sum_image] at hs
    · simpa [paddedWeights] using hs
    · exact fun i _ j _ h => Fin.succ_inj.mp h
  · rintro ⟨s,hs⟩
    refine ⟨s.image Fin.succ, ?_⟩
    rw [Finset.sum_image]
    · simpa [paddedWeights] using hs
    · exact fun i _ j _ h => Fin.succ_inj.mp h

def paddedSubsetSumInput (w : Fin H → ℕ) (B : ℕ) (α : ℚ) (ha : 0 < α) (ha1 : α < 1) :
    RationalPlanningInput Unit Bool :=
  subsetSumPlanningInput (paddedWeights w B) B α ha ha1 (lt_of_le_of_lt (Nat.zero_le B) (padded_total_exceeds w B))

/-- No positive-total premise remains on the original Subset-Sum input. The
constructed rational planning instance incorporates its own dummy stage. -/
theorem paddedSubsetSumInput_feasible_iff (w : Fin H → ℕ) (B : ℕ) (α : ℚ)
    (ha : 0 < α) (ha1 : α < 1) (hw : ∀ i, 0 < w i) :
    (paddedSubsetSumInput w B α ha ha1).Feasible ↔
      ∃ s : Finset (Fin H), ∑ i ∈ s, w i = B := by
  unfold paddedSubsetSumInput
  rw [subsetSumPlanningInput_feasible_iff _ B α ha ha1 (padded_weights_positive w B hw),
    padded_subset_sum_iff]

/-- The dummy stage increases source binary size only linearly. -/
theorem padded_input_size_bound (w : Fin H → ℕ) (B : ℕ) :
    subsetInputBits (paddedWeights w B) B ≤ 2*subsetInputBits w B+3 := by
  have he := size_add_bound B 1
  rw [Nat.size_one] at he
  unfold subsetInputBits
  simp only [paddedWeights, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  omega

/-- The fully padded normalization still has polynomial binary rational payload. -/
theorem padded_reduction_payload_bound (w : Fin H → ℕ) (B : ℕ) :
    (∑ i, 4*fractionPayloadBits (paddedWeights w B i) (∑ j, paddedWeights w B j))+
      2*fractionPayloadBits B (∑ j, paddedWeights w B j) ≤
      12*(2*subsetInputBits w B+4)^2 := by
  have he := reduction_payload_quadratic (paddedWeights w B) B
  have hs := padded_input_size_bound w B
  nlinarith

end

end Paper36.Complexity
