import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# The one-stage obstruction to strict budget tightening

This file formalizes Proposition 3.1 and Corollary 3.2. A policy randomizes
between the three physical actions; that randomization is INSIDE the
Rockafellar--Uryasev upper-tail CVaR objective, with the infimum taken over all
real thresholds. No formula for CVaR, optimality, or duality is assumed.
-/
namespace Paper36.Tightening

open Set Filter
open scoped Topology BigOperators

inductive Action | safe | high | bad deriving DecidableEq, Fintype

/-- All randomized physical-state Markov policies of the one-state, one-stage model. -/
structure Policy where
  high : ℝ
  bad : ℝ
  high_nonneg : 0 ≤ high
  bad_nonneg : 0 ≤ bad
  sum_le : high + bad ≤ 1

noncomputable def Policy.safe (p : Policy) : ℝ := 1 - p.high - p.bad

def cost (t : ℝ) : Action → ℝ
  | .safe => 0 | .high => t | .bad => 1

def reward : Action → ℝ
  | .safe => 0 | .high => 1 | .bad => 0

noncomputable def Policy.prob (p : Policy) : Action → ℝ
  | .safe => p.safe | .high => p.high | .bad => p.bad

/-- The expected reward of the three-action policy is its high-action mass. -/
def value (p : Policy) : ℝ := p.high

lemma safe_nonneg (p : Policy) : 0 ≤ p.safe := by unfold Policy.safe; linarith [p.sum_le]
lemma high_le_one (p : Policy) : p.high ≤ 1 := by linarith [p.sum_le, p.bad_nonneg]

/-- The exact CVaR primal objective for the randomized three-action loss. -/
noncomputable def objective (α t : ℝ) (p : Policy) (z : ℝ) : ℝ :=
  z + (p.safe * max (-z) 0 + p.high * max (t-z) 0 +
    p.bad * max (1-z) 0) / α

/-- Upper-tail CVaR, with action randomization inside the positive part. -/
noncomputable def risk (α t : ℝ) (p : Policy) : ℝ :=
  sInf (Set.range (objective α t p))

noncomputable def bernoulliObjective (α t x z : ℝ) : ℝ :=
  z + ((1-x) * max (-z) 0 + x * max (t-z) 0) / α

lemma objective_ge_bernoulli (α t : ℝ) (hα : 0 < α) (p : Policy) (z : ℝ) :
    bernoulliObjective α t p.high z ≤ objective α t p z := by
  have hm : max (-z) 0 ≤ max (1-z) 0 := max_le_max (by linarith) le_rfl
  have hb := mul_le_mul_of_nonneg_left hm p.bad_nonneg
  unfold objective bernoulliObjective Policy.safe
  apply add_le_add_left
  apply div_le_div_of_nonneg_right _ hα.le
  nlinarith

lemma bernoulli_scaled (α t x z : ℝ) (hα : α ≠ 0) :
    α * bernoulliObjective α t x z =
      α*z + (1-x)*max (-z) 0 + x*max (t-z) 0 := by
  unfold bernoulliObjective
  field_simp
  <;> ring

/-- Direct derivation of the Bernoulli CVaR lower bound for every threshold. -/
lemma bernoulli_lower (α t x z : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 ≤ t) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    t * min (x / α) 1 ≤ bernoulliObjective α t x z := by
  have hs := bernoulli_scaled α t x z hα.ne'
  have hmin0 : 0 ≤ min (x / α) 1 := le_min (div_nonneg hx hα.le) (by norm_num)
  have hmin1 : min (x / α) 1 ≤ 1 := min_le_right _ _
  have hminx : α * min (x / α) 1 ≤ x := by
    have hh := mul_le_mul_of_nonneg_left (min_le_left (x / α) 1) hα.le
    simpa [mul_div_cancel₀ _ hα.ne'] using hh
  apply (mul_le_mul_left hα).mp
  by_cases hz : z ≤ 0
  · have hm0 : max (-z) 0 = -z := max_eq_left (by linarith)
    have hmt : max (t-z) 0 = t-z := max_eq_left (by linarith)
    rw [hm0, hmt] at hs
    have hxbound : α * (t * min (x / α) 1) ≤ t*x := by nlinarith
    nlinarith
  · have hz0 : 0 ≤ z := le_of_lt (lt_of_not_ge hz)
    have hm0 : max (-z) 0 = 0 := max_eq_right (by linarith)
    rw [hm0] at hs
    by_cases hzt : z ≤ t
    · have hmt : max (t-z) 0 = t-z := max_eq_left (by linarith)
      rw [hmt] at hs
      have hleft : 0 ≤ (x - α * min (x / α) 1) * (t-z) :=
        mul_nonneg (by linarith) (by linarith)
      have hright : 0 ≤ α * (1-min (x / α) 1) * z :=
        mul_nonneg (mul_nonneg hα.le (by linarith)) hz0
      nlinarith
    · have hmt : max (t-z) 0 = 0 := max_eq_right (by linarith)
      rw [hmt] at hs
      have htm : t * min (x / α) 1 ≤ t := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hmin1 ht
      have ham := mul_le_mul_of_nonneg_left htm hα.le
      nlinarith

lemma objective_nonneg (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 ≤ t) (p : Policy) (z : ℝ) : 0 ≤ objective α t p z := by
  have hh := bernoulli_lower α t p.high z hα hα1 ht p.high_nonneg (high_le_one p)
  have hn : 0 ≤ t * min (p.high / α) 1 :=
    mul_nonneg ht (le_min (div_nonneg p.high_nonneg hα.le) (by norm_num))
  exact le_trans hn (le_trans hh (objective_ge_bernoulli α t hα p z))

lemma risk_bddBelow (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 ≤ t) (p : Policy) : BddBelow (Set.range (objective α t p)) :=
  ⟨0, by rintro _ ⟨z, rfl⟩; exact objective_nonneg α t hα hα1 ht p z⟩

lemma risk_le_objective (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 ≤ t) (p : Policy) (z : ℝ) : risk α t p ≤ objective α t p z :=
  csInf_le (risk_bddBelow α t hα hα1 ht p) (mem_range_self z)

lemma risk_lower (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 ≤ t) (p : Policy) : t * min (p.high / α) 1 ≤ risk α t p := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨z, rfl⟩
  exact le_trans (bernoulli_lower α t p.high z hα hα1 ht p.high_nonneg
    (high_le_one p)) (objective_ge_bernoulli α t hα p z)

lemma risk_nonneg (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 ≤ t) (p : Policy) : 0 ≤ risk α t p := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨z, rfl⟩
  exact objective_nonneg α t hα hα1 ht p z

/-- A policy supported only on safe and high; all Bernoulli randomizations occur. -/
def mix (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : Policy :=
  ⟨x, 0, hx, le_rfl, by linarith⟩

def pureSafe : Policy := mix 0 le_rfl (by norm_num)
def pureHigh : Policy := mix 1 (by norm_num) le_rfl
def pureBad : Policy := ⟨0, 1, le_rfl, by norm_num, by norm_num⟩

/-- Equation (3.1), proved from the real-threshold CVaR infimum. -/
theorem risk_mix (α t x : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 ≤ t) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    risk α t (mix x hx hx1) = t * min (x / α) 1 := by
  apply le_antisymm _ (risk_lower α t hα hα1 ht _)
  change risk α t (mix x hx hx1) ≤ t * min (x / α) 1
  by_cases hxα : x / α ≤ 1
  · rw [min_eq_left hxα]
    have hh := risk_le_objective α t hα hα1 ht (mix x hx hx1) 0
    simpa [objective, mix, Policy.safe, max_eq_left ht, mul_div_assoc, mul_comm] using hh
  · rw [min_eq_right (le_of_not_ge hxα)]
    have hh := risk_le_objective α t hα hα1 ht (mix x hx hx1) t
    simpa [objective, mix, Policy.safe, max_eq_right (neg_nonpos.mpr ht)] using hh

lemma risk_safe (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (ht : 0 ≤ t) :
    risk α t pureSafe = 0 := by
  simpa [pureSafe] using risk_mix α t 0 hα hα1 ht le_rfl (by norm_num)

lemma risk_high (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (ht : 0 ≤ t) :
    risk α t pureHigh = t := by
  have hh : 1 ≤ 1 / α := (le_div_iff₀ hα).mpr (by simpa using hα1)
  unfold pureHigh
  rw [risk_mix α t 1 hα hα1 ht (by norm_num) le_rfl, min_eq_right hh, mul_one]

lemma risk_bad (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (ht : 0 ≤ t) :
    risk α t pureBad = 1 := by
  have hl : 1 ≤ risk α t pureBad := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨z, rfl⟩
    have hs : α * objective α t pureBad z = α*z + max (1-z) 0 := by
      unfold objective pureBad Policy.safe
      field_simp
      <;> ring
    apply (mul_le_mul_left hα).mp
    by_cases hz : z ≤ 1
    · rw [max_eq_left (by linarith : 0 ≤ 1-z)] at hs
      nlinarith
    · rw [max_eq_right (by linarith : 1-z ≤ 0)] at hs
      nlinarith
  have hu := risk_le_objective α t hα hα1 ht pureBad 1
  exact le_antisymm (by simpa [objective, pureBad, Policy.safe] using hu) hl

/-- Replacing all bad mass by safe mass preserves reward and decreases risk. -/
theorem remove_bad (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 ≤ t) (p : Policy) :
    value (mix p.high p.high_nonneg (high_le_one p)) = value p ∧
    risk α t (mix p.high p.high_nonneg (high_le_one p)) ≤ risk α t p := by
  constructor
  · rfl
  · rw [risk_mix α t p.high hα hα1 ht]
    exact risk_lower α t hα hα1 ht p

noncomputable def feasibleRewards (α t b : ℝ) : Set ℝ :=
  {v | ∃ p : Policy, risk α t p ≤ b ∧ v = value p}
noncomputable def primalValue (α t b : ℝ) : ℝ := sSup (feasibleRewards α t b)

/-- All policies feasible for a strictly smaller budget have small high mass. -/
theorem feasible_high_bound (α t b : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 < t) (hb : b < t) (p : Policy) (hp : risk α t p ≤ b) :
    p.high ≤ α * b / t := by
  have hl := risk_lower α t hα hα1 ht.le p
  have hxα : p.high / α < 1 := by
    by_contra hn
    rw [min_eq_right (le_of_not_gt hn)] at hl
    nlinarith
  rw [min_eq_left hxα.le] at hl
  apply (le_div_iff₀ ht).mpr
  have hh : t * p.high ≤ b * α := by
    have := (div_le_iff₀ hα).mp (show t * p.high / α ≤ b by
      simpa [mul_div_assoc] using le_trans hl hp)
    exact this
  nlinarith

/-- The original budget has value one, with an attained optimum. -/
theorem original_optimum (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (ht : 0 ≤ t) :
    IsGreatest (feasibleRewards α t t) 1 := by
  constructor
  · exact ⟨pureHigh, (risk_high α t hα hα1 ht).le, rfl⟩
  · rintro v ⟨p, _, rfl⟩
    exact high_le_one p

/-- The exact strictly tightened primal value, with an explicit optimizer. -/
theorem tightened_optimum (α t b : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 < t) (hb0 : 0 ≤ b) (hbt : b < t) :
    IsGreatest (feasibleRewards α t b) (α * b / t) := by
  have hx0 : 0 ≤ α * b / t := div_nonneg (mul_nonneg hα.le hb0) ht.le
  have hx1 : α * b / t ≤ 1 := by
    apply (div_le_iff₀ ht).mpr
    nlinarith
  have hxα : (α * b / t) / α = b / t := by field_simp <;> ring
  have hbt' : b / t ≤ 1 := (div_le_one ht).mpr hbt.le
  constructor
  · refine ⟨mix (α*b/t) hx0 hx1, ?_, rfl⟩
    rw [risk_mix α t (α*b/t) hα hα1 ht.le hx0 hx1, hxα, min_eq_left hbt']
    have : t * (b / t) = b := by field_simp
    exact this.le
  · rintro v ⟨p, hp, rfl⟩
    exact feasible_high_bound α t b hα hα1 ht hbt p hp

 theorem primal_original (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (ht : 0 ≤ t) :
    primalValue α t t = 1 := (original_optimum α t hα hα1 ht).csSup_eq

 theorem primal_tightened (α t b : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 < t) (hb0 : 0 ≤ b) (hbt : b < t) :
    primalValue α t b = α*b/t := (tightened_optimum α t b hα hα1 ht hb0 hbt).csSup_eq

/-- Risk dominates expected high-action cost, the key scalar dual estimate. -/
lemma risk_ge_expected_high (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 ≤ t) (p : Policy) : t * p.high ≤ risk α t p := by
  have hm : p.high ≤ min (p.high / α) 1 := by
    apply le_min _ (high_le_one p)
    apply (le_div_iff₀ hα).mpr
    nlinarith [p.high_nonneg]
  exact le_trans (mul_le_mul_of_nonneg_left hm ht) (risk_lower α t hα hα1 ht p)

noncomputable def lagrangianRewards (α t l : ℝ) : Set ℝ :=
  Set.range (fun p : Policy => value p - l * risk α t p)
noncomputable def innerValue (α t l : ℝ) : ℝ := sSup (lagrangianRewards α t l)

/-- The scalar Lagrangian inner maximum is attained at safe or high. -/
theorem lagrangian_maximum (α t l : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 ≤ t) (hl : 0 ≤ l) :
    IsGreatest (lagrangianRewards α t l) (max 0 (1-l*t)) := by
  constructor
  · by_cases he : 0 ≤ 1-l*t
    · rw [max_eq_right he]
      refine ⟨pureHigh, ?_⟩
      change value pureHigh - l * risk α t pureHigh = 1-l*t
      rw [risk_high α t hα hα1 ht]
      rfl
    · rw [max_eq_left (le_of_not_ge he)]
      refine ⟨pureSafe, ?_⟩
      change value pureSafe - l * risk α t pureSafe = 0
      rw [risk_safe α t hα hα1 ht]
      simp [value, pureSafe, mix]
  · rintro _ ⟨p, rfl⟩
    have hr := mul_le_mul_of_nonneg_left (risk_ge_expected_high α t hα hα1 ht p) hl
    have hi := high_le_one p
    have hn := p.high_nonneg
    unfold value
    by_cases he : 0 ≤ 1-l*t
    · rw [max_eq_right he]
      have hh : 0 ≤ (1-p.high)*(1-l*t) := mul_nonneg (by linarith) he
      nlinarith
    · rw [max_eq_left (le_of_not_ge he)]
      have hh : p.high*(1-l*t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn (le_of_not_ge he)
      nlinarith

lemma innerValue_eq (α t l : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 ≤ t) (hl : 0 ≤ l) : innerValue α t l = max 0 (1-l*t) :=
  (lagrangian_maximum α t l hα hα1 ht hl).csSup_eq

noncomputable def dualObjectives (α t b : ℝ) : Set ℝ :=
  {d | ∃ l : ℝ, 0 ≤ l ∧ d = l*b + innerValue α t l}
noncomputable def dualValue (α t b : ℝ) : ℝ := sInf (dualObjectives α t b)

/-- The exact scalar dual infimum, attained at multiplier 1/t. -/
theorem dual_optimum (α t b : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 < t) (hb0 : 0 ≤ b) (hbt : b ≤ t) :
    IsLeast (dualObjectives α t b) (b/t) := by
  constructor
  · refine ⟨1/t, div_nonneg (by norm_num) ht.le, ?_⟩
    rw [innerValue_eq α t (1/t) hα hα1 ht.le (div_nonneg (by norm_num) ht.le)]
    have ht0 := ht.ne'
    field_simp
    <;> simp [max_self]
  · rintro _ ⟨l, hl, rfl⟩
    rw [innerValue_eq α t l hα hα1 ht.le hl]
    apply (div_le_iff₀ ht).mpr
    by_cases he : 0 ≤ 1-l*t
    · rw [max_eq_right he]
      have hh : 0 ≤ (t-b)*(1-l*t) := mul_nonneg (by linarith) he
      nlinarith
    · rw [max_eq_left (le_of_not_ge he)]
      have hh : 0 ≤ b*(l*t-1) := mul_nonneg hb0 (by linarith)
      nlinarith

 theorem dual_tightened (α t b : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 < t) (hb0 : 0 ≤ b) (hbt : b ≤ t) :
    dualValue α t b = b/t := (dual_optimum α t b hα hα1 ht hb0 hbt).csInf_eq

/-- The claimed strict duality gap for every positive strict tightening. -/
theorem strict_duality_gap (α t b : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ht : 0 < t) (hb0 : 0 < b) (hbt : b < t) :
    primalValue α t b < dualValue α t b := by
  rw [primal_tightened α t b hα hα1.le ht hb0.le hbt,
      dual_tightened α t b hα hα1.le ht hb0.le hbt.le]
  exact (div_lt_div_iff_of_pos_right ht).mpr (by nlinarith)

/-- The constructed model has minimum risk zero and hence strict margin t. -/
theorem minimum_risk (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (ht : 0 ≤ t) :
    IsLeast (Set.range (risk α t)) 0 := by
  constructor
  · exact ⟨pureSafe, risk_safe α t hα hα1 ht⟩
  · rintro _ ⟨p, rfl⟩
    exact risk_nonneg α t hα hα1 ht p

/-- The budget t in (0,1) is strictly feasible and nonvacuous. -/
theorem nonvacuous_strict_feasibility (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 < t) (ht1 : t < 1) :
    risk α t pureSafe < t ∧ risk α t pureBad > t ∧
      t - sInf (Set.range (risk α t)) = t := by
  rw [risk_safe α t hα hα1 ht.le, risk_bad α t hα hα1 ht.le,
      (minimum_risk α t hα hα1 ht.le).csInf_eq]
  exact ⟨ht, ht1, by ring⟩

/-- Per-episode strict tightening loses at least 1-alpha reward. -/
theorem strict_tightening_loss (α t ε : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 < t) (hε : 0 < ε) (hεt : ε < t) (p : Policy)
    (hp : risk α t p ≤ t-ε) :
    1-α + α*ε/t ≤ primalValue α t t - value p := by
  rw [primal_original α t hα hα1 ht.le]
  have hh := feasible_high_bound α t (t-ε) hα hα1 ht (by linarith) p hp
  unfold value
  have he : α*(t-ε)/t = α-α*ε/t := by field_simp <;> ring
  rw [he] at hh
  linarith

/-- Corollary 3.2, for arbitrary episode policies and arbitrary positive tightenings. -/
theorem linear_regret (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (ht : 0 < t)
    (K : ℕ) (ε : Fin K → ℝ) (p : Fin K → Policy)
    (hε : ∀ k, 0 < ε k ∧ ε k < t)
    (hp : ∀ k, risk α t (p k) ≤ t-ε k) :
    (1-α)*(K : ℝ) ≤ ∑ k : Fin K, (primalValue α t t - value (p k)) := by
  have hh : ∀ k, 1-α ≤ primalValue α t t - value (p k) := by
    intro k
    have hl := strict_tightening_loss α t (ε k) hα hα1 ht
      (hε k).1 (hε k).2 (p k) (hp k)
    have hn : 0 ≤ α*ε k/t := div_nonneg (mul_nonneg hα.le (hε k).1.le) ht.le
    linarith
  calc
    (1-α)*(K : ℝ) = ∑ _k : Fin K, (1-α) := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum (fun k _ => hh k)

/-- The left-limit reward loss is exactly 1-alpha. -/
theorem tightening_loss_limit (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 < t) :
    Tendsto (fun b : ℝ => primalValue α t t - primalValue α t b)
      (𝓝[<] t) (𝓝 (1-α)) := by
  have hf : Tendsto (fun b : ℝ => 1-α*b/t) (𝓝[<] t) (𝓝 (1-α)) := by
    have hc : Continuous (fun b : ℝ => 1-α*b/t) := by fun_prop
    have hv : 1-α*t/t = 1-α := by field_simp
    have hc' : Tendsto (fun b : ℝ => 1-α*b/t) (𝓝 t) (𝓝 (1-α*t/t)) := hc.tendsto t
    rw [hv] at hc'
    exact hc'.mono_left inf_le_left
  apply Filter.Tendsto.congr' _ hf
  filter_upwards [Ioo_mem_nhdsLT ht] with b hb
  rw [primal_original α t hα hα1 ht.le,
    primal_tightened α t b hα hα1 ht hb.1.le hb.2]


/-- The policy coordinates form a probability distribution on the three actions. -/
theorem policy_probability (p : Policy) :
    (∀ a, 0 ≤ p.prob a) ∧ ∑ a : Action, p.prob a = 1 := by
  have hu : (Finset.univ : Finset Action) = {.safe, .high, .bad} := by decide
  constructor
  · intro a
    cases a with
    | safe => exact safe_nonneg p
    | high => exact p.high_nonneg
    | bad => exact p.bad_nonneg
  · rw [hu]
    simp [Policy.prob, Policy.safe]

/-- Conversely, every probability law on the three physical actions is represented. -/
theorem every_action_law (q : Action → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hs : ∑ a : Action, q a = 1) : ∃ p : Policy, p.prob = q := by
  have hu : (Finset.univ : Finset Action) = {.safe, .high, .bad} := by decide
  have hsum : q .safe + q .high + q .bad = 1 := by
    simpa [hu, add_assoc] using hs
  have hpair : q .high + q .bad ≤ 1 := by linarith [hq .safe]
  refine ⟨⟨q .high, q .bad, hq .high, hq .bad, hpair⟩, ?_⟩
  funext a
  cases a with
  | safe => simp only [Policy.prob, Policy.safe]; linarith
  | high => rfl
  | bad => rfl

/-- Both the costs and rewards are in the paper's unit interval. -/
theorem model_bounds (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∀ a, 0 ≤ cost t a ∧ cost t a ≤ 1) ∧
      (∀ a, 0 ≤ reward a ∧ reward a ≤ 1) := by
  constructor
  · intro a; cases a <;> simp [cost, ht, ht1]
  · intro a; cases a <;> norm_num [reward]

/-- The expected reward formula agrees with summation over the physical actions. -/
theorem reward_expectation (p : Policy) :
    (∑ a : Action, p.prob a * reward a) = value p := by
  have hu : (Finset.univ : Finset Action) = {.safe, .high, .bad} := by decide
  rw [hu]
  simp [Policy.prob, reward, value]

/-- The scalar objective is exactly the CVaR objective of the action loss law. -/
theorem objective_action_law (α t : ℝ) (p : Policy) (z : ℝ) :
    objective α t p z =
      z + (∑ a : Action, p.prob a * max (cost t a - z) 0) / α := by
  have hu : (Finset.univ : Finset Action) = {.safe, .high, .bad} := by decide
  rw [hu]
  simp [objective, Policy.prob, cost, add_assoc]

/-- In particular, risk is CVaR of the full randomized action, not a mixture of risks. -/
theorem risk_action_law (α t : ℝ) (p : Policy) :
    risk α t p = sInf (Set.range (fun z : ℝ =>
      z + (∑ a : Action, p.prob a * max (cost t a - z) 0) / α)) := by
  unfold risk
  congr 1
  congr 1
  funext z
  exact objective_action_law α t p z

/-- Proposition 3.1 as a single existence statement, using the interior budget 1/2. -/
theorem proposition_3_1 (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      IsLeast (Set.range (risk α t)) 0 ∧
      risk α t pureSafe < t ∧ t < risk α t pureBad ∧
      t - sInf (Set.range (risk α t)) = t ∧
      primalValue α t t = 1 ∧
      (∀ b : ℝ, 0 < b → b < t →
        primalValue α t b = α*b/t ∧ dualValue α t b = b/t ∧
          primalValue α t b < dualValue α t b) ∧
      Tendsto (fun b : ℝ => primalValue α t t - primalValue α t b)
        (𝓝[<] t) (𝓝 (1-α)) := by
  let t : ℝ := 1/2
  have ht : 0 < t := by norm_num [t]
  have ht1 : t < 1 := by norm_num [t]
  have hs := nonvacuous_strict_feasibility α t hα hα1.le ht ht1
  refine ⟨t, ht, ht1, minimum_risk α t hα hα1.le ht.le,
    hs.1, hs.2.1, hs.2.2, primal_original α t hα hα1.le ht.le, ?_,
    tightening_loss_limit α t hα hα1.le ht⟩
  intro b hb hbt
  exact ⟨primal_tightened α t b hα hα1.le ht hb.le hbt,
    dual_tightened α t b hα hα1.le ht hb.le hbt.le,
    strict_duality_gap α t b hα hα1 ht hb hbt⟩

end Paper36.Tightening
