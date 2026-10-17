import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The rare-chain experiment (Theorem 7.1, Corollary 7.2, Appendix F)

Histories contain the selected branch, every failure-depth signal, and the
endpoint signal.  The latter is represented by the model index: the selected
branch and the public good/bad endpoint determine exactly this index.
A strategy is an arbitrary function of this observable history, with randomized
branch probabilities.  It cannot inspect the latent model argument of `eval`.
-/
namespace Paper36.LowerBound

noncomputable section

open Finset

structure Policy where
  left : ℝ
  right : ℝ
  safe : ℝ
  left_nonneg : 0 ≤ left
  right_nonneg : 0 ≤ right
  safe_nonneg : 0 ≤ safe
  total : left + right + safe = 1

/-- Risk of the randomized first action, as computed in (F.1). -/
def Policy.risk (p : Policy) (θ : Bool) : ℝ := if θ then p.left else p.right

theorem Policy.risk_nonneg (p : Policy) (θ : Bool) : 0 ≤ p.risk θ := by
  cases θ <;> simp [Policy.risk, p.left_nonneg, p.right_nonneg]

structure FailureLaw (ι : Type*) [Fintype ι] where
  beta : ℝ
  beta_nonneg : 0 ≤ beta
  beta_le_one : beta ≤ 1
  mass : ι → ℝ
  mass_nonneg : ∀ i, 0 ≤ mass i
  total : ∑ i, mass i = 1 - beta

inductive Signal (ι : Type*) where
  | failure (depth : ι)
  | endpoint (model : Bool)
  | fallback

abbrev History (ι : Type*) := List (Option Bool × Signal ι)
abbrev Strategy (ι : Type*) := History ι → Policy

/-- The expected signed debt plus `coeff` times reward shortfall, computed directly
by the finite trajectory tree.  `false` and `true` denote the two branches;
`none` denotes the fallback. -/
def eval {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (coeff : ℝ) (θ : Bool) (h : History ι) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
    (σ h).risk θ - 1/4 + coeff * (σ h).safe +
    (σ h).left *
      ((∑ i, L.mass i * eval L σ coeff θ ((some false, Signal.failure i) :: h) n) +
        L.beta * eval L σ coeff θ ((some false, Signal.endpoint θ) :: h) n) +
    (σ h).right *
      ((∑ i, L.mass i * eval L σ coeff θ ((some true, Signal.failure i) :: h) n) +
        L.beta * eval L σ coeff θ ((some true, Signal.endpoint θ) :: h) n) +
    (σ h).safe * eval L σ coeff θ ((none, Signal.fallback) :: h) n

def bayes {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (coeff : ℝ) (h : History ι) (n : ℕ) : ℝ :=
  (eval L σ coeff false h n + eval L σ coeff true h n) / 2

/-- The geometric expression before division by the positive hazard. -/
def bound (β : ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ range n, (1 - β)^j) / 2 - (n : ℝ) / 4

theorem bound_floor {β : ℝ} (hβ : β ≤ 1) (n : ℕ) : -(n : ℝ)/4 ≤ bound β n := by
  have hs : 0 ≤ ∑ j ∈ range n, (1 - β)^j := by
    exact sum_nonneg fun j _ => pow_nonneg (sub_nonneg.mpr hβ) j
  unfold bound
  linarith

theorem bound_zero (β : ℝ) : bound β 0 = 0 := by simp [bound]

theorem bound_succ (β : ℝ) (n : ℕ) :
    bound β (n+1) = 1/4 + (1-β) * bound β n - β * (n : ℝ)/4 := by
  have hg := geom_sum_mul (1 - β) n
  simp only [bound, sum_range_succ, Nat.cast_add, Nat.cast_one]
  nlinarith [hg]

theorem bound_closed {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    bound β n = (1 - (1 - β)^n) / (2*β) - (n : ℝ)/4 := by
  have hg := geom_sum_mul (1 - β) n
  have hb : β ≠ 0 := ne_of_gt hβ
  unfold bound
  field_simp
  nlinarith [hg]

private theorem weighted_floor {ι : Type*} [Fintype ι] (L : FailureLaw ι)
    (f : ι → ℝ) (b : ℝ) (hf : ∀ i, b ≤ f i) :
    (1 - L.beta) * b ≤ ∑ i, L.mass i * f i := by
  calc
    (1 - L.beta) * b = ∑ i, L.mass i * b := by rw [← sum_mul, L.total]
    _ ≤ _ := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf i) (L.mass_nonneg i)

/-- Nonnegativity of risk gives the universal post-identification floor. -/
theorem eval_floor {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    {coeff : ℝ} (hcoeff : 0 ≤ coeff) (θ : Bool) (h : History ι) (n : ℕ) :
    -(n : ℝ)/4 ≤ eval L σ coeff θ h n := by
  induction n generalizing h with
  | zero => simp [eval]
  | succ n ih =>
    let b : ℝ := -(n : ℝ)/4
    have hc (a : Bool) : b ≤
        (∑ i, L.mass i * eval L σ coeff θ ((some a, Signal.failure i)::h) n) +
          L.beta * eval L σ coeff θ ((some a, Signal.endpoint θ)::h) n := by
      have hf := weighted_floor L (fun i => eval L σ coeff θ ((some a, Signal.failure i)::h) n) b (fun i => ih _)
      have he := mul_le_mul_of_nonneg_left (ih ((some a, Signal.endpoint θ)::h)) L.beta_nonneg
      dsimp [b] at *
      nlinarith
    have hl := mul_le_mul_of_nonneg_left (hc false) (σ h).left_nonneg
    have hr := mul_le_mul_of_nonneg_left (hc true) (σ h).right_nonneg
    have hs := mul_le_mul_of_nonneg_left (ih ((none, Signal.fallback)::h)) (σ h).safe_nonneg
    have hi := (σ h).risk_nonneg θ
    have hp := mul_nonneg hcoeff (σ h).safe_nonneg
    have ht := (σ h).total
    have hn : (σ h).left*b + (σ h).right*b + (σ h).safe*b = b := by
      rw [← add_mul, ← add_mul, ht, one_mul]
    simp only [eval, Nat.cast_add, Nat.cast_one]
    dsimp [b] at *
    nlinarith

/-- Pair the two model values before revelation.  The strategy is shared by
both models, while every failure signal has the same likelihood. -/
theorem bayes_lower {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    {coeff : ℝ} (hcoeff : 0 ≤ coeff)
    (hscore : ∀ h, (1/2 - coeff) * (σ h).safe ≤ 0)
    (h : History ι) (n : ℕ) : bound L.beta n ≤ bayes L σ coeff h n := by
  induction n generalizing h with
  | zero => simp [bound, bayes, eval]
  | succ n ih =>
    let B := bound L.beta n
    let b : ℝ := -(n : ℝ)/4
    have hc (a : Bool) :
        (1-L.beta)*B + L.beta*b ≤
        (((∑ i, L.mass i * eval L σ coeff false ((some a, Signal.failure i)::h) n) +
            L.beta * eval L σ coeff false ((some a, Signal.endpoint false)::h) n) +
          ((∑ i, L.mass i * eval L σ coeff true ((some a, Signal.failure i)::h) n) +
            L.beta * eval L σ coeff true ((some a, Signal.endpoint true)::h) n)) / 2 := by
      have hf := weighted_floor L
        (fun i => bayes L σ coeff ((some a, Signal.failure i)::h) n) B (fun i => ih _)
      have he0 := eval_floor L σ hcoeff false ((some a, Signal.endpoint false)::h) n
      have he1 := eval_floor L σ hcoeff true ((some a, Signal.endpoint true)::h) n
      have he := mul_le_mul_of_nonneg_left (add_le_add he0 he1) L.beta_nonneg
      simp only [bayes, div_eq_mul_inv, mul_add, add_mul, ← mul_assoc, sum_add_distrib, ← sum_mul] at hf
      dsimp [b] at *
      linarith
    have hl := mul_le_mul_of_nonneg_left (hc false) (σ h).left_nonneg
    have hr := mul_le_mul_of_nonneg_left (hc true) (σ h).right_nonneg
    have hs := mul_le_mul_of_nonneg_left (ih ((none, Signal.fallback)::h)) (σ h).safe_nonneg
    have hBb : b ≤ B := bound_floor L.beta_le_one n
    have hextra : 0 ≤ (σ h).safe * L.beta * (B-b) :=
      mul_nonneg (mul_nonneg (σ h).safe_nonneg L.beta_nonneg) (sub_nonneg.mpr hBb)
    have ht := (σ h).total
    have him := hscore h
    have hn : (σ h).left*((1-L.beta)*B+L.beta*b) +
        (σ h).right*((1-L.beta)*B+L.beta*b) +
        (σ h).safe*((1-L.beta)*B+L.beta*b) = (1-L.beta)*B+L.beta*b := by
      rw [← add_mul, ← add_mul, ht, one_mul]
    unfold bayes at hs
    rw [bound_succ]
    unfold bayes
    simp only [eval, Policy.risk, Bool.false_eq_true, ↓reduceIte]
    dsimp [B, b] at *
    nlinarith

/-- Corollary 7.2: arbitrary observable-history strategies, with the fallback. -/
theorem fallback_lower {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (h : History ι) (n : ℕ) : bound L.beta n ≤ bayes L σ (1/2) h n := by
  apply bayes_lower L σ (by norm_num)
  intro h
  norm_num

/-- Theorem 7.1: the fallback probability is zero, but all history dependence
and randomized branch choices remain unrestricted. -/
theorem no_fallback_lower {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (hσ : ∀ h, (σ h).safe = 0) (h : History ι) (n : ℕ) :
    bound L.beta n ≤ bayes L σ 0 h n := by
  apply bayes_lower L σ (by norm_num)
  intro h
  rw [hσ h]
  simp


/-- The model index is learned precisely when an endpoint occurs. -/
def knowledge {ι : Type*} : History ι → Option Bool
  | [] => none
  | (_, Signal.endpoint θ) :: _ => some θ
  | _ :: h => knowledge h

def pureBranch (a : Bool) : Policy where
  left := if a then 0 else 1
  right := if a then 1 else 0
  safe := 0
  left_nonneg := by cases a <;> norm_num
  right_nonneg := by cases a <;> norm_num
  safe_nonneg := le_rfl
  total := by cases a <;> norm_num

/-- Explore the left branch until revelation, then always select the good one. -/
def attaining {ι : Type*} : Strategy ι :=
  fun h => pureBranch ((knowledge h).getD false)

theorem attaining_no_fallback {ι : Type*} (h : History ι) : (attaining h).safe = 0 := rfl

theorem attaining_known {ι : Type*} [Fintype ι] (L : FailureLaw ι)
    (coeff : ℝ) (θ : Bool) (h : History ι) (hk : knowledge h = some θ) (n : ℕ) :
    eval L attaining coeff θ h n = -(n : ℝ)/4 := by
  induction n generalizing h with
  | zero => simp [eval]
  | succ n ih =>
    have hf (a : Bool) :
        (∑ i, L.mass i * eval L attaining coeff θ ((some a, Signal.failure i)::h) n) =
          (1-L.beta) * (-(n : ℝ)/4) := by
      have hfi (i : ι) := ih ((some a, Signal.failure i)::h) hk
      simp_rw [hfi]
      rw [← sum_mul, L.total]
    have he (a : Bool) :
        eval L attaining coeff θ ((some a, Signal.endpoint θ)::h) n = -(n : ℝ)/4 :=
      ih _ (by simp [knowledge])
    simp only [eval, hf, he, attaining, hk, Option.getD_some]
    cases θ <;> simp [pureBranch, Policy.risk] <;> ring

theorem attaining_unknown {ι : Type*} [Fintype ι] (L : FailureLaw ι)
    (coeff : ℝ) (h : History ι) (hk : knowledge h = none) (n : ℕ) :
    bayes L attaining coeff h n = bound L.beta n := by
  induction n generalizing h with
  | zero => simp [bayes, eval, bound]
  | succ n ih =>
    have hf :
        ((∑ i, L.mass i * eval L attaining coeff false ((some false, Signal.failure i)::h) n) +
          (∑ i, L.mass i * eval L attaining coeff true ((some false, Signal.failure i)::h) n)) / 2 =
          (1-L.beta) * bound L.beta n := by
      calc
        _ = ∑ i, L.mass i * bayes L attaining coeff ((some false, Signal.failure i)::h) n := by
          simp only [bayes, div_eq_mul_inv, mul_add, add_mul, ← mul_assoc, sum_add_distrib, ← sum_mul]
        _ = ∑ i, L.mass i * bound L.beta n := by
          congr 1
          ext i
          rw [ih _ (by simp [knowledge, hk])]
        _ = _ := by rw [← sum_mul, L.total]
    have he (θ : Bool) :
        eval L attaining coeff θ ((some false, Signal.endpoint θ)::h) n = -(n : ℝ)/4 :=
      attaining_known L coeff θ _ (by simp [knowledge]) n
    rw [bound_succ]
    unfold bayes
    simp only [eval, attaining, hk, Option.getD_none, pureBranch, Policy.risk,
      Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero, one_mul, he]
    linarith

/-- The exact Bayes optimum is proved by a universal lower bound and an
explicit admissible strategy attaining it; it is not an assumed hypothesis. -/
theorem exact_no_fallback_optimum {ι : Type*} [Fintype ι] (L : FailureLaw ι) (n : ℕ) :
    IsLeast {v : ℝ | ∃ σ : Strategy ι, (∀ h, (σ h).safe = 0) ∧
      v = bayes L σ 0 [] n} (bound L.beta n) := by
  constructor
  · exact ⟨attaining, attaining_no_fallback, (attaining_unknown L 0 [] rfl n).symm⟩
  · rintro v ⟨σ, hσ, rfl⟩
    exact no_fallback_lower L σ hσ [] n


/-- Expected reward shortfall: branch reward is one; fallback reward is zero. -/
def rewardRegret {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (θ : Bool) (h : History ι) : ℕ → ℝ
  | 0 => 0
  | n+1 => (σ h).safe +
    (σ h).left * ((∑ i, L.mass i * rewardRegret L σ θ ((some false, Signal.failure i)::h) n) +
      L.beta * rewardRegret L σ θ ((some false, Signal.endpoint θ)::h) n) +
    (σ h).right * ((∑ i, L.mass i * rewardRegret L σ θ ((some true, Signal.failure i)::h) n) +
      L.beta * rewardRegret L σ θ ((some true, Signal.endpoint θ)::h) n) +
    (σ h).safe * rewardRegret L σ θ ((none, Signal.fallback)::h) n

def bayesReward {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (h : History ι) (n : ℕ) : ℝ :=
  (rewardRegret L σ false h n + rewardRegret L σ true h n) / 2

private theorem weighted_affine {ι : Type*} [Fintype ι] (w f g : ι → ℝ) (c : ℝ) :
    (∑ i, w i * (f i + c*g i)) = (∑ i, w i*f i) + c*(∑ i, w i*g i) := by
  simp only [mul_add, sum_add_distrib]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  ring

theorem eval_affine {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (c : ℝ) (θ : Bool) (h : History ι) (n : ℕ) :
    eval L σ c θ h n = eval L σ 0 θ h n + c * rewardRegret L σ θ h n := by
  induction n generalizing h with
  | zero => simp [eval, rewardRegret]
  | succ n ih =>
    simp only [eval, rewardRegret, ih, weighted_affine]
    ring

theorem bayes_affine {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (c : ℝ) (h : History ι) (n : ℕ) :
    bayes L σ c h n = bayes L σ 0 h n + c * bayesReward L σ h n := by
  simp only [bayes, bayesReward, eval_affine L σ c]
  ring

theorem no_fallback_zero_reward {ι : Type*} [Fintype ι] (L : FailureLaw ι)
    (σ : Strategy ι) (hσ : ∀ h, (σ h).safe = 0) (θ : Bool) (h : History ι) (n : ℕ) :
    rewardRegret L σ θ h n = 0 := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => simp [rewardRegret, ih, hσ]

/-- The first two Bonferroni terms, derived by summing Bernoulli's inequality. -/
theorem bound_quadratic {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (n : ℕ) :
    (n : ℝ)/4 * (1 - ((n : ℝ)-1)*β) ≤ bound β n := by
  have hs : (n : ℝ) - (n : ℝ)*((n : ℝ)-1)*β/2 ≤ ∑ j ∈ range n, (1-β)^j := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hp : 1 - (n : ℝ)*β ≤ (1-β)^n := by
        simpa only [sub_eq_add_neg, mul_neg] using
          one_add_mul_le_pow (a := -β) (by linarith : -2 ≤ -β) n
      rw [sum_range_succ]
      push_cast
      nlinarith
  unfold bound
  nlinarith

/-- The paper's episode count uses the natural floor. -/
def K0 (β : ℝ) : ℕ := ⌊1/(2*β)⌋₊

theorem K0_bounds {β : ℝ} (hβ : 0 < β) (hβ4 : β ≤ 1/4) :
    1/(4*β) ≤ (K0 β : ℝ) ∧ (K0 β : ℝ)*β ≤ 1/2 := by
  have hp : 0 < 2*β := by positivity
  have hf := Nat.floor_le (show 0 ≤ 1/(2*β) by positivity)
  have hg := Nat.lt_floor_add_one (1/(2*β))
  change (K0 β : ℝ) ≤ 1/(2*β) at hf
  change 1/(2*β) < (K0 β : ℝ)+1 at hg
  have hfm := (le_div_iff₀ hp).mp hf
  have hgm := mul_lt_mul_of_pos_right hg hp
  have hc : (1/(2*β))*(2*β) = 1 := by field_simp
  rw [hc] at hgm
  constructor
  · apply (div_le_iff₀ (show 0 < 4*β by positivity)).2
    nlinarith
  · nlinarith

theorem tailored_bound {β : ℝ} (hβ : 0 < β) (hβ4 : β ≤ 1/4) :
    1/(32*β) ≤ bound β (K0 β) := by
  obtain ⟨hlarge, hsmall⟩ := K0_bounds hβ hβ4
  have hquad := bound_quadratic hβ.le (by linarith : β ≤ 1) (K0 β)
  have hn : 0 ≤ (K0 β : ℝ) := Nat.cast_nonneg _
  have hfactor : 1/2 ≤ 1-((K0 β : ℝ)-1)*β := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hfactor (show 0 ≤ (K0 β : ℝ)/4 by positivity)
  have hdiv : 1/(32*β) = (1/(4*β))/8 := by field_simp; ring
  rw [hdiv]
  nlinarith

/-- Equations (7.1)--(7.2), with no Bayes-optimality premise. -/
theorem no_fallback_tailored {ι : Type*} [Fintype ι] (L : FailureLaw ι)
    (σ : Strategy ι) (hσ : ∀ h, (σ h).safe = 0)
    (hβ : 0 < L.beta) (hβ4 : L.beta ≤ 1/4) :
    1/(32*L.beta) ≤ bayes L σ 0 [] (K0 L.beta) :=
  (tailored_bound hβ hβ4).trans (no_fallback_lower L σ hσ [] _)

/-- Equation (7.3), expressed in separate reward and signed risk debts. -/
theorem fallback_tradeoff {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (n : ℕ) : bound L.beta n ≤ bayes L σ 0 [] n + (1/2)*bayesReward L σ [] n := by
  rw [← bayes_affine]
  exact fallback_lower L σ [] n

/-- The coefficient tradeoff (7.4) follows at the single tailored count. -/
theorem pareto_coefficients {β F G : ℝ} (hβ : 0 < β) (hβ4 : β ≤ 1/4)
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (h : 1/(32*β) ≤ G + (1/2)*F*Real.sqrt (K0 β : ℝ)) :
    1/(64*β) ≤ G ∨ Real.sqrt 2/(32*Real.sqrt β) ≤ F := by
  by_cases hg : 1/(64*β) ≤ G
  · exact Or.inl hg
  · right
    have hsmall := (K0_bounds hβ hβ4).2
    have hsq := Real.sq_sqrt (show 0 ≤ (K0 β : ℝ) by positivity)
    have hsβ := Real.sq_sqrt hβ.le
    have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hsp := Real.sqrt_pos.2 hβ
    have hs0 := Real.sqrt_nonneg (K0 β : ℝ)
    have hs20 := Real.sqrt_nonneg (2:ℝ)
    have hg' : G < 1/(64*β) := lt_of_not_ge hg
    have hprod : 1/(64*β) < (1/2)*F*Real.sqrt (K0 β : ℝ) := by
      have heq : 1/(32*β) = 2*(1/(64*β)) := by field_simp; ring
      linarith
    have hc : 1/(64*β) * (64*β) = 1 := by field_simp
    have hprod' := mul_lt_mul_of_pos_right hprod (show 0 < 64*β by positivity)
    rw [hc] at hprod'
    apply (div_le_iff₀ (show 0 < 32*Real.sqrt β by positivity)).2
    by_contra hn
    have hn' : F*(32*Real.sqrt β) < Real.sqrt 2 := lt_of_not_ge hn
    have hab : 0 ≤ F*(32*Real.sqrt β) := by positivity
    have hsprod : (Real.sqrt (K0 β : ℝ) * Real.sqrt β)^2 ≤ 1/2 := by
      rw [mul_pow, hsq, hsβ]
      exact hsmall
    have hroot : Real.sqrt (K0 β : ℝ)*Real.sqrt β ≤ Real.sqrt 2/2 := by
      nlinarith only [hsprod, hs2, mul_nonneg hs0 hsp.le, hs20]
    have hcmp := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ 32*F*Real.sqrt β by positivity)
    have hident : 32*F*Real.sqrt β*(Real.sqrt (K0 β : ℝ)*Real.sqrt β) =
        32*F*Real.sqrt (K0 β : ℝ)*β := by
      calc
        _ = 32*F*Real.sqrt (K0 β : ℝ)*(Real.sqrt β)^2 := by ring
        _ = _ := by rw [hsβ]
    rw [hident] at hcmp
    have hn2 := mul_lt_mul_of_pos_right hn' (show 0 < Real.sqrt 2 by positivity)
    nlinarith only [hprod', hcmp, hn2, hs2]


/-- Survival of the first `n` rare transitions (heterogeneous Remark F.1). -/
def survival (a : ℕ → ℝ) (n : ℕ) : ℝ := ∏ j ∈ range n, a j

theorem failure_mass_total (a : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ range n, survival a j * (1-a j)) = 1-survival a n := by
  induction n with
  | zero => simp [survival]
  | succ n ih =>
    rw [sum_range_succ, ih]
    simp only [survival, prod_range_succ]
    ring

/-- The failure signal records the exact first failure depth, not just a binary
success/failure observation.  Its distribution is identical in both models. -/
def heterogeneousLaw (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1) (n : ℕ) :
    FailureLaw (Fin n) where
  beta := survival a n
  beta_nonneg := prod_nonneg fun j _ => (ha j).1
  beta_le_one := by
    apply prod_le_one
    · intro j _; exact (ha j).1
    · intro j _; exact (ha j).2
  mass := fun j => survival a j * (1-a j)
  mass_nonneg := fun j => mul_nonneg (prod_nonneg fun k _ => (ha k).1) (by linarith [(ha j).2])
  total := by
    simpa only [← Fin.sum_univ_eq_sum_range] using failure_mass_total a n

def homogeneousLaw (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) : FailureLaw (Fin n) :=
  heterogeneousLaw (fun _ => α) (fun _ => ⟨hα, hα1⟩) n

theorem homogeneous_beta (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) :
    (homogeneousLaw α hα hα1 n).beta = α^n := by
  simp [homogeneousLaw, heterogeneousLaw, survival]

theorem rare_hazard_quarter {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 1/2)
    {H : ℕ} (hH : 3 ≤ H) : α^(H-1) ≤ 1/4 := by
  have hn : 2 ≤ H-1 := by omega
  have hp := pow_le_pow_of_le_one hα (show α ≤ 1 by linarith) hn
  have hs : α^2 ≤ (1/2 : ℝ)^2 := pow_le_pow_left₀ hα hα2 2
  norm_num at hs
  exact hp.trans hs

/-- The homogeneous exponent in Theorem 7.1 is obtained from actual independent
rare-step hazards, and not introduced as an unrelated parameter. -/
theorem homogeneous_tailored {α : ℝ} (hα : 0 < α) (hα2 : α ≤ 1/2)
    {H : ℕ} (hH : 3 ≤ H) (σ : Strategy (Fin (H-1)))
    (hσ : ∀ h, (σ h).safe = 0) :
    1/(32*α^(H-1)) ≤
      bayes (homogeneousLaw α hα.le (by linarith) (H-1)) σ 0 [] (K0 (α^(H-1))) := by
  let L := homogeneousLaw α hα.le (show α ≤ 1 by linarith) (H-1)
  have heq : L.beta = α^(H-1) := homogeneous_beta _ _ _ _
  have hh := no_fallback_tailored L σ hσ (by rw [heq]; positivity)
    (by rw [heq]; exact rare_hazard_quarter hα.le hα2 hH)
  simpa only [heq] using hh


/-- The exact likelihood of one observable episode in the rare-chain experiment.
Failure depths are public; an endpoint and the known branch encode the model. -/
def stepMass {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (θ : Bool) (h : History ι) : Option Bool × Signal ι → ℝ
  | (some a, Signal.failure i) => (if a then (σ h).right else (σ h).left) * L.mass i
  | (some a, Signal.endpoint t) =>
      if t = θ then (if a then (σ h).right else (σ h).left) * L.beta else 0
  | (none, Signal.fallback) => (σ h).safe
  | _ => 0

def pathMass {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (θ : Bool) : History ι → ℝ
  | [] => 1
  | e :: h => pathMass L σ θ h * stepMass L σ θ h e

def NoEndpoint {ι : Type*} (h : History ι) : Prop :=
  ∀ (e : Option Bool × Signal ι), e ∈ h → ∀ θ, e.2 ≠ Signal.endpoint θ

/-- The uniform posterior before revelation is a likelihood theorem, proved for
an arbitrary strategy rather than assumed in the lower-bound argument. -/
theorem identical_unrevealed_likelihood {ι : Type*} [Fintype ι] (L : FailureLaw ι)
    (σ : Strategy ι) (h : History ι) (hu : NoEndpoint h) :
    pathMass L σ false h = pathMass L σ true h := by
  induction h with
  | nil => rfl
  | cons e h ih =>
    have hh : NoEndpoint h := by
      intro d hd t
      exact hu d (List.mem_cons_of_mem e hd) t
    have he : ∀ t, e.2 ≠ Signal.endpoint t := fun t => hu e (List.mem_cons_self) t
    simp only [pathMass, ih hh]
    congr 1
    obtain ⟨a, sig⟩ := e
    cases a <;> cases sig <;> simp_all [stepMass]

theorem uniform_posterior {ι : Type*} [Fintype ι] (L : FailureLaw ι)
    (σ : Strategy ι) (h : History ι) (hu : NoEndpoint h)
    (hp : 0 < pathMass L σ false h) :
    ((1/2)*pathMass L σ false h) /
      ((1/2)*pathMass L σ false h + (1/2)*pathMass L σ true h) = 1/2 := by
  rw [← identical_unrevealed_likelihood L σ h hu]
  field_simp
  <;> nlinarith

/-- Observing the endpoint rules out the other latent model. -/
theorem endpoint_identifies {ι : Type*} [Fintype ι] (L : FailureLaw ι)
    (σ : Strategy ι) (a t θ : Bool) (hne : t ≠ θ) (h : History ι) :
    pathMass L σ θ ((some a, Signal.endpoint t)::h) = 0 := by
  simp [pathMass, stepMass, hne]

/-- Probability of surviving without identification for `n` whole episodes. -/
def unrevealed {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (h : History ι) : ℕ → ℝ
  | 0 => 1
  | n+1 =>
      (σ h).left * (∑ i, L.mass i * unrevealed L σ ((some false, Signal.failure i)::h) n) +
      (σ h).right * (∑ i, L.mass i * unrevealed L σ ((some true, Signal.failure i)::h) n) +
      (σ h).safe * unrevealed L σ ((none, Signal.fallback)::h) n

theorem no_fallback_geometric_survival {ι : Type*} [Fintype ι] (L : FailureLaw ι)
    (σ : Strategy ι) (hσ : ∀ h, (σ h).safe = 0) (h : History ι) (n : ℕ) :
    unrevealed L σ h n = (1-L.beta)^n := by
  induction n generalizing h with
  | zero => simp [unrevealed]
  | succ n ih =>
    simp only [unrevealed, ih, ← sum_mul, L.total, hσ, zero_mul, add_zero]
    have ht := (σ h).total
    rw [hσ h, add_zero] at ht
    rw [← add_mul, ht, one_mul, pow_succ]
    ring

theorem fallback_geometric_survival {ι : Type*} [Fintype ι] (L : FailureLaw ι)
    (σ : Strategy ι) (h : History ι) (n : ℕ) :
    (1-L.beta)^n ≤ unrevealed L σ h n := by
  induction n generalizing h with
  | zero => simp [unrevealed]
  | succ n ih =>
    have hl := weighted_floor L _ ((1-L.beta)^n)
      (fun i => ih ((some false, Signal.failure i)::h))
    have hr := weighted_floor L _ ((1-L.beta)^n)
      (fun i => ih ((some true, Signal.failure i)::h))
    have hl' := mul_le_mul_of_nonneg_left hl (σ h).left_nonneg
    have hr' := mul_le_mul_of_nonneg_left hr (σ h).right_nonneg
    have hs := mul_le_mul_of_nonneg_left (ih ((none, Signal.fallback)::h)) (σ h).safe_nonneg
    have hp : 0 ≤ (1-L.beta)^n := pow_nonneg (by linarith [L.beta_le_one]) n
    have hex : 0 ≤ (σ h).safe*L.beta*((1-L.beta)^n) :=
      mul_nonneg (mul_nonneg (σ h).safe_nonneg L.beta_nonneg) hp
    have hn : (σ h).left*((1-L.beta)*((1-L.beta)^n)) +
        (σ h).right*((1-L.beta)*((1-L.beta)^n)) +
        (σ h).safe*((1-L.beta)*((1-L.beta)^n)) = (1-L.beta)*((1-L.beta)^n) := by
      rw [← add_mul, ← add_mul, (σ h).total, one_mul]
    rw [unrevealed, pow_succ]
    nlinarith


/-- The finite-horizon Bayes optimum in the exact closed form (7.1). -/
theorem exact_no_fallback_closed {ι : Type*} [Fintype ι] (L : FailureLaw ι)
    (hβ : 0 < L.beta) (n : ℕ) :
    IsLeast {v : ℝ | ∃ σ : Strategy ι, (∀ h, (σ h).safe = 0) ∧
      v = bayes L σ 0 [] n}
      ((1-(1-L.beta)^n)/(2*L.beta)-(n : ℝ)/4) := by
  rw [← bound_closed hβ n]
  exact exact_no_fallback_optimum L n

/-- Corollary 7.2 in its full all-episode coefficient quantifiers for every
strategy of the observable experiment. -/
theorem fallback_pareto {ι : Type*} [Fintype ι] (L : FailureLaw ι) (σ : Strategy ι)
    (hβ : 0 < L.beta) (hβ4 : L.beta ≤ 1/4) {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hr : ∀ n, bayesReward L σ [] n ≤ F*Real.sqrt (n : ℝ))
    (hρ : ∀ n, bayes L σ 0 [] n ≤ G) :
    1/(64*L.beta) ≤ G ∨ Real.sqrt 2/(32*Real.sqrt L.beta) ≤ F := by
  apply pareto_coefficients hβ hβ4 hF hG
  have hl := (tailored_bound hβ hβ4).trans (fallback_tradeoff L σ (K0 L.beta))
  have hrr := hr (K0 L.beta)
  have hρρ := hρ (K0 L.beta)
  linarith

end
end Paper36.LowerBound
