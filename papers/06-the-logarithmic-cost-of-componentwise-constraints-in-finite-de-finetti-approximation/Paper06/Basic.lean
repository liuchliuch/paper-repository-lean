/-
Copyright (c) 2026. Finite-alphabet probability, relative entropy, products
and mixtures used by "The logarithmic cost of componentwise constraints in
finite de Finetti approximation".
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Fin

open Real Set BigOperators
open scoped Classical

namespace Paper06

/-- A probability mass function on a finite type. -/
structure FinProb (α : Type*) [Fintype α] where
  w : α → ℝ
  nonneg : ∀ y, 0 ≤ w y
  sum_eq_one : ∑ y, w y = 1

namespace FinProb

variable {α : Type*} [Fintype α]

/-- Expectation of a statistic. -/
def expect (p : FinProb α) (f : α → ℝ) : ℝ := ∑ y, p.w y * f y

/-- Pointwise equality of mass functions implies equality of laws. -/
theorem ext {p q : FinProb α} (h : ∀ y, p.w y = q.w y) : p = q := by
  cases p; cases q; congr 1; exact funext h

theorem w_nonneg (p : FinProb α) (y : α) : 0 ≤ p.w y := p.nonneg y

/-- The real finite-sum part of relative entropy. Use `FinProb.kl` from
`Divergence` for the paper’s divergence, which is infinite on support mismatch. -/
noncomputable def klPos (p q : FinProb α) : ℝ :=
  ∑ y, p.w y * log (p.w y / q.w y)

/-- Entropy of `p`: `H(p) = -∑ y, p y log p y`. -/
noncomputable def entropy (p : FinProb α) : ℝ :=
  - ∑ y, p.w y * log (p.w y)

/-- Chain rule for relative entropy on a finite alphabet with full support. -/
theorem klPos_chain_rule {p q r : FinProb α}
    (hq : ∀ y, 0 < q.w y) (hr : ∀ y, 0 < r.w y) :
    klPos p r = klPos p q + expect p (fun y => log (q.w y / r.w y)) := by
  show ∑ y, p.w y * log (p.w y / r.w y)
      = ∑ y, p.w y * log (p.w y / q.w y) + ∑ y, p.w y * log (q.w y / r.w y)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hp0 : p.w y = 0
  · simp [hp0]
  · have hp_pos : 0 < p.w y := lt_of_le_of_ne (p.nonneg y) (Ne.symm hp0)
    have hdiv : p.w y / r.w y = (p.w y / q.w y) * (q.w y / r.w y) := by
      have hq0 : q.w y ≠ 0 := ne_of_gt (hq y)
      have hr0 : r.w y ≠ 0 := ne_of_gt (hr y)
      field_simp [hq0, hr0, mul_comm, mul_left_comm, mul_assoc]
    rw [hdiv, log_mul (ne_of_gt (div_pos hp_pos (hq y)))
        (ne_of_gt (div_pos (hq y) (hr y))), mul_add]

/-- Gibbs' inequality: `D(p‖q) ≥ 0` when `q` has full support. -/
theorem klPos_nonneg {p q : FinProb α} (hq : ∀ y, 0 < q.w y) :
    0 ≤ klPos p q := by
  show 0 ≤ ∑ y, p.w y * log (p.w y / q.w y)
  have hpoint : ∀ y, p.w y - q.w y ≤ p.w y * log (p.w y / q.w y) := by
    intro y
    by_cases hp0 : p.w y = 0
    · have hz : (0 : ℝ) * log (0 / q.w y) = 0 := by rw [zero_mul]
      rw [hp0, hz]
      have : 0 ≤ q.w y := le_of_lt (hq y)
      linarith
    · have hp : 0 < p.w y := lt_of_le_of_ne (p.nonneg y) (Ne.symm hp0)
      have hlog : log (p.w y / q.w y) = - log (q.w y / p.w y) := by
        rw [log_div (ne_of_gt hp) (ne_of_gt (hq y)),
            log_div (ne_of_gt (hq y)) (ne_of_gt hp)]
        ring
      have hqlog : log (q.w y / p.w y) ≤ (q.w y / p.w y) - 1 :=
        log_le_sub_one_of_pos (div_pos (hq y) hp)
      have hge : 1 - q.w y / p.w y ≤ log (p.w y / q.w y) := by
        rw [hlog]
        linarith
      have hmul : p.w y * (1 - q.w y / p.w y) ≤ p.w y * log (p.w y / q.w y) :=
        mul_le_mul_of_nonneg_left hge (le_of_lt hp)
      have hcancel : p.w y * (1 - q.w y / p.w y) = p.w y - q.w y := by
        rw [mul_sub, mul_one, mul_div_cancel₀ _ (ne_of_gt hp)]
      rw [← hcancel]
      exact hmul
  have hsum : ∑ y, (p.w y - q.w y) ≤ ∑ y, p.w y * log (p.w y / q.w y) :=
    Finset.sum_le_sum (fun y _ => hpoint y)
  have hsum0 : ∑ y, (p.w y - q.w y) = 0 := by
    rw [Finset.sum_sub_distrib, p.sum_eq_one, q.sum_eq_one, sub_self]
  linarith

/-- Full support of a law. -/
def FullSupport (p : FinProb α) : Prop := ∀ y, 0 < p.w y

theorem fullSupport_pos {p : FinProb α} (hp : FullSupport p) (y : α) :
    0 < p.w y := hp y

end FinProb

/-! ### Product laws on `Fin k → α` -/

/-- Product mass function of `q` on `Fin k → α`. -/
noncomputable def productW {α : Type*} [Fintype α] (k : ℕ) (q : FinProb α) :
    (Fin k → α) → ℝ :=
  fun z => ∏ i : Fin k, q.w (z i)

theorem productW_nonneg {α : Type*} [Fintype α] (k : ℕ) (q : FinProb α)
    (z : Fin k → α) : 0 ≤ productW k q z :=
  Finset.prod_nonneg (fun _ _ => q.nonneg _)

/-- Split the product mass at the head coordinate. -/
theorem productW_succ {α : Type*} [Fintype α] (k : ℕ) (q : FinProb α)
    (z : Fin (k + 1) → α) :
    productW (k + 1) q z = q.w (z 0) * productW k q (fun i => z i.succ) := by
  unfold productW
  exact Fin.prod_univ_succ _

/-- Equivalence between `α × (Fin k → α)` and `Fin (k+1) → α`. -/
def consEquiv (α : Type*) (k : ℕ) : (α × (Fin k → α)) ≃ (Fin (k + 1) → α) :=
{ toFun := fun x => Fin.cons x.1 x.2
  invFun := fun z => (z 0, fun i => z i.succ)
  left_inv := by
    intro x
    cases x with
    | mk a zs =>
      simp [Fin.cons_zero, Fin.cons_succ]
  right_inv := by
    intro z
    funext i
    by_cases hi : i.val = 0
    · have h0 : i = 0 := Fin.eq_of_val_eq hi
      subst h0
      simp
    · have hpos : 0 < i.val := Nat.pos_of_ne_zero hi
      have hex : ∃ j : Fin k, i = j.succ := by
        have hex' : ∃ j : ℕ, i.val = j + 1 ∧ j < k :=
          ⟨i.val - 1, ⟨by omega, by omega⟩⟩
        obtain ⟨j, hj1, hj2⟩ := hex'
        exact ⟨⟨j, hj2⟩, Fin.ext (by simpa using hj1)⟩
      obtain ⟨j, rfl⟩ := hex
      simp }

theorem consEquiv_apply {α : Type*} {k : ℕ} (x : α × (Fin k → α)) :
    consEquiv α k x = Fin.cons x.1 x.2 := rfl

/-- Product of `k` copies of `q` sums to one. -/
theorem productW_sum_one {α : Type*} [Fintype α] (k : ℕ) (q : FinProb α) :
    ∑ z : Fin k → α, productW k q z = 1 := by
  classical
  induction k with
  | zero =>
    show ∑ z : Fin 0 → α, productW 0 q z = 1
    simp [productW]
  | succ k ih =>
    have hcomp : ∑ z : Fin (k+1) → α, productW (k+1) q z
        = ∑ x : α × (Fin k → α), productW (k+1) q (consEquiv α k x) := by
      refine Finset.sum_bij (fun z _ => (consEquiv α k).symm z) ?_ ?_ ?_ ?_
      · intro z _; exact Finset.mem_univ _
      · intro z₁ z₂ _ _ h; exact (consEquiv α k).symm.injective h
      · intro x _
        exact ⟨consEquiv α k x, Finset.mem_univ _,
          (consEquiv α k).symm_apply_apply x⟩
      · intro z _
        rw [(consEquiv α k).apply_symm_apply z]
    have hre : ∑ z : Fin (k+1) → α, productW (k+1) q z
        = ∑ a : α, ∑ zs : Fin k → α, q.w a * productW k q zs :=
      calc ∑ z : Fin (k+1) → α, productW (k+1) q z
          = ∑ x : α × (Fin k → α), productW (k+1) q (consEquiv α k x) := hcomp
        _ = ∑ x : α × (Fin k → α), q.w x.1 * productW k q x.2 := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [consEquiv_apply, productW_succ]
            simp
        _ = ∑ a : α, ∑ zs : Fin k → α, q.w a * productW k q zs :=
            Fintype.sum_prod_type' (fun a zs => q.w a * productW k q zs)
    have key : ∑ z : Fin (k+1) → α, productW (k+1) q z
        = (∑ a : α, q.w a) * ∑ zs : Fin k → α, productW k q zs := by
      rw [hre]
      have hmul : ∀ a : α, ∑ zs : Fin k → α, q.w a * productW k q zs
          = q.w a * ∑ zs : Fin k → α, productW k q zs := by
        intro a
        rw [← Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun a _ => hmul a), Finset.sum_mul]
    rw [key, q.sum_eq_one, one_mul, ih]

/-- Product law `q^{⊗ k}` on `Fin k → α`. -/
noncomputable def productFinProb {α : Type*} [Fintype α] (k : ℕ) (q : FinProb α) :
    FinProb (Fin k → α) where
  w := productW k q
  nonneg := productW_nonneg k q
  sum_eq_one := productW_sum_one k q

theorem productFinProb_w {α : Type*} [Fintype α] (k : ℕ) (q : FinProb α)
    (z : Fin k → α) : (productFinProb k q).w z = ∏ i, q.w (z i) := rfl

/-- Product of two independent laws on a product type. -/
noncomputable def prod {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb α) (q : FinProb β) : FinProb (α × β) where
  w z := p.w z.1 * q.w z.2
  nonneg := by
    intro z
    exact mul_nonneg (p.nonneg _) (q.nonneg _)
  sum_eq_one := by
    classical
    have key : ∑ x : α × β, p.w x.1 * q.w x.2
        = ∑ x : α, ∑ y : β, p.w x * q.w y :=
      Fintype.sum_prod_type' (fun x y => p.w x * q.w y)
    rw [key]
    have hinner : ∀ x : α, ∑ y : β, p.w x * q.w y
        = p.w x * ∑ y : β, q.w y :=
      fun x => (Finset.mul_sum (Finset.univ) (fun y => q.w y) (p.w x)).symm
    rw [Finset.sum_congr rfl (fun x _ => hinner x)]
    rw [q.sum_eq_one]
    show ∑ x : α, p.w x * 1 = 1
    simp only [mul_one, p.sum_eq_one]

theorem prod_w {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb α) (q : FinProb β) (z : α × β) :
    (prod p q).w z = p.w z.1 * q.w z.2 := rfl

/-- A finite mixture `∑ j, w j • q j` of laws. -/
noncomputable def mixture {α ι : Type*} [Fintype α] [Fintype ι]
    (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (q : ι → FinProb α) : FinProb α where
  w y := ∑ j, w j * (q j).w y
  nonneg := by
    intro y
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) ((q j).nonneg y))
  sum_eq_one := by
    classical
    show ∑ y, (∑ j, w j * (q j).w y) = 1
    rw [Finset.sum_comm]
    have hinner : ∀ j : ι, ∑ y : α, w j * (q j).w y
        = w j * ∑ y : α, (q j).w y :=
      fun j => (Finset.mul_sum (Finset.univ) (fun y => (q j).w y) (w j)).symm
    rw [Finset.sum_congr rfl (fun j _ => hinner j)]
    have hq : ∀ j : ι, ∑ y : α, (q j).w y = 1 := fun j => (q j).sum_eq_one
    rw [Finset.sum_congr rfl (fun j _ => by rw [hq j, mul_one])]
    exact hw1

theorem mixture_w {α ι : Type*} [Fintype α] [Fintype ι]
    (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (q : ι → FinProb α) (y : α) :
    (mixture w hw hw1 q).w y = ∑ j, w j * (q j).w y := rfl

/-! ### Mixtures of product laws -/

/-- `M_{k,μ}` for a finite mixing distribution `μ` on laws over `α`. -/
noncomputable def mixtureProduct {α ι : Type*} [Fintype α] [Fintype ι]
    (k : ℕ) (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (q : ι → FinProb α) : FinProb (Fin k → α) :=
  mixture w hw hw1 (fun j => productFinProb k (q j))

theorem mixtureProduct_w {α ι : Type*} [Fintype α] [Fintype ι]
    (k : ℕ) (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (q : ι → FinProb α) (z : Fin k → α) :
    (mixtureProduct k w hw hw1 q).w z = ∑ j, w j * ∏ i, (q j).w (z i) :=
  rfl

/-! ### Bernoulli relative entropy -/

/-- Relative entropy of Bernoulli laws: `d_Ber(p‖q)`. -/
noncomputable def dBer (p q : ℝ) : ℝ :=
  (if p = 0 then 0 else p * log (p / q)) +
  (if p = 1 then 0 else (1 - p) * log ((1 - p) / (1 - q)))

theorem dBer_eq (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) (_hq : 0 < q) (_hq1 : q < 1) :
    dBer p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := by
  simp [dBer, hp.ne', (ne_of_lt hp1)]

/-- Auxiliary: `(1-p) log(1-p) ≥ -p` for `0 < p < 1`. -/
theorem one_sub_p_log (p : ℝ) (_hp : 0 < p) (hp1 : p < 1) :
    (1 - p) * log (1 - p) ≥ -p := by
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  have hlog : log (1 - p) ≥ 1 - 1 / (1 - p) := by
    have hlt : 0 < 1 / (1 - p) := by positivity
    have h1 : log (1 / (1 - p)) = - log (1 - p) := by
      rw [log_div (by norm_num) (ne_of_gt h1p), log_one, zero_sub]
    have h2 : log (1 / (1 - p)) ≤ 1 / (1 - p) - 1 :=
      log_le_sub_one_of_pos hlt
    linarith
  have hmul : (1 - p) * (1 - 1 / (1 - p)) = (1 - p) - 1 := by
    rw [mul_sub, mul_one, mul_div_cancel₀ _ (ne_of_gt h1p)]
  have hthis : (1 - p) * log (1 - p) ≥ (1 - p) * (1 - 1 / (1 - p)) :=
    mul_le_mul_of_nonneg_left hlog (le_of_lt h1p)
  rw [hmul] at hthis
  -- `hthis : (1-p) * log(1-p) ≥ (1-p) - 1`, and `(1-p) - 1 = -p`
  have hcalc : (1 - p) - 1 = -p := by ring
  rw [hcalc] at hthis
  exact hthis

/-- Binary data-processing witness: for `0 < q ≤ p < 1`,
`d_Ber(p‖q) ≥ p log (p/(e q))`. -/
theorem dBer_ge_p_log (p q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hp : q ≤ p) (hp1 : p < 1) (hp0 : 0 < p) :
    dBer p q ≥ p * log (p / (Real.exp 1 * q)) := by
  have hd : dBer p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) :=
    dBer_eq p q hp0 hp1 hq hq1
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have hdiv_ge : (1 - p) / (1 - q) ≥ 1 - p := by
    have hinv : (1 : ℝ) / (1 - q) ≥ 1 := one_le_div₀ h1q |>.mpr (by linarith)
    calc (1 - p) / (1 - q) = (1 - p) * (1 / (1 - q)) := by ring
      _ ≥ (1 - p) * 1 := mul_le_mul_of_nonneg_left hinv (le_of_lt h1p)
      _ = 1 - p := mul_one _
  have hlog_ge : log ((1 - p) / (1 - q)) ≥ log (1 - p) :=
    log_le_log (by linarith) hdiv_ge
  have h2 : (1 - p) * log ((1 - p) / (1 - q)) ≥ -p := by
    have hpow := one_sub_p_log p hp0 hp1
    have hmul' : (1 - p) * log ((1 - p) / (1 - q)) ≥ (1 - p) * log (1 - p) :=
      mul_le_mul_of_nonneg_left hlog_ge (le_of_lt h1p)
    linarith
  have h1 : p * log (p / q) = p * log (p / (Real.exp 1 * q)) + p := by
    have hdiv : p / q = (p / (Real.exp 1 * q)) * Real.exp 1 := by
      field_simp
    have hexp : Real.exp 1 ≠ 0 := by positivity
    have hpeq : p / (Real.exp 1 * q) ≠ 0 := by
      exact div_ne_zero (ne_of_gt hp0) (by positivity)
    rw [hdiv, log_mul hpeq hexp, mul_add, Real.log_exp, mul_one]
  rw [hd, h1]
  have hsum : p + (1 - p) * log ((1 - p) / (1 - q)) ≥ 0 := by linarith
  linarith

end Paper06
