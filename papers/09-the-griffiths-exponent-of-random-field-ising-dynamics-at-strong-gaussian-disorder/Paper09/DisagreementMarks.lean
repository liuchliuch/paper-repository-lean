import Paper09.Coupling
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open Finset BigOperators Classical
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

namespace Paper09

/-- An actual finite joint distribution with two spin marginals and a mark marginal. -/
structure MarkedCoupling {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinProb α) (q : FinProb β) (m : FinProb γ) where
  mass : α → β → γ → ℝ
  nonneg : ∀ a b ω, 0 ≤ mass a b ω
  left : ∀ a, ∑ b, ∑ ω, mass a b ω = p.w a
  right : ∀ b, ∑ a, ∑ ω, mass a b ω = q.w b
  mark : ∀ ω, ∑ a, ∑ b, mass a b ω = m.w ω

namespace FinProb
variable {α β : Type*} [Fintype α] [Fintype β]

/-- Independent product of two finite laws. -/
def prod (p : FinProb α) (q : FinProb β) : FinProb (α × β) where
  w z := p.w z.1 * q.w z.2
  nonneg z := mul_nonneg (p.nonneg _) (q.nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, q.sum_one, mul_one]
    exact p.sum_one

/-- Exact finite pushforward, formed by summing the masses in each fiber. -/
def map (p : FinProb α) (f : α → β) : FinProb β where
  w b := ∑ a, if f a = b then p.w a else 0
  nonneg b := sum_nonneg fun a _ => by split_ifs <;> simp_all [p.nonneg]
  sum_one := by rw [sum_comm]; simpa using p.sum_one

/-- Expectation under an actual finite pushforward. -/
theorem expect_map (p : FinProb α) (φ : α → β) (f : β → ℝ) :
    (p.map φ).expect f = p.expect (fun a => f (φ a)) := by
  simp only [expect, map, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp [ite_mul]

/-- Iterated expectation for the actual independent finite product law. -/
theorem expect_prod (p : FinProb α) (q : FinProb β) (f : α × β → ℝ) :
    (p.prod q).expect f = p.expect (fun a => q.expect (fun b => f (a, b))) := by
  simp only [expect, prod, Fintype.sum_prod_type, mul_sum, mul_assoc]

/-- Finite laws are equal when their actual masses agree. -/
theorem ext_weights (p q : FinProb α) (h : ∀ a, p.w a = q.w a) : p = q := by
  cases p with
  | mk pw pn ps =>
    cases q with
    | mk qw qn qs =>
      have he : pw = qw := funext h
      cases he
      rfl

end FinProb

private theorem sum_four_swap {ι κ χ μ : Type*}
    [Fintype ι] [Fintype κ] [Fintype χ] [Fintype μ] (f : ι → κ → χ → μ → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  simpa only [Fintype.sum_prod_type] using
    (sum_comm (s := (univ : Finset (ι × κ))) (t := (univ : Finset (χ × μ)))
      (f := fun ij kl => f ij.1 ij.2 kl.1 kl.2))

namespace MarkedCoupling
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable {p : FinProb α} {q : FinProb β} {m : FinProb γ}

/-- Sample an ordinary coupling independently of the mark. -/
def independentProduct (c : Coupling p q) (m : FinProb γ) : MarkedCoupling p q m where
  mass a b ω := c.mass a b * m.w ω
  nonneg a b ω := mul_nonneg (c.nonneg a b) (m.nonneg ω)
  left a := by simp_rw [← mul_sum, m.sum_one, mul_one]; exact c.row a
  right b := by simp_rw [← mul_sum, m.sum_one, mul_one]; exact c.col b
  mark ω := by simp_rw [← sum_mul, c.row]; rw [p.sum_one, one_mul]

/-- Forget the mark, leaving a genuine coupling of the two given laws. -/
def toCoupling (c : MarkedCoupling p q m) : Coupling p q where
  mass a b := ∑ ω, c.mass a b ω
  nonneg a b := sum_nonneg fun ω _ => c.nonneg a b ω
  row := c.left
  col := c.right

/-- The joint law on the three finite coordinates. -/
def joint (c : MarkedCoupling p q m) : FinProb (α × β × γ) where
  w z := c.mass z.1 z.2.1 z.2.2
  nonneg z := c.nonneg _ _ _
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, c.left]
    exact p.sum_one


/-- A zero first marginal makes every corresponding joint entry vanish. -/
theorem mass_eq_zero_of_left (c : MarkedCoupling p q m) {a : α}
    (ha : p.w a = 0) (b : β) (ω : γ) : c.mass a b ω = 0 := by
  have hle : c.mass a b ω ≤ ∑ b, ∑ ω, c.mass a b ω :=
    (single_le_sum (fun ω _ => c.nonneg a b ω) (mem_univ ω)).trans
      (single_le_sum (fun b _ => sum_nonneg fun ω _ => c.nonneg a b ω) (mem_univ b))
  rw [c.left, ha] at hle
  exact le_antisymm hle (c.nonneg _ _ _)

/-- A zero second marginal makes every corresponding joint entry vanish. -/
theorem mass_eq_zero_of_right (c : MarkedCoupling p q m) {b : β}
    (hb : q.w b = 0) (a : α) (ω : γ) : c.mass a b ω = 0 := by
  have hle : c.mass a b ω ≤ ∑ a, ∑ ω, c.mass a b ω :=
    (single_le_sum (fun ω _ => c.nonneg a b ω) (mem_univ ω)).trans
      (single_le_sum (fun a _ => sum_nonneg fun ω _ => c.nonneg a b ω) (mem_univ a))
  rw [c.right, hb] at hle
  exact le_antisymm hle (c.nonneg _ _ _)

/-- A zero mark marginal makes all entries with this mark vanish. -/
theorem mass_eq_zero_of_mark (c : MarkedCoupling p q m) {ω : γ}
    (hω : m.w ω = 0) (a : α) (b : β) : c.mass a b ω = 0 := by
  have hle : c.mass a b ω ≤ ∑ a, ∑ b, c.mass a b ω :=
    (single_le_sum (fun b _ => c.nonneg a b ω) (mem_univ b)).trans
      (single_le_sum (fun a _ => sum_nonneg fun b _ => c.nonneg a b ω) (mem_univ a))
  rw [c.mark, hω] at hle
  exact le_antisymm hle (c.nonneg _ _ _)

/-- Relabel or coarsen the mark by the exact finite pushforward. -/
def mapMark {δ : Type*} [Fintype δ] (c : MarkedCoupling p q m) (f : γ → δ) :
    MarkedCoupling p q (m.map f) where
  mass a b z := ∑ ω, if f ω = z then c.mass a b ω else 0
  nonneg a b z := sum_nonneg fun ω _ => by split_ifs <;> simp_all [c.nonneg]
  left a := by
    simp_rw [sum_comm (f := fun z ω => if f ω = z then c.mass a _ ω else 0)]
    simpa using c.left a
  right b := by
    simp_rw [sum_comm (f := fun z ω => if f ω = z then c.mass _ b ω else 0)]
    simpa using c.right b
  mark z := by
    simp_rw [sum_comm (f := fun b ω => if f ω = z then c.mass _ b ω else 0)]
    rw [sum_comm]
    change _ = ∑ ω, if f ω = z then m.w ω else 0
    apply sum_congr rfl
    intro ω _
    by_cases hω : f ω = z
    · simp only [hω, if_true]; exact c.mark ω
    · simp [hω]

/-- Nonzero pushed-forward mass has a nonzero original entry in its mark fiber. -/
theorem mapMark_support {δ : Type*} [Fintype δ] (c : MarkedCoupling p q m)
    (f : γ → δ) (a : α) (b : β) (z : δ)
    (hm : (c.mapMark f).mass a b z ≠ 0) :
    ∃ ω, f ω = z ∧ c.mass a b ω ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply hm
  apply sum_eq_zero
  intro ω _
  by_cases hω : f ω = z
  · simp [hω, hn ω hω]
  · simp [hω]

/-- Sample a marked spin pair, then a conditionally coupled continuation.
The continuation may depend on the first mark; its mark law is fixed. -/
def compose {A B δ : Type*} [Fintype A] [Fintype B] [Fintype δ]
    (c : MarkedCoupling p q m) (P : α → FinProb A) (Q : β → FinProb B)
    (n : FinProb δ) (e : ∀ a b (_ω : γ), MarkedCoupling (P a) (Q b) n) :
    MarkedCoupling (p.bind P) (q.bind Q) (m.prod n) where
  mass z w ν := ∑ a, ∑ b, c.mass a b ν.1 * (e a b ν.1).mass z w ν.2
  nonneg z w ν := sum_nonneg fun a _ => sum_nonneg fun b _ =>
    mul_nonneg (c.nonneg _ _ _) ((e _ _ _).nonneg _ _ _)
  left z := by
    rw [sum_four_swap]
    simp only [Fintype.sum_prod_type]
    simp_rw [← mul_sum]
    simp_rw [sum_comm (f := fun w ω => c.mass _ _ ω * ∑ ν, (e _ _ ω).mass z w ν)]
    simp_rw [← mul_sum, (e _ _ _).left]
    simp_rw [← sum_mul, c.left]
    rfl
  right w := by
    rw [sum_four_swap]
    simp only [Fintype.sum_prod_type]
    simp_rw [← mul_sum]
    simp_rw [sum_comm (f := fun z ω => c.mass _ _ ω * ∑ ν, (e _ _ ω).mass z w ν)]
    simp_rw [← mul_sum, (e _ _ _).right]
    rw [sum_comm]
    simp_rw [← sum_mul, c.right]
    rfl
  mark ν := by
    rw [sum_four_swap]
    simp_rw [← mul_sum, (e _ _ _).mark]
    simp_rw [← sum_mul]
    rw [c.mark]
    rfl

/-- A positive composed entry comes from an actual first-stage pair and continuation. -/
theorem compose_support {A B δ : Type*} [Fintype A] [Fintype B] [Fintype δ]
    (c : MarkedCoupling p q m) (P : α → FinProb A) (Q : β → FinProb B)
    (n : FinProb δ) (e : ∀ a b (_ω : γ), MarkedCoupling (P a) (Q b) n)
    (z : A) (w : B) (ν : γ × δ)
    (hm : (c.compose P Q n e).mass z w ν ≠ 0) :
    ∃ a b, c.mass a b ν.1 ≠ 0 ∧ (e a b ν.1).mass z w ν.2 ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply hm
  apply sum_eq_zero
  intro a _
  apply sum_eq_zero
  intro b _
  by_cases hab : c.mass a b ν.1 = 0
  · simp [hab]
  · simp [hn a b hab]

end MarkedCoupling

namespace DisagreementMarks

/-- The Bernoulli mass, with `true` denoting an open site. -/
def bernoulliWeight (ρ : ℝ) (b : Bool) : ℝ := if b then ρ else 1 - ρ

@[simp] theorem bernoulliWeight_true (ρ : ℝ) : bernoulliWeight ρ true = ρ := rfl
@[simp] theorem bernoulliWeight_false (ρ : ℝ) : bernoulliWeight ρ false = 1 - ρ := rfl

theorem bernoulliWeight_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (b : Bool) :
    0 ≤ bernoulliWeight ρ b := by cases b <;> simp [bernoulliWeight] <;> linarith

@[simp] theorem sum_bernoulliWeight (ρ : ℝ) : ∑ b, bernoulliWeight ρ b = 1 := by
  simp [bernoulliWeight]

/-- An actual Bernoulli probability law, allowing the degenerate parameters 0 and 1. -/
def bernoulli (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : FinProb Bool where
  w := bernoulliWeight ρ
  nonneg := bernoulliWeight_nonneg h0 h1
  sum_one := sum_bernoulliWeight ρ

/-- Residual probability mass after allocating the common closed mark to a preferred state. -/
def residual {α : Type*} [Fintype α] (p : FinProb α) (s : α) (ρ : ℝ) (a : α) : ℝ :=
  p.w a - if a = s then 1 - ρ else 0

theorem residual_nonneg {α : Type*} [Fintype α] (p : FinProb α) (s : α) (ρ : ℝ)
    (hp : 1 - ρ ≤ p.w s) (a : α) : 0 ≤ residual p s ρ a := by
  by_cases ha : a = s
  · subst a; simp only [residual, ite_true]; linarith
  · simpa [residual, ha] using p.nonneg a

@[simp] theorem sum_residual {α : Type*} [Fintype α] (p : FinProb α) (s : α) (ρ : ℝ) :
    ∑ a, residual p s ρ a = ρ := by
  simp [residual, sum_sub_distrib, p.sum_one]

theorem residual_eq_zero {α : Type*} [Fintype α] (p : FinProb α) (s : α)
    (hp : 1 ≤ p.w s) (a : α) : residual p s 0 a = 0 := by
  have h := single_le_sum (s := (univ : Finset α))
    (fun a _ => residual_nonneg p s 0 (by simpa using hp) a) (mem_univ a)
  rw [sum_residual] at h
  exact le_antisymm h (residual_nonneg p s 0 (by simpa using hp) a)

/-- The open part is the independent product of the two residuals, divided by their common mass. -/
def openMass {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb α) (q : FinProb β) (s : α) (t : β) (ρ : ℝ) (a : α) (b : β) : ℝ :=
  residual p s ρ a * residual q t ρ b / ρ

theorem openMass_row {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb α) (q : FinProb β) (s : α) (t : β) (ρ : ℝ)
    (hp : 1 - ρ ≤ p.w s) (a : α) :
    ∑ b, openMass p q s t ρ a b = residual p s ρ a := by
  simp only [openMass, ← sum_div, ← mul_sum, sum_residual]
  by_cases hρ : ρ = 0
  · subst ρ; simp [residual_eq_zero p s (by simpa using hp) a]
  · exact mul_div_cancel_right₀ _ hρ

theorem openMass_col {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb α) (q : FinProb β) (s : α) (t : β) (ρ : ℝ)
    (hq : 1 - ρ ≤ q.w t) (b : β) :
    ∑ a, openMass p q s t ρ a b = residual q t ρ b := by
  simp only [openMass, ← sum_div, ← sum_mul, sum_residual]
  by_cases hρ : ρ = 0
  · subst ρ; simp [residual_eq_zero q t (by simpa using hq) b]
  · exact mul_div_cancel_left₀ _ hρ

/-- On the closed mark both outputs equal their specified preferred states;
on the open mark sample the actual normalized residuals. -/
def preferredCoupling {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb α) (q : FinProb β) (s : α) (t : β) (ρ : ℝ)
    (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hp : 1 - ρ ≤ p.w s) (hq : 1 - ρ ≤ q.w t) :
    MarkedCoupling p q (bernoulli ρ h0 h1) where
  mass a b ω := if ω then openMass p q s t ρ a b else
    if a = s ∧ b = t then 1 - ρ else 0
  nonneg a b ω := by
    cases ω
    · simp only [Bool.false_eq_true, if_false]
      split_ifs <;> linarith
    · exact div_nonneg (mul_nonneg (residual_nonneg p s ρ hp a)
        (residual_nonneg q t ρ hq b)) h0
  left a := by
    simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, sum_add_distrib]
    rw [openMass_row p q s t ρ hp]
    by_cases ha : a = s
    · subst a; simp [residual]
    · simp [ha, residual]
  right b := by
    simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, sum_add_distrib]
    rw [openMass_col p q s t ρ hq]
    by_cases hb : b = t
    · subst b; simp [residual]
    · simp [hb, residual]
  mark ω := by
    cases ω
    · simp [bernoulli, bernoulliWeight, ite_and]
    · simp only [if_true, bernoulli, bernoulliWeight]
      simp_rw [openMass_row p q s t ρ hp]
      exact sum_residual p s ρ

@[simp] theorem preferredCoupling_closed {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb α) (q : FinProb β) (s : α) (t : β) (ρ : ℝ)
    (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hp : 1 - ρ ≤ p.w s) (hq : 1 - ρ ≤ q.w t) (a : α) (b : β) :
    (preferredCoupling p q s t ρ h0 h1 hp hq).mass a b false =
      if a = s ∧ b = t then 1 - ρ else 0 := rfl

theorem preferredCoupling_closed_support {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb α) (q : FinProb β) (s : α) (t : β) (ρ : ℝ)
    (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hp : 1 - ρ ≤ p.w s) (hq : 1 - ρ ≤ q.w t) (a : α) (b : β)
    (hm : (preferredCoupling p q s t ρ h0 h1 hp hq).mass a b false ≠ 0) :
    a = s ∧ b = t := by
  by_contra hn
  exact hm (by simp [preferredCoupling, hn])

variable {V : Type*} [Fintype V]

/-- A coordinate is Bernoulli in the remaining set and identically closed outside. -/
def markFactor (ρ : V → ℝ) (U : Finset V) (x : V) (b : Bool) : ℝ :=
  if x ∈ U then bernoulliWeight (ρ x) b else if b then 0 else 1

omit [Fintype V] in
theorem markFactor_nonneg (ρ : V → ℝ) (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∀ x, ρ x ≤ 1)
    (U : Finset V) (x : V) (b : Bool) : 0 ≤ markFactor ρ U x b := by
  by_cases hx : x ∈ U
  · simpa [markFactor, hx] using bernoulliWeight_nonneg (h0 x) (h1 x) b
  · cases b <;> simp [markFactor, hx]

omit [Fintype V] in
@[simp] theorem sum_markFactor (ρ : V → ℝ) (U : Finset V) (x : V) :
    ∑ b, markFactor ρ U x b = 1 := by
  by_cases hx : x ∈ U
  · simp [markFactor, hx]
  · simp [markFactor, hx]

/-- Independent inhomogeneous marks on `U`, with all other coordinates closed. -/
def productMarks (ρ : V → ℝ) (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∀ x, ρ x ≤ 1)
    (U : Finset V) : FinProb (V → Bool) where
  w ω := ∏ x, markFactor ρ U x (ω x)
  nonneg ω := prod_nonneg fun x _ => markFactor_nonneg ρ h0 h1 U x (ω x)
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [sum_markFactor, prod_const_one]

/-- A positive-mass mark assignment is closed outside the remaining set. -/
theorem productMarks_support (ρ : V → ℝ) (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∀ x, ρ x ≤ 1)
    (U : Finset V) (ω : V → Bool) (hm : (productMarks ρ h0 h1 U).w ω ≠ 0)
    (x : V) (hx : x ∉ U) : ω x = false := by
  cases hb : ω x
  · rfl
  · apply False.elim
    apply hm
    apply prod_eq_zero (mem_univ x)
    simp [markFactor, hx, hb]

/-- Splitting off an active coordinate leaves the product law with that coordinate erased. -/
theorem productMarks_weight_split (ρ : V → ℝ) (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∀ x, ρ x ≤ 1)
    (U : Finset V) (x : V) (hx : x ∈ U) (ω : V → Bool) :
    (productMarks ρ h0 h1 U).w ω = bernoulliWeight (ρ x) (ω x) *
      (productMarks ρ h0 h1 (U.erase x)).w (Function.update ω x false) := by
  change (∏ z, markFactor ρ U z (ω z)) = _
  rw [← mul_prod_erase (univ : Finset V) (fun z => markFactor ρ U z (ω z)) (mem_univ x)]
  rw [show markFactor ρ U x (ω x) = bernoulliWeight (ρ x) (ω x) by simp [markFactor, hx]]
  congr 1
  change _ = ∏ z, markFactor ρ (U.erase x) z (Function.update ω x false z)
  rw [← mul_prod_erase (univ : Finset V)
    (fun z => markFactor ρ (U.erase x) z (Function.update ω x false z)) (mem_univ x)]
  simp only [Function.update_self, markFactor, notMem_erase, if_false, Bool.false_eq_true,
    one_mul]
  apply prod_congr rfl
  intro z hz
  have hzx : z ≠ x := (mem_erase.mp hz).1
  simp [hzx]


/-- Canonically split a mark assignment into its value at `x` and a remainder
which is closed at `x`. -/
def markSplit (x : V) : (V → Bool) ≃ Bool × {ω : V → Bool // ω x = false} where
  toFun ω := (ω x, ⟨Function.update ω x false, by simp⟩)
  invFun ν := Function.update ν.2.1 x ν.1
  left_inv ω := by simp
  right_inv ν := by
    rcases ν with ⟨b, ω, hω⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp only [Function.update_idem]
      rw [← hω, Function.update_eq_self]

/-- Exact enumeration by the next Boolean mark and its closed remainder. -/
theorem sum_mark_update (x : V) (f : (V → Bool) → ℝ) :
    (∑ ω, f ω) = ∑ b : Bool, ∑ ω : V → Bool,
      if ω x = false then f (Function.update ω x b) else 0 := by
  rw [← (markSplit x).symm.sum_comp f, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro b _
  change (∑ ω : {ω : V → Bool // ω x = false}, f (Function.update ω.1 x b)) = _
  symm
  rw [← sum_filter]
  exact sum_subtype (univ.filter fun ω : V → Bool => ω x = false)
    (by intro ω; simp) (fun ω => f (Function.update ω x b))

/-- Inserting an independent Bernoulli mark into the erased product law recovers
exactly the original inhomogeneous product law. -/
theorem productMarks_update (ρ : V → ℝ) (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∀ x, ρ x ≤ 1)
    (U : Finset V) (x : V) (hx : x ∈ U) :
    ((bernoulli (ρ x) (h0 x) (h1 x)).prod (productMarks ρ h0 h1 (U.erase x))).map
      (fun ν => Function.update ν.2 x ν.1) = productMarks ρ h0 h1 U := by
  apply FinProb.ext_weights
  intro ω
  let m := productMarks ρ h0 h1 (U.erase x)
  have hterm (b : Bool) (ω' : V → Bool) :
      (if Function.update ω' x b = ω then bernoulliWeight (ρ x) b * m.w ω' else 0) =
      if b = ω x ∧ ω' = Function.update ω x false then
        bernoulliWeight (ρ x) b * m.w ω' else 0 := by
    by_cases hm : m.w ω' = 0
    · simp [hm]
    · have hc : ω' x = false := productMarks_support ρ h0 h1 (U.erase x) ω' hm x
        (notMem_erase x U)
      have he : Function.update ω' x b = ω ↔ b = ω x ∧ ω' = Function.update ω x false := by
        constructor
        · intro hh
          constructor
          · simpa using congrFun hh x
          · funext z
            by_cases hzx : z = x
            · subst z; simp [hc]
            · have hz := congrFun hh z
              simpa [Function.update_of_ne hzx] using hz
        · rintro ⟨hb, hω'⟩
          simp [hω', hb]
      simp only [he]
  simp only [FinProb.map, FinProb.prod, bernoulli]
  change (∑ ν : Bool × (V → Bool), if Function.update ν.2 x ν.1 = ω then
    bernoulliWeight (ρ x) ν.1 * m.w ν.2 else 0) = _
  rw [Fintype.sum_prod_type]
  simp_rw [hterm, ite_and]
  simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, if_true]
  exact (productMarks_weight_split ρ h0 h1 U x hx ω).symm

/-- Exact integration of one active Bernoulli coordinate under the mark product law. -/
theorem productMarks_expect_split (ρ : V → ℝ) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∀ x, ρ x ≤ 1) (U : Finset V) (x : V) (hx : x ∈ U)
    (f : (V → Bool) → ℝ) :
    (productMarks ρ h0 h1 U).expect f =
      ρ x * (productMarks ρ h0 h1 (U.erase x)).expect
        (fun ω => f (Function.update ω x true)) +
      (1 - ρ x) * (productMarks ρ h0 h1 (U.erase x)).expect
        (fun ω => f (Function.update ω x false)) := by
  rw [← productMarks_update ρ h0 h1 U x hx, FinProb.expect_map, FinProb.expect_prod]
  change (∑ b : Bool, bernoulliWeight (ρ x) b *
    (productMarks ρ h0 h1 (U.erase x)).expect (fun ω => f (Function.update ω x b))) = _
  simp only [Fintype.sum_bool, bernoulliWeight_true, bernoulliWeight_false]

/-- Insert a fresh independent root coordinate and integrate its two possible values. -/
theorem productMarks_expect_insert (ρ : V → ℝ) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∀ x, ρ x ≤ 1) (U : Finset V) (y : V) (hy : y ∉ U)
    (f : (V → Bool) → ℝ) :
    (productMarks ρ h0 h1 (insert y U)).expect f =
      ρ y * (productMarks ρ h0 h1 U).expect (fun ω => f (Function.update ω y true)) +
      (1 - ρ y) * (productMarks ρ h0 h1 U).expect (fun ω => f (Function.update ω y false)) := by
  simpa only [erase_insert hy] using
    productMarks_expect_split ρ h0 h1 (insert y U) y (mem_insert_self y U) f

/-- Paper (3.9)'s independent-root factor, for every event on marks with the root
forced open. The event can in particular be a finite cluster-size event. -/
theorem forcedRoot_event_factor (ρ : V → ℝ) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∀ x, ρ x ≤ 1) (U : Finset V) (y : V) (hy : y ∉ U)
    (A : (V → Bool) → Prop) :
    (productMarks ρ h0 h1 (insert y U)).expect
      (fun ω => if ω y = true ∧ A (Function.update ω y true) then 1 else 0) =
      ρ y * (productMarks ρ h0 h1 U).expect
        (fun ω => if A (Function.update ω y true) then 1 else 0) := by
  rw [productMarks_expect_insert ρ h0 h1 U y hy]
  simp only [Function.update_self, Function.update_idem, true_and,
    Bool.false_eq_true, false_and, if_false, FinProb.expect_const, mul_zero, add_zero]

/-- Positive root opening probability permits the equivalent division form in (3.9). -/
theorem forcedRoot_event_div (ρ : V → ℝ) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∀ x, ρ x ≤ 1) (U : Finset V) (y : V) (hy : y ∉ U)
    (hρ : 0 < ρ y) (A : (V → Bool) → Prop) :
    (productMarks ρ h0 h1 U).expect
      (fun ω => if A (Function.update ω y true) then 1 else 0) =
      (productMarks ρ h0 h1 (insert y U)).expect
        (fun ω => if ω y = true ∧ A (Function.update ω y true) then 1 else 0) / ρ y := by
  rw [forcedRoot_event_factor ρ h0 h1 U y hy A]
  exact (mul_div_cancel_left₀ _ hρ.ne').symm

end DisagreementMarks
end Paper09
