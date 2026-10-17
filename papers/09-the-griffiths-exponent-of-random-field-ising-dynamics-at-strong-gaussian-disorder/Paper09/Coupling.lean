/-
Copyright (c) 2026. Finite couplings and the Hamming Wasserstein distance.
-/
import Paper09.Basic
import Paper09.FiniteProb
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

open Finset BigOperators Classical

namespace Paper09

/-- A coupling is a nonnegative matrix with the two specified marginals. -/
structure Coupling {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb α) (q : FinProb β) where
  mass : α → β → ℝ
  nonneg : ∀ a b, 0 ≤ mass a b
  row : ∀ a, ∑ b, mass a b = p.w a
  col : ∀ b, ∑ a, mass a b = q.w b

namespace Coupling

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable {p : FinProb α} {q : FinProb β} {r : FinProb γ}

/-- Independent sampling always supplies a coupling. -/
def independent (p : FinProb α) (q : FinProb β) : Coupling p q where
  mass a b := p.w a * q.w b
  nonneg a b := mul_nonneg (p.nonneg a) (q.nonneg b)
  row a := by rw [← mul_sum, q.sum_one, mul_one]
  col b := by rw [← sum_mul, p.sum_one, one_mul]

instance : Nonempty (Coupling p q) := ⟨independent p q⟩

/-- Interchange the two coordinates. -/
def swap (c : Coupling p q) : Coupling q p where
  mass b a := c.mass a b
  nonneg b a := c.nonneg a b
  row := c.col
  col := c.row

/-- The identical coupling of a law with itself. -/
noncomputable def diagonal (p : FinProb α) : Coupling p p where
  mass a b := if a = b then p.w a else 0
  nonneg a b := by split_ifs <;> simp_all [p.nonneg]
  row a := by simp
  col b := by simp

/-- A zero marginal forces every entry in that row to vanish. -/
theorem mass_eq_zero_of_row (c : Coupling p q) {a : α} (ha : p.w a = 0) (b : β) :
    c.mass a b = 0 := by
  have hle : c.mass a b ≤ ∑ j, c.mass a j := single_le_sum (fun j _ => c.nonneg a j) (mem_univ b)
  rw [c.row, ha] at hle
  exact le_antisymm hle (c.nonneg a b)

/-- A zero marginal forces every entry in that column to vanish. -/
theorem mass_eq_zero_of_col (c : Coupling p q) {b : β} (hb : q.w b = 0) (a : α) :
    c.mass a b = 0 := by
  exact c.swap.mass_eq_zero_of_row hb a

/-- Finite gluing: condition on the shared middle coordinate and sum it out. -/
noncomputable def glue (c : Coupling p q) (e : Coupling q r) : Coupling p r where
  mass a z := ∑ b, c.mass a b * e.mass b z / q.w b
  nonneg a z := sum_nonneg fun b _ => div_nonneg
    (mul_nonneg (c.nonneg a b) (e.nonneg b z)) (q.nonneg b)
  row a := by
    rw [sum_comm]
    calc (∑ b, ∑ z, c.mass a b * e.mass b z / q.w b)
        = ∑ b, c.mass a b := by
          apply sum_congr rfl
          intro b _
          simp only [div_eq_mul_inv]
          rw [← sum_mul, ← mul_sum, e.row]
          by_cases hb : q.w b = 0
          · simp [hb, c.mass_eq_zero_of_col hb a]
          · field_simp
      _ = p.w a := c.row a
  col z := by
    rw [sum_comm]
    calc (∑ b, ∑ a, c.mass a b * e.mass b z / q.w b)
        = ∑ b, e.mass b z := by
          apply sum_congr rfl
          intro b _
          simp only [div_eq_mul_inv]
          rw [← sum_mul, ← sum_mul, c.col]
          by_cases hb : q.w b = 0
          · simp [hb, e.mass_eq_zero_of_row hb z]
          · field_simp
      _ = r.w z := e.col z

/-- Expected transport cost under a concrete coupling. -/
def cost (c : Coupling p q) (d : α → β → ℝ) : ℝ :=
  ∑ a, ∑ b, c.mass a b * d a b

theorem cost_nonneg (c : Coupling p q) {d : α → β → ℝ} (hd : ∀ a b, 0 ≤ d a b) :
    0 ≤ c.cost d :=
  sum_nonneg fun a _ => sum_nonneg fun b _ => mul_nonneg (c.nonneg a b) (hd a b)

theorem expect_left (c : Coupling p q) (f : α → ℝ) :
    (∑ a, ∑ b, c.mass a b * f a) = p.expect f := by
  unfold FinProb.expect
  apply sum_congr rfl
  intro a _
  rw [← sum_mul, c.row]

theorem expect_right (c : Coupling p q) (f : β → ℝ) :
    (∑ a, ∑ b, c.mass a b * f b) = q.expect f := by
  rw [sum_comm]
  unfold FinProb.expect
  apply sum_congr rfl
  intro b _
  rw [← sum_mul, c.col]

/-- Gluing respects any pointwise triangular bound on the costs. -/
theorem cost_glue_le (c : Coupling p q) (e : Coupling q r)
    (d₁ : α → β → ℝ) (d₂ : β → γ → ℝ) (d₃ : α → γ → ℝ)
    (htri : ∀ a b z, d₃ a z ≤ d₁ a b + d₂ b z) :
    (c.glue e).cost d₃ ≤ c.cost d₁ + e.cost d₂ := by
  have hm (a : α) (b : β) (z : γ) :
      0 ≤ c.mass a b * e.mass b z / q.w b :=
    div_nonneg (mul_nonneg (c.nonneg a b) (e.nonneg b z)) (q.nonneg b)
  have hrow (a : α) (b : β) :
      (∑ z, c.mass a b * e.mass b z / q.w b) = c.mass a b := by
    simp only [div_eq_mul_inv]
    rw [← sum_mul, ← mul_sum, e.row]
    by_cases hb : q.w b = 0
    · simp [hb, c.mass_eq_zero_of_col hb a]
    · field_simp
  have hcol (b : β) (z : γ) :
      (∑ a, c.mass a b * e.mass b z / q.w b) = e.mass b z := by
    simp only [div_eq_mul_inv]
    rw [← sum_mul, ← sum_mul, c.col]
    by_cases hb : q.w b = 0
    · simp [hb, e.mass_eq_zero_of_row hb z]
    · field_simp
  calc (c.glue e).cost d₃
      = ∑ a, ∑ b, ∑ z, (c.mass a b * e.mass b z / q.w b) * d₃ a z := by
        unfold cost glue
        simp only [sum_mul]
        apply sum_congr rfl
        intro a _
        rw [sum_comm]
    _ ≤ ∑ a, ∑ b, ∑ z,
        (c.mass a b * e.mass b z / q.w b) * (d₁ a b + d₂ b z) := by
        exact sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (htri a b z) (hm a b z)
    _ = c.cost d₁ + e.cost d₂ := by
        simp only [mul_add, sum_add_distrib]
        congr 1
        · unfold cost
          apply sum_congr rfl
          intro a _
          apply sum_congr rfl
          intro b _
          rw [← sum_mul, hrow]
        · unfold cost
          rw [sum_comm]
          apply sum_congr rfl
          intro b _
          rw [sum_comm]
          apply sum_congr rfl
          intro z _
          rw [← sum_mul, hcol]

end Coupling

namespace FinProb

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Apply a finite Markov kernel by summing over the starting configuration. -/
def bind (p : FinProb α) (K : α → FinProb β) : FinProb β where
  w b := ∑ a, p.w a * (K a).w b
  nonneg b := sum_nonneg fun a _ => mul_nonneg (p.nonneg a) ((K a).nonneg b)
  sum_one := by
    rw [sum_comm]
    simp_rw [← mul_sum, (K _).sum_one, mul_one]
    exact p.sum_one

/-- Evolve the actual finite law for a specified number of kernel steps. -/
def evolve (K : α → FinProb α) : ℕ → FinProb α → FinProb α
  | 0, p => p
  | n + 1, p => (evolve K n p).bind K

end FinProb

namespace Coupling

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable {p : FinProb α} {q : FinProb β}

/-- Lift an initial coupling through actual couplings of each pair of kernel outputs. -/
def bind (c : Coupling p q) (K : α → FinProb γ) (L : β → FinProb δ)
    (e : ∀ a b, Coupling (K a) (L b)) : Coupling (p.bind K) (q.bind L) where
  mass z w := ∑ a, ∑ b, c.mass a b * (e a b).mass z w
  nonneg z w := sum_nonneg fun a _ => sum_nonneg fun b _ =>
    mul_nonneg (c.nonneg a b) ((e a b).nonneg z w)
  row z := by
    rw [sum_comm]
    unfold FinProb.bind
    apply sum_congr rfl
    intro a _
    rw [sum_comm]
    simp_rw [← mul_sum, (e a _).row]
    rw [← sum_mul, c.row]
  col w := by
    rw [sum_comm]
    simp_rw [sum_comm (f := fun z b => c.mass _ b * (e _ b).mass z w)]
    simp_rw [← mul_sum, (e _ _).col]
    rw [sum_comm]
    unfold FinProb.bind
    apply sum_congr rfl
    intro b _
    rw [← sum_mul, c.col]

/-- The lifted cost is the expectation of the conditional transport costs. -/
theorem cost_bind (c : Coupling p q) (K : α → FinProb γ) (L : β → FinProb δ)
    (e : ∀ a b, Coupling (K a) (L b)) (d : γ → δ → ℝ) :
    (c.bind K L e).cost d = ∑ a, ∑ b, c.mass a b * (e a b).cost d := by
  unfold cost bind
  simp only [sum_mul, mul_sum]
  calc (∑ z, ∑ w, ∑ a, ∑ b, c.mass a b * (e a b).mass z w * d z w)
      = ∑ a, ∑ b, ∑ z, ∑ w, c.mass a b * (e a b).mass z w * d z w := by
        calc (∑ z, ∑ w, ∑ a, ∑ b, c.mass a b * (e a b).mass z w * d z w)
            = ∑ z, ∑ a, ∑ w, ∑ b, c.mass a b * (e a b).mass z w * d z w := by
              apply sum_congr rfl
              intro z _
              rw [sum_comm]
          _ = ∑ a, ∑ z, ∑ w, ∑ b, c.mass a b * (e a b).mass z w * d z w := by
              rw [sum_comm]
          _ = ∑ a, ∑ z, ∑ b, ∑ w, c.mass a b * (e a b).mass z w * d z w := by
              apply sum_congr rfl
              intro a _
              apply sum_congr rfl
              intro z _
              rw [sum_comm]
          _ = _ := by
              apply sum_congr rfl
              intro a _
              rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro z _
      apply sum_congr rfl
      intro w _
      ring

theorem mass_sum (c : Coupling p q) : ∑ a, ∑ b, c.mass a b = 1 := by
  simp_rw [c.row]
  exact p.sum_one

theorem cost_const (c : Coupling p q) (M : ℝ) : c.cost (fun _ _ => M) = M := by
  unfold cost
  simp_rw [← sum_mul]
  rw [c.mass_sum, one_mul]

theorem cost_mono (c : Coupling p q) {d e : α → β → ℝ} (h : ∀ a b, d a b ≤ e a b) :
    c.cost d ≤ c.cost e :=
  sum_le_sum fun a _ => sum_le_sum fun b _ =>
    mul_le_mul_of_nonneg_left (h a b) (c.nonneg a b)

end Coupling

/-- The actual transport infimum over all couplings of the given finite laws. -/
noncomputable def wasserstein {α β : Type*} [Fintype α] [Fintype β]
    (d : α → β → ℝ) (p : FinProb α) (q : FinProb β) : ℝ :=
  sInf (Set.range fun c : Coupling p q => c.cost d)

namespace Wasserstein

variable {α : Type*} [Fintype α]
variable {d : α → α → ℝ} {p q r : FinProb α}

theorem le_cost (hd : ∀ a b, 0 ≤ d a b) (c : Coupling p q) :
    wasserstein d p q ≤ c.cost d := by
  have hb : BddBelow (Set.range fun e : Coupling p q => e.cost d) :=
    ⟨0, fun x ⟨e, he⟩ => he ▸ e.cost_nonneg hd⟩
  exact csInf_le hb ⟨c, rfl⟩

theorem lower_bound (h : ∀ c : Coupling p q, t ≤ c.cost d) :
    t ≤ wasserstein d p q := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨c, rfl⟩
  exact h c

theorem nonneg (hd : ∀ a b, 0 ≤ d a b) : 0 ≤ wasserstein d p q :=
  lower_bound fun c => c.cost_nonneg hd

theorem self (hd : ∀ a b, 0 ≤ d a b) (hdiag : ∀ a, d a a = 0) :
    wasserstein d p p = 0 := by
  apply le_antisymm _ (nonneg hd)
  calc wasserstein d p p ≤ (Coupling.diagonal p).cost d := le_cost hd _
    _ = 0 := by simp [Coupling.cost, Coupling.diagonal, hdiag]

/-- The triangle inequality follows from the explicit finite gluing construction. -/
theorem triangle (hd : ∀ a b, 0 ≤ d a b)
    (htri : ∀ a b z, d a z ≤ d a b + d b z) :
    wasserstein d p r ≤ wasserstein d p q + wasserstein d q r := by
  have hc : ∀ c : Coupling p q,
      wasserstein d p r - wasserstein d q r ≤ c.cost d := by
    intro c
    have he : wasserstein d p r - c.cost d ≤ wasserstein d q r := by
      apply lower_bound
      intro e
      have h := (le_cost hd (c.glue e)).trans (c.cost_glue_le e d d d htri)
      linarith
    linarith
  have h := lower_bound hc
  linarith

/-- Since the coupling set is nonempty, its infimum admits arbitrarily good
actual couplings; no optimal-coupling oracle is assumed. -/
theorem exists_cost_lt (p q : FinProb α) (d : α → α → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : Coupling p q, c.cost d < wasserstein d p q + ε := by
  have hlt : wasserstein d p q < wasserstein d p q + ε := by linarith
  obtain ⟨x, ⟨c, rfl⟩, hc⟩ := exists_lt_of_csInf_lt
    (Set.range_nonempty (fun c : Coupling p q => c.cost d)) hlt
  exact ⟨c, hc⟩

/-- A pointwise kernel contraction extends to arbitrary starting laws.
The proof uses finite mixtures of explicit couplings and an epsilon-infimum
argument, rather than assuming existence of an optimal coupling. -/
theorem kernel_contraction (hd : ∀ a b, 0 ≤ d a b)
    (K : α → FinProb α) {a : ℝ} (ha : 0 ≤ a)
    (hK : ∀ x y, wasserstein d (K x) (K y) ≤ a * d x y) :
    wasserstein d (p.bind K) (q.bind K) ≤ a * wasserstein d p q := by
  have hc : ∀ c : Coupling p q,
      wasserstein d (p.bind K) (q.bind K) ≤ a * c.cost d := by
    intro c
    apply le_of_forall_pos_le_add
    intro ε hε
    have hchoices : ∀ x y, ∃ e : Coupling (K x) (K y),
        e.cost d < wasserstein d (K x) (K y) + ε :=
      fun x y => exists_cost_lt (K x) (K y) d hε
    choose e he using hchoices
    have hbound (x y : α) : (e x y).cost d ≤ a * d x y + ε := by
      linarith [he x y, hK x y]
    calc wasserstein d (p.bind K) (q.bind K) ≤ (c.bind K K e).cost d := le_cost hd _
      _ = ∑ x, ∑ y, c.mass x y * (e x y).cost d := c.cost_bind K K e d
      _ ≤ ∑ x, ∑ y, c.mass x y * (a * d x y + ε) := by
        exact sum_le_sum fun x _ => sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (hbound x y) (c.nonneg x y)
      _ = a * c.cost d + ε := by
        simp only [mul_add, sum_add_distrib]
        have hmain : (∑ x, ∑ y, c.mass x y * (a * d x y)) = a * c.cost d := by
          unfold Coupling.cost
          simp only [mul_sum]
          apply sum_congr rfl
          intro x _
          apply sum_congr rfl
          intro y _
          ring
        rw [hmain]
        congr 1
        simp only [← sum_mul, c.mass_sum, one_mul]
  by_cases hz : a = 0
  · simpa [hz] using hc (Coupling.independent p q)
  · have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    have h : wasserstein d (p.bind K) (q.bind K) / a ≤ wasserstein d p q := by
      apply lower_bound
      intro c
      apply (div_le_iff₀ hpos).mpr
      simpa only [mul_comm] using hc c
    exact (div_le_iff₀ hpos).mp h |>.trans_eq (mul_comm _ _)

/-- Iterating a contracting finite kernel contracts transport distance by `a^n`. -/
theorem kernel_iterate_contraction (hd : ∀ a b, 0 ≤ d a b)
    (K : α → FinProb α) {a : ℝ} (ha : 0 ≤ a)
    (hK : ∀ x y, wasserstein d (K x) (K y) ≤ a * d x y) (n : ℕ) :
    wasserstein d (FinProb.evolve K n p) (FinProb.evolve K n q) ≤
      a ^ n * wasserstein d p q := by
  induction n with
  | zero => simp [FinProb.evolve]
  | succ n ih =>
      calc wasserstein d (FinProb.evolve K (n + 1) p) (FinProb.evolve K (n + 1) q)
          ≤ a * wasserstein d (FinProb.evolve K n p) (FinProb.evolve K n q) :=
            kernel_contraction hd K ha hK
        _ ≤ a * (a ^ n * wasserstein d p q) := mul_le_mul_of_nonneg_left ih ha
        _ = a ^ (n + 1) * wasserstein d p q := by rw [pow_succ]; ring

end Wasserstein

namespace Coupling

variable {α : Type*} [Fintype α]

/-- Unmatched mass remaining after matching the pointwise common part. -/
noncomputable def deficit (p q : FinProb α) : ℝ := 1 - ∑ a, min (p.w a) (q.w a)

noncomputable def leftResidual (p q : FinProb α) (a : α) : ℝ := p.w a - min (p.w a) (q.w a)
noncomputable def rightResidual (p q : FinProb α) (a : α) : ℝ := q.w a - min (p.w a) (q.w a)

theorem leftResidual_nonneg (p q : FinProb α) (a : α) : 0 ≤ leftResidual p q a :=
  sub_nonneg.mpr (min_le_left _ _)

theorem rightResidual_nonneg (p q : FinProb α) (a : α) : 0 ≤ rightResidual p q a :=
  sub_nonneg.mpr (min_le_right _ _)

theorem sum_leftResidual (p q : FinProb α) : ∑ a, leftResidual p q a = deficit p q := by
  simp only [leftResidual, sum_sub_distrib, p.sum_one, deficit]

theorem sum_rightResidual (p q : FinProb α) : ∑ a, rightResidual p q a = deficit p q := by
  simp only [rightResidual, sum_sub_distrib, q.sum_one, deficit]

theorem deficit_nonneg (p q : FinProb α) : 0 ≤ deficit p q := by
  rw [← sum_leftResidual]
  exact sum_nonneg fun a _ => leftResidual_nonneg p q a

theorem leftResidual_zero (p q : FinProb α) (h : deficit p q = 0) (a : α) :
    leftResidual p q a = 0 := by
  have hle := single_le_sum (s := (univ : Finset α))
    (fun b _ => leftResidual_nonneg p q b) (mem_univ a)
  rw [sum_leftResidual, h] at hle
  exact le_antisymm hle (leftResidual_nonneg p q a)

theorem rightResidual_zero (p q : FinProb α) (h : deficit p q = 0) (a : α) :
    rightResidual p q a = 0 := by
  have hle := single_le_sum (s := (univ : Finset α))
    (fun b _ => rightResidual_nonneg p q b) (mem_univ a)
  rw [sum_rightResidual, h] at hle
  exact le_antisymm hle (rightResidual_nonneg p q a)

/-- A maximal coupling: first match the common part, then independently pair
its two residual masses. The zero-deficit case uses the same formula, with
Lean's zero division; the residuals are then both proved to vanish. -/
noncomputable def maximal (p q : FinProb α) : Coupling p q where
  mass a b := (if a = b then min (p.w a) (q.w a) else 0) +
    leftResidual p q a * rightResidual p q b / deficit p q
  nonneg a b := add_nonneg
    (by split_ifs <;> simp_all [p.nonneg, q.nonneg])
    (div_nonneg (mul_nonneg (leftResidual_nonneg p q a) (rightResidual_nonneg p q b))
      (deficit_nonneg p q))
  row a := by
    rw [sum_add_distrib]
    simp only [sum_ite_eq, mem_univ, if_true]
    simp only [div_eq_mul_inv]
    rw [← sum_mul, ← mul_sum, sum_rightResidual]
    by_cases h : deficit p q = 0
    · have hz := leftResidual_zero p q h a
      simp only [leftResidual] at hz
      rw [h]
      simp only [inv_zero, mul_zero, add_zero]
      linarith
    · rw [mul_inv_cancel_right₀ h]
      simp [leftResidual]
  col b := by
    rw [sum_add_distrib]
    simp only [sum_ite_eq', mem_univ, if_true]
    simp only [div_eq_mul_inv]
    rw [← sum_mul, ← sum_mul, sum_leftResidual]
    by_cases h : deficit p q = 0
    · have hz := rightResidual_zero p q h b
      simp only [rightResidual] at hz
      rw [h]
      simp only [inv_zero, mul_zero, add_zero]
      linarith
    · rw [mul_comm (deficit p q) (rightResidual p q b), mul_inv_cancel_right₀ h]
      simp [rightResidual]

/-- The residual mass equals the usual half of the L¹ distance. -/
theorem deficit_eq_half_l1 (p q : FinProb α) :
    deficit p q = (1 / 2 : ℝ) * ∑ a, |p.w a - q.w a| := by
  have ha (a : α) : |p.w a - q.w a| = p.w a + q.w a - 2 * min (p.w a) (q.w a) := by
    rcases le_total (p.w a) (q.w a) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  simp only [ha, sum_sub_distrib, sum_add_distrib, ← mul_sum, p.sum_one, q.sum_one, deficit]
  ring

/-- Total mass off the diagonal is one minus the mass of identical samples. -/
theorem disagreement_cost_eq {p q : FinProb α} (c : Coupling p q) :
    c.cost (fun a b => if a = b then 0 else 1) = 1 - ∑ a, c.mass a a := by
  have hrow (a : α) :
      (∑ b, c.mass a b * (if a = b then (0 : ℝ) else 1)) = p.w a - c.mass a a := by
    have hsplit : (∑ b, c.mass a b) =
        c.mass a a + ∑ b, c.mass a b * (if a = b then (0 : ℝ) else 1) := by
      calc (∑ b, c.mass a b) = ∑ b,
          ((if a = b then c.mass a b else 0) + c.mass a b * (if a = b then 0 else 1)) := by
            apply sum_congr rfl
            intro b _
            split_ifs <;> simp
        _ = _ := by rw [sum_add_distrib]; simp
    rw [c.row] at hsplit
    linarith
  unfold cost
  simp only [hrow, sum_sub_distrib, p.sum_one]

/-- The coupling inequality for finite laws, proved from diagonal mass bounds. -/
theorem half_l1_le_disagreement_cost {p q : FinProb α} (c : Coupling p q) :
    (1 / 2 : ℝ) * ∑ a, |p.w a - q.w a| ≤
      c.cost (fun a b => if a = b then 0 else 1) := by
  rw [← deficit_eq_half_l1, disagreement_cost_eq]
  unfold deficit
  have hs : (∑ a, c.mass a a) ≤ ∑ a, min (p.w a) (q.w a) := by
    apply sum_le_sum
    intro a _
    apply le_min
    · have h := single_le_sum (fun b _ => c.nonneg a b) (mem_univ a)
      rwa [c.row] at h
    · have h := single_le_sum (fun b _ => c.nonneg b a) (mem_univ a)
      rwa [c.col] at h
  linarith

/-- The constructed maximal coupling attains the total-variation disagreement bound. -/
theorem maximal_disagreement_cost (p q : FinProb α) :
    (maximal p q).cost (fun a b => if a = b then 0 else 1) =
      (1 / 2 : ℝ) * ∑ a, |p.w a - q.w a| := by
  have hres (a : α) : leftResidual p q a * rightResidual p q a = 0 := by
    rcases le_total (p.w a) (q.w a) with h | h
    · simp [leftResidual, min_eq_left h]
    · simp [rightResidual, min_eq_right h]
  rw [disagreement_cost_eq, ← deficit_eq_half_l1]
  simp [maximal, hres, deficit]

/-- A maximal coupling costs at most the diameter times total variation. -/
theorem maximal_cost_le (p q : FinProb α) (d : α → α → ℝ) (M : ℝ)
    (hdiag : ∀ a, d a a = 0) (hbound : ∀ a b, d a b ≤ M) :
    (maximal p q).cost d ≤ M * ((1 / 2 : ℝ) * ∑ a, |p.w a - q.w a|) := by
  have hres : (∑ a, ∑ b, leftResidual p q a * rightResidual p q b / deficit p q) =
      deficit p q := by
    simp only [div_eq_mul_inv]
    simp_rw [← sum_mul, ← mul_sum, sum_rightResidual]
    rw [← sum_mul, sum_leftResidual]
    by_cases h : deficit p q = 0
    · simp [h]
    · field_simp
  calc (maximal p q).cost d
      = ∑ a, ∑ b, (leftResidual p q a * rightResidual p q b / deficit p q) * d a b := by
        unfold cost maximal
        apply sum_congr rfl
        intro a _
        apply sum_congr rfl
        intro b _
        by_cases h : a = b
        · subst b; simp [hdiag]
        · simp [h]
    _ ≤ ∑ a, ∑ b, (leftResidual p q a * rightResidual p q b / deficit p q) * M := by
        apply sum_le_sum
        intro a _
        apply sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left (hbound a b)
          (div_nonneg (mul_nonneg (leftResidual_nonneg p q a) (rightResidual_nonneg p q b))
            (deficit_nonneg p q))
    _ = deficit p q * M := by simp only [← sum_mul]; rw [hres]
    _ = _ := by rw [deficit_eq_half_l1]; ring

end Coupling

/-- Hamming distance viewed as a real transport cost. -/
def hammingR {ι : Type*} [Fintype ι] (η ξ : Config ι) : ℝ := hamming η ξ

theorem hammingR_eq_sum {ι : Type*} [Fintype ι] (η ξ : Config ι) :
    hammingR η ξ = ∑ x, if η x = ξ x then (0 : ℝ) else 1 := by
  simp [hammingR, hamming, ← Finset.sum_boole, ite_not]

theorem hammingR_nonneg {ι : Type*} [Fintype ι] (η ξ : Config ι) :
    0 ≤ hammingR η ξ := Nat.cast_nonneg _

theorem hammingR_triangle {ι : Type*} [Fintype ι] (η ξ ζ : Config ι) :
    hammingR η ζ ≤ hammingR η ξ + hammingR ξ ζ := by
  simp only [hammingR_eq_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases h₁ : η x = ξ x <;> by_cases h₂ : ξ x = ζ x <;>
    by_cases h₃ : η x = ζ x <;> simp_all

/-- The Hamming diameter of a configuration space is its number of sites. -/
theorem hammingR_le_card {ι : Type*} [Fintype ι] (η ξ : Config ι) :
    hammingR η ξ ≤ Fintype.card ι := by
  have h : hamming η ξ ≤ Fintype.card ι := card_le_card (filter_subset _ _)
  unfold hammingR
  exact_mod_cast h

/-- Hamming Wasserstein distance, with the infimum taken over genuine couplings. -/
noncomputable def hammingWasserstein {ι : Type*} [Fintype ι]
    (p q : FinProb (Config ι)) : ℝ := wasserstein hammingR p q

/-- Total-variation approximation gives a concrete Hamming-cost approximation. -/
theorem hammingWasserstein_le_half_l1 {ι : Type*} [Fintype ι]
    (p q : FinProb (Config ι)) :
    hammingWasserstein p q ≤ (Fintype.card ι : ℝ) *
      ((1 / 2 : ℝ) * ∑ η, |p.w η - q.w η|) := by
  calc hammingWasserstein p q ≤ (Coupling.maximal p q).cost hammingR :=
         Wasserstein.le_cost hammingR_nonneg _
    _ ≤ _ := Coupling.maximal_cost_le p q hammingR _
         (fun η => by simp [hammingR, hamming_self]) hammingR_le_card

/-- Gluing local approximations on both sides adds at most diameter times the
sum of their TV errors. With equal errors this is the `2 M δ` term in (3.18). -/
theorem hamming_simulation_gluing {ι : Type*} [Fintype ι]
    (p q pEq qEq : FinProb (Config ι)) (δp δq : ℝ)
    (hp : (1 / 2 : ℝ) * ∑ η, |p.w η - pEq.w η| ≤ δp)
    (hq : (1 / 2 : ℝ) * ∑ η, |qEq.w η - q.w η| ≤ δq) :
    hammingWasserstein p q ≤ hammingWasserstein pEq qEq +
      (Fintype.card ι : ℝ) * (δp + δq) := by
  have hpw := (hammingWasserstein_le_half_l1 p pEq).trans
    (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _))
  have hqw := (hammingWasserstein_le_half_l1 qEq q).trans
    (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _))
  have ht₁ : hammingWasserstein p q ≤
      hammingWasserstein p pEq + hammingWasserstein pEq q :=
    Wasserstein.triangle hammingR_nonneg hammingR_triangle
  have ht₂ : hammingWasserstein pEq q ≤
      hammingWasserstein pEq qEq + hammingWasserstein qEq q :=
    Wasserstein.triangle hammingR_nonneg hammingR_triangle
  nlinarith

theorem hamming_eq_zero_iff {ι : Type*} [Fintype ι] (η ξ : Config ι) :
    hamming η ξ = 0 ↔ η = ξ := by
  constructor
  · intro h
    funext x
    by_contra hx
    have hp : 0 < hamming η ξ := by
      exact card_pos.mpr ⟨x, by simp [hx]⟩
    omega
  · rintro rfl
    exact hamming_self _

/-- Disagreement of entire configurations costs at least one Hamming unit. -/
theorem configuration_disagreement_le_hammingR {ι : Type*} [Fintype ι]
    (η ξ : Config ι) : (if η = ξ then (0 : ℝ) else 1) ≤ hammingR η ξ := by
  by_cases h : η = ξ
  · simp [h, hammingR, hamming_self]
  · simp only [h, if_false]
    have hz : hamming η ξ ≠ 0 := by simpa [hamming_eq_zero_iff] using h
    have hn : 1 ≤ hamming η ξ := Nat.one_le_iff_ne_zero.mpr hz
    unfold hammingR
    exact_mod_cast hn

/-- Total variation is bounded by Hamming Wasserstein distance, using the
finite coupling inequality and the integer-valued Hamming cost. -/
theorem half_l1_le_hammingWasserstein {ι : Type*} [Fintype ι]
    (p q : FinProb (Config ι)) :
    (1 / 2 : ℝ) * ∑ η, |p.w η - q.w η| ≤ hammingWasserstein p q := by
  apply Wasserstein.lower_bound
  intro c
  apply (c.half_l1_le_disagreement_cost).trans
  unfold Coupling.cost
  apply sum_le_sum
  intro η _
  apply sum_le_sum
  intro ξ _
  apply mul_le_mul_of_nonneg_left _ (c.nonneg η ξ)
  have h := configuration_disagreement_le_hammingR η ξ
  by_cases he : η = ξ <;> simpa only [he, if_true, if_false] using h

/-- The usual one-discrepancy relation is exactly Hamming distance one. -/
theorem hamming_eq_one_iff {ι : Type*} [Fintype ι] (η ξ : Config ι) :
    hamming η ξ = 1 ↔ ∃ x, η x ≠ ξ x ∧ ∀ y, y ≠ x → η y = ξ y := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := card_eq_one.mp h
    have hxmem : x ∈ (univ.filter fun y => η y ≠ ξ y) := by rw [hx]; simp
    refine ⟨x, (mem_filter.mp hxmem).2, ?_⟩
    intro y hy
    by_contra hneq
    have hymem : y ∈ (univ.filter fun y => η y ≠ ξ y) := by simp [hneq]
    rw [hx] at hymem
    exact hy (mem_singleton.mp hymem)
  · rintro ⟨x, hx, hrest⟩
    have he : (univ.filter fun y => η y ≠ ξ y) = {x} := by
      ext y
      by_cases hy : y = x
      · subst y; simp [hx]
      · simp [hy, hrest y hy]
    simp [hamming, he]

/-- Correcting a discrepant coordinate removes exactly one unit of Hamming distance. -/
theorem hamming_update_target {ι : Type*} [Fintype ι]
    (η ξ : Config ι) {x : ι} (hx : η x ≠ ξ x) :
    hamming (Function.update η x (ξ x)) ξ + 1 = hamming η ξ := by
  have he : (univ.filter fun y => Function.update η x (ξ x) y ≠ ξ y) =
      (univ.filter fun y => η y ≠ ξ y).erase x := by
    ext y
    by_cases hy : y = x
    · subst y; simp
    · simp [hy]
  unfold hamming
  rw [he]
  exact card_erase_add_one (by simp [hx])

/-- One coordinate change is an edge of a shortest Hamming path. -/
theorem hamming_update_one {ι : Type*} [Fintype ι]
    (η ξ : Config ι) {x : ι} (hx : η x ≠ ξ x) :
    hamming η (Function.update η x (ξ x)) = 1 := by
  have he : (univ.filter fun y => η y ≠ Function.update η x (ξ x) y) = {x} := by
    ext y
    by_cases hy : y = x
    · subst y; simp [hx]
    · simp [hy]
  simp [hamming, he]

/-- Path coupling: a one-discrepancy transport estimate extends to all configurations.
The proof corrects discrepant coordinates one at a time and uses the proved gluing
triangle inequality. This is the shortest-path step in Lemmas 3.5 and 3.6. -/
theorem hamming_path_coupling {ι : Type*} [Fintype ι]
    (K : Config ι → FinProb (Config ι)) (a : ℝ)
    (hstep : ∀ η ξ, hamming η ξ = 1 → hammingWasserstein (K η) (K ξ) ≤ a) :
    ∀ η ξ, hammingWasserstein (K η) (K ξ) ≤ a * hammingR η ξ := by
  have hall : ∀ n : ℕ, ∀ η ξ : Config ι, hamming η ξ = n →
      hammingWasserstein (K η) (K ξ) ≤ a * hammingR η ξ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro η ξ hn
      by_cases hzero : hamming η ξ = 0
      · have he := (hamming_eq_zero_iff η ξ).mp hzero
        subst ξ
        have hw : hammingWasserstein (K η) (K η) = 0 :=
          Wasserstein.self hammingR_nonneg (fun ζ => by simp [hammingR, hamming_self])
        simp [hw, hammingR, hamming_self]
      · have hpos : 0 < hamming η ξ := Nat.pos_of_ne_zero hzero
        obtain ⟨x, hx⟩ := card_pos.mp hpos
        have hneq : η x ≠ ξ x := (mem_filter.mp hx).2
        let ζ := Function.update η x (ξ x)
        have hreduce : hamming ζ ξ + 1 = hamming η ξ := hamming_update_target η ξ hneq
        have hlt : hamming ζ ξ < n := by omega
        have hi := ih (hamming ζ ξ) hlt ζ ξ rfl
        have hs := hstep η ζ (hamming_update_one η ξ hneq)
        have ht : hammingWasserstein (K η) (K ξ) ≤
            hammingWasserstein (K η) (K ζ) + hammingWasserstein (K ζ) (K ξ) :=
          Wasserstein.triangle hammingR_nonneg hammingR_triangle
        have hreal : hammingR ζ ξ + 1 = hammingR η ξ := by
          unfold hammingR
          exact_mod_cast hreduce
        calc hammingWasserstein (K η) (K ξ)
            ≤ hammingWasserstein (K η) (K ζ) + hammingWasserstein (K ζ) (K ξ) := ht
          _ ≤ a + a * hammingR ζ ξ := add_le_add hs hi
          _ = a * hammingR η ξ := by rw [← hreal]; ring
  intro η ξ
  exact hall (hamming η ξ) η ξ rfl

/-- The finite configuration space has Hamming Wasserstein diameter at most its size. -/
theorem hammingWasserstein_le_card {ι : Type*} [Fintype ι]
    (p q : FinProb (Config ι)) : hammingWasserstein p q ≤ Fintype.card ι := by
  let c := Coupling.independent p q
  calc hammingWasserstein p q ≤ c.cost hammingR := Wasserstein.le_cost hammingR_nonneg c
    _ ≤ c.cost (fun _ _ => (Fintype.card ι : ℝ)) := c.cost_mono hammingR_le_card
    _ = _ := c.cost_const _

/-- The genuine one-discrepancy path estimate yields contraction for arbitrary
initial laws and every integer number of steps. -/
theorem hamming_path_coupling_iterate {ι : Type*} [Fintype ι]
    (K : Config ι → FinProb (Config ι)) (a : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ η ξ, hamming η ξ = 1 → hammingWasserstein (K η) (K ξ) ≤ a)
    (p q : FinProb (Config ι)) (n : ℕ) :
    hammingWasserstein (FinProb.evolve K n p) (FinProb.evolve K n q) ≤
      a ^ n * hammingWasserstein p q :=
  Wasserstein.kernel_iterate_contraction hammingR_nonneg K ha
    (hamming_path_coupling K a hstep) n

/-- Stationarity is preserved by any number of actual kernel steps. -/
theorem FinProb.evolve_stationary {α : Type*} [Fintype α]
    (K : α → FinProb α) (q : FinProb α) (hq : q.bind K = q) (n : ℕ) :
    FinProb.evolve K n q = q := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [FinProb.evolve, ih] using hq

/-- A finite-kernel mixing estimate derived from one-discrepancy contraction,
the concrete coupling inequality, and the Hamming diameter bound. -/
theorem finite_kernel_mixing_from_path {ι : Type*} [Fintype ι]
    (K : Config ι → FinProb (Config ι)) (a : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ η ξ, hamming η ξ = 1 → hammingWasserstein (K η) (K ξ) ≤ a)
    (p q : FinProb (Config ι)) (hq : q.bind K = q) (n : ℕ) :
    (1 / 2 : ℝ) * ∑ η, |(FinProb.evolve K n p).w η - q.w η| ≤
      (Fintype.card ι : ℝ) * a ^ n := by
  have hcontract := hamming_path_coupling_iterate K a ha hstep p q n
  rw [FinProb.evolve_stationary K q hq n] at hcontract
  calc (1 / 2 : ℝ) * ∑ η, |(FinProb.evolve K n p).w η - q.w η|
      ≤ hammingWasserstein (FinProb.evolve K n p) q := half_l1_le_hammingWasserstein _ _
    _ ≤ a ^ n * hammingWasserstein p q := hcontract
    _ ≤ a ^ n * (Fintype.card ι : ℝ) :=
      mul_le_mul_of_nonneg_left (hammingWasserstein_le_card p q) (pow_nonneg ha n)
    _ = _ := mul_comm _ _

private theorem spin_discrepancy_lower (a b : Spin) :
    (spinVal b - spinVal a) / 2 ≤ if a = b then (0 : ℝ) else 1 := by
  fin_cases a <;> fin_cases b <;> norm_num [spinVal]

private theorem spin_discrepancy_ordered (a b : Spin) (hab : a ≤ b) :
    (if a = b then (0 : ℝ) else 1) = (spinVal b - spinVal a) / 2 := by
  fin_cases a <;> fin_cases b <;> norm_num [spinVal] at *

/-- The difference of expected spin sums under two finite laws. -/
noncomputable def spinExpectationDifference {ι : Type*} [Fintype ι]
    (p q : FinProb (Config ι)) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, (q.expect (fun η => spinVal (η x)) -
    p.expect (fun η => spinVal (η x)))

private theorem sum_triple_rotate {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] (F : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ z, F a b z) = ∑ z, ∑ a, ∑ b, F a b z := by
  calc (∑ a, ∑ b, ∑ z, F a b z) = ∑ a, ∑ z, ∑ b, F a b z := by
         apply sum_congr rfl
         intro a _
         rw [sum_comm]
    _ = _ := by rw [sum_comm]

/-- Marginal identities express the signed coordinate cost using either coupling. -/
theorem spinExpectationDifference_eq_coupling {ι : Type*} [Fintype ι]
    {p q : FinProb (Config ι)} (c : Coupling p q) :
    spinExpectationDifference p q =
      ∑ η, ∑ ξ, c.mass η ξ * (∑ x, (spinVal (ξ x) - spinVal (η x)) / 2) := by
  have hex (x : ι) :
      (∑ η, ∑ ξ, c.mass η ξ * ((spinVal (ξ x) - spinVal (η x)) / 2)) =
      (q.expect (fun ξ => spinVal (ξ x)) - p.expect (fun η => spinVal (η x))) / 2 := by
    calc (∑ η, ∑ ξ, c.mass η ξ * ((spinVal (ξ x) - spinVal (η x)) / 2))
        = ((∑ η, ∑ ξ, c.mass η ξ * spinVal (ξ x)) -
          (∑ η, ∑ ξ, c.mass η ξ * spinVal (η x))) / 2 := by
            simp only [div_eq_mul_inv, mul_sub, ← mul_assoc, sub_mul,
              sum_sub_distrib, ← sum_mul]
      _ = _ := by rw [c.expect_right, c.expect_left]
  symm
  calc (∑ η, ∑ ξ, c.mass η ξ * (∑ x, (spinVal (ξ x) - spinVal (η x)) / 2))
      = ∑ x, ∑ η, ∑ ξ, c.mass η ξ * ((spinVal (ξ x) - spinVal (η x)) / 2) := by
        simp only [mul_sum]
        exact sum_triple_rotate _
    _ = spinExpectationDifference p q := by
        simp only [hex]
        unfold spinExpectationDifference
        rw [mul_sum]
        apply sum_congr rfl
        intro x _
        ring

/-- Every coupling has at least the coordinatewise expected-spin cost. -/
theorem spinExpectationDifference_le_cost {ι : Type*} [Fintype ι]
    {p q : FinProb (Config ι)} (c : Coupling p q) :
    spinExpectationDifference p q ≤ c.cost hammingR := by
  rw [spinExpectationDifference_eq_coupling c]
  unfold Coupling.cost
  apply sum_le_sum
  intro η _
  apply sum_le_sum
  intro ξ _
  apply mul_le_mul_of_nonneg_left _ (c.nonneg η ξ)
  rw [hammingR_eq_sum]
  exact sum_le_sum fun x _ => spin_discrepancy_lower (η x) (ξ x)

/-- In a monotone coupling, the coordinatewise lower bound is attained exactly. -/
theorem cost_eq_spinExpectationDifference_of_monotone {ι : Type*} [Fintype ι]
    {p q : FinProb (Config ι)} (c : Coupling p q)
    (hmon : ∀ η ξ, c.mass η ξ ≠ 0 → ∀ x, η x ≤ ξ x) :
    c.cost hammingR = spinExpectationDifference p q := by
  rw [spinExpectationDifference_eq_coupling c]
  unfold Coupling.cost
  apply sum_congr rfl
  intro η _
  apply sum_congr rfl
  intro ξ _
  by_cases hz : c.mass η ξ = 0
  · simp [hz]
  · congr 1
    rw [hammingR_eq_sum]
    apply sum_congr rfl
    intro x _
    exact spin_discrepancy_ordered _ _ (hmon η ξ hz x)

/-- Paper (3.22): for stochastically ordered laws, any monotone coupling is optimal. -/
theorem hammingWasserstein_eq_spinExpectationDifference {ι : Type*} [Fintype ι]
    {p q : FinProb (Config ι)} (c : Coupling p q)
    (hmon : ∀ η ξ, c.mass η ξ ≠ 0 → ∀ x, η x ≤ ξ x) :
    hammingWasserstein p q = spinExpectationDifference p q := by
  apply le_antisymm
  · calc hammingWasserstein p q ≤ c.cost hammingR :=
           Wasserstein.le_cost hammingR_nonneg c
      _ = spinExpectationDifference p q := cost_eq_spinExpectationDifference_of_monotone c hmon
  · exact Wasserstein.lower_bound spinExpectationDifference_le_cost

end Paper09
