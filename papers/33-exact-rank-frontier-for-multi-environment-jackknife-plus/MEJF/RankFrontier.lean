import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Prod
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The arithmetic rank frontier

This file formalizes the integer and real arithmetic in Section 3.  `failureRate`
is the explicit formula (3.2), rather than a definition of the statistical
supremum Γ.  Thus these theorems do not assert the statistical sharpness theorem.
-/
namespace MEJF.RankFrontier

noncomputable section

/-- The integer `L` from (3.1). Natural division is the indicated floor when `t ≤ F`. -/
def capacity (m F t ell : ℕ) : ℕ :=
  min m (F * (ell - 1) / (F - t + 1))

/-- The equivalent graph outdegree threshold `w = m-L` in (3.7). -/
def outdegreeDemand (m F t ell : ℕ) : ℕ := m - capacity m F t ell

/-- Numerator of the proposed exact finite-rank failure law, including its two branches. -/
def failureCount (m F t ell : ℕ) : ℕ :=
  if F < t then m + 1 else min (m + 1) (2 * capacity m F t ell + 1)

/-- The scalar formula of (3.2). It is not defined as a supremum over data laws. -/
def failureRate (m F t ell : ℕ) : ℝ :=
  (failureCount m F t ell : ℝ) / (m + 1 : ℕ)

/-- Ceiling of a nonnegative integer divided by two. -/
def halfCeil (D : ℕ) : ℕ := (D + 1) / 2

lemma halfCeil_pos {D : ℕ} (hD : 0 < D) : 0 < halfCeil D := by
  unfold halfCeil
  omega

lemma halfCeil_le {D : ℕ} : halfCeil D ≤ D := by
  unfold halfCeil
  omega

lemma two_mul_add_one_le_iff {L D : ℕ} :
    2 * L + 1 ≤ D ↔ L < halfCeil D := by
  unfold halfCeil
  omega

lemma capacity_le_m (m F t ell : ℕ) : capacity m F t ell ≤ m :=
  min_le_left _ _

lemma capacity_lt_iff {m F t ell q : ℕ} (hqm : q ≤ m)
    (htF : t ≤ F) :
    capacity m F t ell < q ↔ F * (ell - 1) < q * (F - t + 1) := by
  unfold capacity
  rw [min_lt_iff]
  have hd : 0 < F - t + 1 := by omega
  rw [Nat.div_lt_iff_lt_mul hd]
  omega

lemma capacity_one_inner {m F ell : ℕ} (hF : 0 < F) (hell : ell ≤ m + 1) :
    capacity m F 1 ell = ell - 1 := by
  unfold capacity
  have hden : F - 1 + 1 = F := by omega
  rw [hden, Nat.mul_div_right _ hF]
  omega

lemma capacity_one_outer (m F t : ℕ) : capacity m F t 1 = 0 := by
  simp [capacity]

lemma failureCount_le (m F t ell : ℕ) : failureCount m F t ell ≤ m + 1 := by
  unfold failureCount
  split_ifs <;> simp

lemma failureCount_pos (m F t ell : ℕ) : 0 < failureCount m F t ell := by
  unfold failureCount
  split_ifs <;> omega

lemma failureRate_nonneg (m F t ell : ℕ) : 0 ≤ failureRate m F t ell := by
  unfold failureRate
  positivity

lemma failureRate_le_one (m F t ell : ℕ) : failureRate m F t ell ≤ 1 := by
  unfold failureRate
  apply (div_le_one (by positivity : (0 : ℝ) < (m + 1 : ℕ))).mpr
  exact_mod_cast failureCount_le m F t ell

lemma failureRate_lower_bound (m F t ell : ℕ) :
    1 / (m + 1 : ℕ) ≤ failureRate m F t ell := by
  unfold failureRate
  apply (div_le_div_iff_of_pos_right (by positivity)).mpr
  exact_mod_cast failureCount_pos m F t ell

lemma failureRate_high_inner {m F t ell : ℕ} (h : F < t) :
    failureRate m F t ell = 1 := by
  rw [failureRate, failureCount, if_pos h]
  exact div_self (by positivity)

lemma failureRate_one_outer {m F t : ℕ} (htF : t ≤ F) :
    failureRate m F t 1 = 1 / (m + 1 : ℕ) := by
  simp [failureRate, failureCount, not_lt.mpr htF, capacity_one_outer]

lemma failureRate_low_inner {m F ell : ℕ} (hF : 0 < F) (hell : ell ≤ m + 1) :
    failureRate m F 1 ell =
      (min (m + 1) (2 * (ell - 1) + 1) : ℕ) / (m + 1 : ℕ) := by
  simp [failureRate, failureCount, not_lt.mpr (show 1 ≤ F by omega), capacity_one_inner hF hell]

/-- Removing truncation and floor converts the rank budget into a strict product inequality. -/
theorem count_le_budget_iff {m F t ell D : ℕ} (hD : D ≤ m) :
    failureCount m F t ell ≤ D ↔
      t ≤ F ∧ F * (ell - 1) < halfCeil D * (F - t + 1) := by
  unfold failureCount
  by_cases htF : t ≤ F
  · rw [if_neg (not_lt.mpr htF)]
    have hq : halfCeil D ≤ m := le_trans halfCeil_le hD
    rw [min_le_iff]
    have hn : ¬ m + 1 ≤ D := by omega
    simp only [hn, false_or]
    rw [two_mul_add_one_le_iff, capacity_lt_iff hq htF]
    simp [htF]
  · rw [if_pos (by omega : F < t)]
    simp [htF, show ¬ m + 1 ≤ D by omega]

/-- Arithmetic rearrangement in the proof of Corollary 3.2. -/
lemma product_budget_iff {F t ell q : ℕ} (ht : 1 ≤ t) (htF : t ≤ F)
    (hell : 1 ≤ ell) (hq : 1 ≤ q) :
    F * (ell - 1) < q * (F - t + 1) ↔
      ell ≤ q ∧ q * (t - 1) + 1 ≤ F * (q - ell + 1) := by
  have hF : 1 ≤ F := le_trans ht htF
  have h1 : F - t + 1 + (t - 1) = F := by omega
  have h2 : ell - 1 + 1 = ell := by omega
  constructor
  · intro h
    have h3 : q * (F - t + 1) ≤ q * F := Nat.mul_le_mul_left q (by omega)
    have helq : ell ≤ q := by
      by_contra hn
      have hm : q * F ≤ F * (ell - 1) := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left F (by omega : q ≤ ell - 1)
      omega
    refine ⟨helq, ?_⟩
    have h4 : q - ell + 1 + (ell - 1) = q := by omega
    nlinarith [Nat.mul_add q (F - t + 1) (t - 1),
      Nat.mul_add F (q - ell + 1) (ell - 1)]
  · rintro ⟨helq, h⟩
    have h4 : q - ell + 1 + (ell - 1) = q := by omega
    nlinarith [Nat.mul_add q (F - t + 1) (t - 1),
      Nat.mul_add F (q - ell + 1) (ell - 1)]

/-- Corollary 3.2 for an integer failure budget `D = floor (δ N)`. -/
theorem finite_budget_criterion {m F t ell D : ℕ} (hD : 1 ≤ D) (hDm : D ≤ m)
    (ht : 1 ≤ t) (hell : 1 ≤ ell) :
    failureCount m F t ell ≤ D ↔
      t ≤ F ∧ ell ≤ halfCeil D ∧
        halfCeil D * (t - 1) + 1 ≤ F * (halfCeil D - ell + 1) := by
  rw [count_le_budget_iff hDm]
  constructor
  · rintro ⟨htF, h⟩
    exact ⟨htF, (product_budget_iff ht htF hell (halfCeil_pos hD)).mp h⟩
  · rintro ⟨htF, h⟩
    exact ⟨htF, (product_budget_iff ht htF hell (halfCeil_pos hD)).mpr h⟩

/-- There is no positive finite-rank formula within a zero integer failure budget. -/
theorem zero_budget_impossible (m F t ell : ℕ) : ¬ failureCount m F t ell ≤ 0 := by
  have := failureCount_pos m F t ell
  omega

/-- The capacity always includes the ordinary outer-rank allowance. -/
lemma outer_le_capacity {m F t ell : ℕ} (ht : 1 ≤ t) (htF : t ≤ F)
    (hell : ell ≤ m + 1) : ell - 1 ≤ capacity m F t ell := by
  unfold capacity
  rw [le_min_iff]
  refine ⟨by omega, ?_⟩
  rw [Nat.le_div_iff_mul_le (by omega : 0 < F - t + 1)]
  exact Nat.mul_le_mul_left (ell - 1) (by omega : F - t + 1 ≤ F) |>.trans_eq
    (Nat.mul_comm (ell - 1) F)

/-- The arithmetic assertion `w ≤ d` used in Lemma 4.1. -/
lemma outdegreeDemand_le_outerDemand {m F t ell : ℕ} (ht : 1 ≤ t) (htF : t ≤ F)
    (hell : 1 ≤ ell) (helm : ell ≤ m + 1) :
    outdegreeDemand m F t ell ≤ m + 1 - ell := by
  have := outer_le_capacity ht htF helm
  unfold outdegreeDemand
  omega

/-- The nontrivial graph regime implies the endpoint-order assertion `ell ≤ d`. -/
lemma aggregate_rank_nonempty {m F t ell : ℕ} (ht : 1 ≤ t) (htF : t ≤ F)
    (hell : 1 ≤ ell) (helm : ell ≤ m + 1)
    (hw : m / 2 < outdegreeDemand m F t ell) : ell ≤ m + 1 - ell := by
  have := outdegreeDemand_le_outerDemand ht htF hell helm
  omega

/-- Corollary 3.6: the complete-failure phase of the scalar formula. -/
theorem complete_failure_iff {m F t ell : ℕ} :
    failureCount m F t ell = m + 1 ↔
      F < t ∨ (t ≤ F ∧ (F - t + 1) * halfCeil m ≤ F * (ell - 1)) := by
  unfold failureCount
  by_cases h : F < t
  · simp [h]
  · have htF : t ≤ F := by omega
    rw [if_neg h]
    have hq : halfCeil m ≤ m := halfCeil_le
    have hd : 0 < F - t + 1 := by omega
    have hx : m + 1 ≤ 2 * capacity m F t ell + 1 ↔
        halfCeil m ≤ capacity m F t ell := by unfold halfCeil; omega
    rw [min_eq_left_iff, hx]
    unfold capacity
    rw [le_min_iff]
    simp only [hq, true_and]
    rw [Nat.le_div_iff_mul_le hd]
    simp [h, htF, Nat.mul_comm]

/-- The natural half-ceiling is exactly the real ceiling used in (3.8). -/
lemma halfCeil_eq_real_ceil (D : ℕ) : halfCeil D = ⌈(D : ℝ) / 2⌉₊ := by
  by_cases hD : D = 0
  · simp [hD, halfCeil]
  · symm
    apply (Nat.ceil_eq_iff (by have := halfCeil_pos (Nat.pos_of_ne_zero hD); omega)).mpr
    have hlo : 2 * (halfCeil D - 1) < D := by unfold halfCeil; omega
    have hhi : D ≤ 2 * halfCeil D := by unfold halfCeil; omega
    constructor
    · have h : (2 : ℝ) * (halfCeil D - 1 : ℕ) < D := by exact_mod_cast hlo
      linarith
    · have h : (D : ℝ) ≤ 2 * halfCeil D := by exact_mod_cast hhi
      linarith

/-- Real target budgets reduce exactly to a natural floor, with no rounding approximation. -/
lemma rate_le_iff_count_le_floor {m F t ell : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) :
    failureRate m F t ell ≤ δ ↔
      failureCount m F t ell ≤ ⌊δ * (m + 1 : ℕ)⌋₊ := by
  unfold failureRate
  rw [div_le_iff₀ (by positivity)]
  exact (Nat.le_floor_iff (mul_nonneg hδ (by positivity))).symm

lemma floor_budget_le_m {m : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    ⌊δ * (m + 1 : ℕ)⌋₊ ≤ m := by
  have hn : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hf : ⌊δ * (m + 1 : ℕ)⌋₊ < m + 1 := by
    rw [Nat.floor_lt (mul_nonneg hδ hn.le)]
    nlinarith
  omega

/-- Corollary 3.2, for the explicit scalar expression of (3.2). -/
theorem finite_validity_criterion {m F t ell : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (ht : 1 ≤ t) (hell : 1 ≤ ell)
    (hD : 1 ≤ ⌊δ * (m + 1 : ℕ)⌋₊) :
    failureRate m F t ell ≤ δ ↔
      t ≤ F ∧ ell ≤ halfCeil ⌊δ * (m + 1 : ℕ)⌋₊ ∧
        halfCeil ⌊δ * (m + 1 : ℕ)⌋₊ * (t - 1) + 1 ≤
          F * (halfCeil ⌊δ * (m + 1 : ℕ)⌋₊ - ell + 1) := by
  rw [rate_le_iff_count_le_floor hδ.le]
  exact finite_budget_criterion hD (floor_budget_le_m hδ.le hδ1) ht hell

/-- The zero-floor part of Corollary 3.2. -/
theorem zero_floor_impossible {m F t ell : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hD : ⌊δ * (m + 1 : ℕ)⌋₊ = 0) : ¬ failureRate m F t ell ≤ δ := by
  rw [rate_le_iff_count_le_floor hδ, hD]
  exact zero_budget_impossible m F t ell

/-- Complete failure in terms of the real-valued scalar formula. -/
theorem complete_failure_rate_iff {m F t ell : ℕ} :
    failureRate m F t ell = 1 ↔
      F < t ∨ (t ≤ F ∧ (F - t + 1) * halfCeil m ≤ F * (ell - 1)) := by
  rw [← complete_failure_iff]
  unfold failureRate
  rw [div_eq_one_iff_eq (by positivity : (m + 1 : ℕ) ≠ (0 : ℝ))]
  exact Nat.cast_inj

/-- The nontrivial branch of the asymptotic expression in (3.15).
No assertion about convergence of the statistical supremum is made here. -/
def limitingRate (a b α : ℝ) : ℝ :=
  if a < α then min 1 (2 * α * b / (α - a)) else 1

/-- Solving the limiting scalar expression gives the budget line (3.16). -/
theorem limiting_budget_iff {a b α δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ < 1) :
    limitingRate a b α ≤ δ ↔ a / α + 2 * b / δ ≤ 1 := by
  unfold limitingRate
  by_cases haα : a < α
  · rw [if_pos haα, min_le_iff]
    have hden : 0 < α - a := by linarith
    rw [div_le_iff₀ hden]
    have he : a / α + 2 * b / δ ≤ 1 ↔ 2 * α * b ≤ δ * (α - a) := by
      constructor <;> intro h
      · have h' := (mul_le_mul_iff_right₀ (mul_pos hα hδ)).mpr h
        field_simp at h'
        nlinarith
      · apply (mul_le_mul_iff_right₀ (mul_pos hα hδ)).mp
        field_simp
        nlinarith
    rw [he]
    simp [show ¬ 1 ≤ δ by linarith]
  · rw [if_neg haα]
    have hlarge : 1 ≤ a / α := (le_div_iff₀ hα).mpr (by linarith)
    have hpos : 0 < 2 * b / δ := by positivity
    constructor <;> intro h <;> linarith

/-- The algebraic phase boundary (3.18) of the limiting scalar expression. -/
theorem limiting_complete_failure_iff {a b α : ℝ} (hα : 0 < α) :
    limitingRate a b α = 1 ↔
      α ≤ a ∨ (a < α ∧ 1 ≤ a / α + 2 * b) := by
  unfold limitingRate
  by_cases haα : a < α
  · rw [if_pos haα, min_eq_left_iff]
    have hd : 0 < α - a := by linarith
    rw [le_div_iff₀ hd]
    have h : 1 ≤ a / α + 2 * b ↔ α - a ≤ 2 * α * b := by
      constructor <;> intro hh
      · have hh' := (mul_le_mul_iff_right₀ hα).mpr hh
        field_simp at hh'
        nlinarith
      · apply (mul_le_mul_iff_right₀ hα).mp
        field_simp
        nlinarith
    simp only [not_le.mpr haα, false_or, haα, true_and]
    simpa using h.symm
  · simp [haα, le_of_not_gt haα]

/-- The natural numerator formulation is exactly the real min/division in (3.2). -/
lemma failureRate_eq_min {m F t ell : ℕ} (htF : t ≤ F) :
    failureRate m F t ell =
      min 1 ((2 * (capacity m F t ell : ℝ) + 1) / (m + 1 : ℕ)) := by
  rw [failureRate, failureCount, if_neg (not_lt.mpr htF), Nat.cast_min,
    ← min_div_div_right (by positivity : (0 : ℝ) ≤ (m + 1 : ℕ)),
    div_self (by positivity : (m + 1 : ℕ) ≠ (0 : ℝ))]
  norm_cast

/-- The positive lattice cells defined by inequality (3.9). -/
def LatticeValid (F q t ell : ℕ) : Prop :=
  1 ≤ t ∧ t ≤ F ∧ 1 ≤ ell ∧ ell ≤ q ∧
    q * (t - 1) < F * (q - ell + 1)

/-- Coordinatewise Pareto maximality in the positive lattice. -/
def Pareto (F q t ell : ℕ) : Prop :=
  LatticeValid F q t ell ∧
    ∀ t' ell', LatticeValid F q t' ell' → t ≤ t' → ell ≤ ell' →
      t' = t ∧ ell' = ell

/-- Largest admissible outer rank at the fixed inner rank, equation (3.13). -/
def outerTop (F q t : ℕ) : ℕ := q - q * (t - 1) / F

/-- Largest admissible inner rank at the fixed outer rank, equation (3.10). -/
def innerTop (F q ell : ℕ) : ℕ := (F * (q - ell + 1) - 1) / q + 1

lemma outerTop_bounds {F q t : ℕ} (hF : 0 < F) (hq : 0 < q)
    (ht : 1 ≤ t) (htF : t ≤ F) : 1 ≤ outerTop F q t ∧ outerTop F q t ≤ q := by
  have hprod : q * (t - 1) < q * F :=
    Nat.mul_lt_mul_of_pos_left (by omega : t - 1 < F) hq
  have hdiv : q * (t - 1) / F < q := by
    apply (Nat.div_lt_iff_lt_mul hF).mpr
    simpa [Nat.mul_comm] using hprod
  exact ⟨Nat.sub_pos_of_lt hdiv, Nat.sub_le _ _⟩

lemma valid_iff_outerTop {F q t ell : ℕ} (hF : 0 < F) (hq : 0 < q)
    (ht : 1 ≤ t) (htF : t ≤ F) (hell : 1 ≤ ell) :
    LatticeValid F q t ell ↔ ell ≤ outerTop F q t := by
  have hbound := outerTop_bounds hF hq ht htF
  unfold LatticeValid
  simp only [outerTop] at *
  constructor
  · rintro ⟨_, _, _, helq, h⟩
    have hdiv : q * (t - 1) / F < q - ell + 1 := by
      apply (Nat.div_lt_iff_lt_mul hF).mpr
      simpa [Nat.mul_comm] using h
    omega
  · intro he
    have helq : ell ≤ q := by omega
    refine ⟨ht, htF, hell, helq, ?_⟩
    have hd : q * (t - 1) / F < q - ell + 1 := by omega
    have := (Nat.div_lt_iff_lt_mul hF).mp hd
    simpa [Nat.mul_comm] using this

lemma outerTop_valid {F q t : ℕ} (hF : 0 < F) (hq : 0 < q)
    (ht : 1 ≤ t) (htF : t ≤ F) : LatticeValid F q t (outerTop F q t) := by
  exact (valid_iff_outerTop hF hq ht htF (outerTop_bounds hF hq ht htF).1).mpr le_rfl

lemma outerTop_strict {F q t t' : ℕ} (hF : 0 < F) (hFq : F ≤ q)
    (ht : 1 ≤ t) (htt' : t < t') (ht'F : t' ≤ F) :
    outerTop F q t' < outerTop F q t := by
  have hq : 0 < q := lt_of_lt_of_le hF hFq
  have hbt := outerTop_bounds hF hq ht (by omega : t ≤ F)
  have hbt' := outerTop_bounds hF hq (by omega : 1 ≤ t') ht'F
  have hmul := Nat.div_mul_le_self (q * (t - 1)) F
  have hprod : F * (q * (t - 1) / F + 1) ≤ q * (t' - 1) := by
    have hstep : t - 1 + 1 ≤ t' - 1 := by omega
    have := Nat.mul_le_mul_left q hstep
    nlinarith
  have hdiv : q * (t - 1) / F + 1 ≤ q * (t' - 1) / F := by
    apply (Nat.le_div_iff_mul_le hF).mpr
    simpa [Nat.mul_comm] using hprod
  unfold outerTop at *
  omega

lemma innerTop_bounds {F q ell : ℕ} (hF : 0 < F) (hq : 0 < q)
    (hell : 1 ≤ ell) (helq : ell ≤ q) : 1 ≤ innerTop F q ell ∧ innerTop F q ell ≤ F := by
  have hr : 1 ≤ q - ell + 1 := by omega
  have hX : 0 < F * (q - ell + 1) := by positivity
  have hXle : F * (q - ell + 1) ≤ F * q :=
    Nat.mul_le_mul_left F (by omega)
  have hdiv : (F * (q - ell + 1) - 1) / q < F := by
    apply (Nat.div_lt_iff_lt_mul hq).mpr
    omega
  exact ⟨Nat.succ_le_succ (Nat.zero_le _), hdiv⟩

lemma valid_iff_innerTop {F q t ell : ℕ} (hF : 0 < F) (hq : 0 < q)
    (ht : 1 ≤ t) (hell : 1 ≤ ell) (helq : ell ≤ q) :
    LatticeValid F q t ell ↔ t ≤ innerTop F q ell := by
  have hb := innerTop_bounds hF hq hell helq
  have hX : 0 < F * (q - ell + 1) := by positivity
  have hdiv : q * (t - 1) < F * (q - ell + 1) ↔
      t - 1 ≤ (F * (q - ell + 1) - 1) / q := by
    rw [Nat.le_div_iff_mul_le hq, Nat.mul_comm (t - 1) q]
    omega
  unfold LatticeValid innerTop at *
  rw [hdiv]
  omega

lemma innerTop_valid {F q ell : ℕ} (hF : 0 < F) (hq : 0 < q)
    (hell : 1 ≤ ell) (helq : ell ≤ q) : LatticeValid F q (innerTop F q ell) ell := by
  exact (valid_iff_innerTop hF hq (innerTop_bounds hF hq hell helq).1 hell helq).mpr le_rfl

lemma innerTop_strict {F q ell ell' : ℕ} (hq : 0 < q) (hqF : q ≤ F)
    (hell : 1 ≤ ell) (hell' : ell < ell') (hel'q : ell' ≤ q) :
    innerTop F q ell' < innerTop F q ell := by
  have hF : 0 < F := lt_of_lt_of_le hq hqF
  have hx' : 0 < F * (q - ell' + 1) := by positivity
  have hx : 0 < F * (q - ell + 1) := by positivity
  have hdiff : q - ell' + 1 + 1 ≤ q - ell + 1 := by omega
  have hdiff' := Nat.mul_le_mul_left F hdiff
  have hmul := Nat.div_mul_le_self (F * (q - ell' + 1) - 1) q
  have hx1 : F * (q - ell + 1) - 1 + 1 = F * (q - ell + 1) := by omega
  have hx1' : F * (q - ell' + 1) - 1 + 1 = F * (q - ell' + 1) := by omega
  have hprod : ((F * (q - ell' + 1) - 1) / q + 1) * q ≤
      F * (q - ell + 1) - 1 := by nlinarith
  have hdiv := (Nat.le_div_iff_mul_le hq).mpr hprod
  unfold innerTop
  omega

/-- The elementary positive integer ceiling identity underlying equation (3.12). -/
lemma ceil_div_eq_pred_div_add_one {x q : ℕ} (hx : 0 < x) (hq : 0 < q) :
    ⌈(x : ℝ) / q⌉₊ = (x - 1) / q + 1 := by
  apply (Nat.ceil_eq_iff (Nat.succ_ne_zero ((x - 1) / q))).mpr
  have hmul := Nat.div_mul_le_self (x - 1) q
  have hmod := Nat.mod_lt (x - 1) hq
  have heq := Nat.mod_add_div (x - 1) q
  have hx1 : x - 1 + 1 = x := by omega
  have hlow : (x - 1) / q * q < x := by omega
  have hhigh : x ≤ ((x - 1) / q + 1) * q := by nlinarith
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · rw [lt_div_iff₀ hqr]
    exact_mod_cast hlow
  · rw [div_le_iff₀ hqr]
    exact_mod_cast hhigh

/-- Corollary 3.3, equation (3.12), including the real ceiling semantics. -/
lemma innerTop_eq_real_ceil {F q ell : ℕ} (hF : 0 < F) (hq : 0 < q)
    (helq : ell ≤ q) :
    innerTop F q ell = ⌈(F : ℝ) * (q - ell + 1 : ℕ) / q⌉₊ := by
  have hx : 0 < F * (q - ell + 1) := by positivity
  simpa only [innerTop, Nat.cast_mul] using (ceil_div_eq_pred_div_add_one hx hq).symm

/-- For `F ≤ q`, the outer rank strictly decreases at every successive inner rank,
so equation (3.13) enumerates exactly the Pareto antichain. -/
theorem pareto_iff_outer {F q t ell : ℕ} (hF : 0 < F) (hFq : F ≤ q) :
    Pareto F q t ell ↔ 1 ≤ t ∧ t ≤ F ∧ ell = outerTop F q t := by
  have hq : 0 < q := lt_of_lt_of_le hF hFq
  constructor
  · rintro ⟨hv, hmax⟩
    have htop := outerTop_valid hF hq hv.1 hv.2.1
    have hle := (valid_iff_outerTop hF hq hv.1 hv.2.1 hv.2.2.1).mp hv
    have heq := hmax t (outerTop F q t) htop le_rfl hle
    exact ⟨hv.1, hv.2.1, heq.2.symm⟩
  · rintro ⟨ht, htF, rfl⟩
    refine ⟨outerTop_valid hF hq ht htF, ?_⟩
    intro t' ell' hv htt' hell'
    have hle := (valid_iff_outerTop hF hq hv.1 hv.2.1 hv.2.2.1).mp hv
    have heq : t' = t := by
      by_contra hn
      have hs := outerTop_strict hF hFq ht (by omega : t < t') hv.2.1
      omega
    subst t'
    omega

/-- For `q ≤ F`, all outer ranks have strictly decreasing top inner rank.
This is equation (3.14), parametrized by `ell = q-r+1`. -/
theorem pareto_iff_inner {F q t ell : ℕ} (hq : 0 < q) (hqF : q ≤ F) :
    Pareto F q t ell ↔ 1 ≤ ell ∧ ell ≤ q ∧ t = innerTop F q ell := by
  have hF : 0 < F := lt_of_lt_of_le hq hqF
  constructor
  · rintro ⟨hv, hmax⟩
    have htop := innerTop_valid hF hq hv.2.2.1 hv.2.2.2.1
    have hle := (valid_iff_innerTop hF hq hv.1 hv.2.2.1 hv.2.2.2.1).mp hv
    have heq := hmax (innerTop F q ell) ell htop hle le_rfl
    exact ⟨hv.2.2.1, hv.2.2.2.1, heq.1.symm⟩
  · rintro ⟨hell, helq, rfl⟩
    refine ⟨innerTop_valid hF hq hell helq, ?_⟩
    intro t' ell' hv htt' hell'
    have hle := (valid_iff_innerTop hF hq hv.1 hv.2.2.1 hv.2.2.2.1).mp hv
    have heq : ell' = ell := by
      by_contra hn
      have hs := innerTop_strict hq hqF hell (by omega : ell < ell') hv.2.2.2.1
      omega
    subst ell'
    omega

/-- A finite set representing the actual coordinatewise maximal valid cells. -/
def paretoRanks (F q : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 F).product (Finset.Icc 1 q)).filter
    (fun p => Pareto F q p.1 p.2)

lemma mem_paretoRanks {F q : ℕ} {p : ℕ × ℕ} :
    p ∈ paretoRanks F q ↔ Pareto F q p.1 p.2 := by
  classical
  rcases p with ⟨t, ell⟩
  simp only [paretoRanks, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Prod.fst, Prod.snd]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨⟨h.1.1, h.1.2.1⟩, ⟨h.1.2.2.1, h.1.2.2.2.1⟩⟩, h⟩

/-- The finite enumeration (3.13) is exact. -/
theorem paretoRanks_eq_outer {F q : ℕ} (hF : 0 < F) (hFq : F ≤ q) :
    paretoRanks F q = (Finset.Icc 1 F).image (fun t => (t, outerTop F q t)) := by
  classical
  ext p
  rcases p with ⟨t, ell⟩
  rw [mem_paretoRanks, pareto_iff_outer hF hFq]
  simp only [Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]
  constructor
  · rintro ⟨ht, htF, he⟩
    exact ⟨t, ⟨ht, htF⟩, rfl, he.symm⟩
  · rintro ⟨t', ⟨ht', ht'F⟩, rfl, he⟩
    exact ⟨ht', ht'F, he.symm⟩

/-- The finite enumeration (3.14), using the outer rank as index, is exact. -/
theorem paretoRanks_eq_inner {F q : ℕ} (hq : 0 < q) (hqF : q ≤ F) :
    paretoRanks F q = (Finset.Icc 1 q).image (fun ell => (innerTop F q ell, ell)) := by
  classical
  ext p
  rcases p with ⟨t, ell⟩
  rw [mem_paretoRanks, pareto_iff_inner hq hqF]
  simp only [Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]
  constructor
  · rintro ⟨hell, helq, he⟩
    exact ⟨ell, ⟨hell, helq⟩, he.symm, rfl⟩
  · rintro ⟨ell', ⟨hell', hel'q⟩, he, rfl⟩
    exact ⟨hell', hel'q, he.symm⟩

/-- Equation (3.14) with exactly the source's index `r` and real-valued ceiling. -/
theorem paretoRanks_eq_inner_reindexed {F q : ℕ} (hq : 0 < q) (hqF : q ≤ F) :
    paretoRanks F q = (Finset.Icc 1 q).image
      (fun r : ℕ => (⌈(F : ℝ) * r / q⌉₊, q - r + 1)) := by
  classical
  have hF : 0 < F := lt_of_lt_of_le hq hqF
  rw [paretoRanks_eq_inner hq hqF]
  ext p
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨ell, ⟨hell, helq⟩, rfl⟩
    refine ⟨q - ell + 1, ⟨by omega, by omega⟩, ?_⟩
    rw [← innerTop_eq_real_ceil hF hq helq]
    congr 1
    omega
  · rintro ⟨r, ⟨hr, hrq⟩, rfl⟩
    refine ⟨q - r + 1, ⟨by omega, by omega⟩, ?_⟩
    rw [innerTop_eq_real_ceil hF hq (by omega : q - r + 1 ≤ q)]
    have hflip : q - (q - r + 1) + 1 = r := by omega
    simp [hflip]

/-- Corollary 3.3: after retaining only undominated cells, precisely `min F q` remain. -/
theorem paretoRanks_card {F q : ℕ} (hF : 0 < F) (hq : 0 < q) :
    (paretoRanks F q).card = min F q := by
  classical
  by_cases hFq : F ≤ q
  · rw [paretoRanks_eq_outer hF hFq, Finset.card_image_of_injective]
    · simp [min_eq_left hFq]
    · intro a b h
      exact (Prod.mk.inj h).1
  · have hqF : q ≤ F := by omega
    rw [paretoRanks_eq_inner hq hqF, Finset.card_image_of_injective]
    · simp [min_eq_right hqF]
    · intro a b h
      exact (Prod.mk.inj h).2

/-- The arithmetic values underlying Proposition 7.1. -/
theorem ordinary_factor_two_counterexample : failureRate 19 41 40 2 = 1 := by
  norm_num [failureRate, failureCount, capacity]

/-- The arithmetic value underlying the valid pair in Proposition 7.2. -/
theorem nonextreme_example : failureRate 19 4 2 2 = 3 / 20 := by
  norm_num [failureRate, failureCount, capacity]

end

end MEJF.RankFrontier
