/-
Copyright (c) 2026. Finite probability spaces for the Griffiths-exponent paper.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Classical

namespace Paper09

/-- A probability mass function on a finite type, stored as weights. -/
structure FinProb (α : Type*) [Fintype α] where
  w : α → ℝ
  nonneg : ∀ y, 0 ≤ w y
  sum_one : ∑ y, w y = 1

namespace FinProb

variable {α : Type*} [Fintype α]

theorem sum_w (p : FinProb α) : ∑ y, p.w y = 1 := p.sum_one

/-- Expectation of a statistic. -/
def expect (p : FinProb α) (f : α → ℝ) : ℝ := ∑ y, p.w y * f y

@[simp]
theorem expect_const (p : FinProb α) (c : ℝ) : expect p (fun _ => c) = c := by
  show (∑ y, p.w y * c) = c
  have h := sum_mul (univ : Finset α) (fun y => p.w y) c
  -- h : (∑ y, p.w y) * c = ∑ y, p.w y * c
  rw [← h, p.sum_one, one_mul]

theorem expect_add (p : FinProb α) (f g : α → ℝ) :
    expect p (fun y => f y + g y) = expect p f + expect p g := by
  simp only [expect, mul_add, sum_add_distrib]

theorem expect_sub (p : FinProb α) (f g : α → ℝ) :
    expect p (fun y => f y - g y) = expect p f - expect p g := by
  simp only [expect, mul_sub, sum_sub_distrib]

theorem expect_smul (p : FinProb α) (c : ℝ) (f : α → ℝ) :
    expect p (fun y => c * f y) = c * expect p f := by
  simp only [expect]
  calc ∑ y, p.w y * (c * f y) = ∑ y, c * (p.w y * f y) := by
        congr 1; funext y; ring
    _ = c * ∑ y, p.w y * f y := by rw [mul_sum]

theorem expect_mono {p : FinProb α} {f g : α → ℝ} (h : ∀ y, f y ≤ g y) :
    expect p f ≤ expect p g :=
  sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (p.nonneg y)

theorem expect_nonneg {p : FinProb α} {f : α → ℝ} (h : ∀ y, 0 ≤ f y) :
    0 ≤ expect p f :=
  sum_nonneg fun y _ => mul_nonneg (p.nonneg y) (h y)

theorem expect_centered (p : FinProb α) (f : α → ℝ) :
    expect p (fun y => f y - expect p f) = 0 := by
  rw [expect_sub, expect_const]; ring

/-- Variance `E[(f - E f)²]`. -/
def variance (p : FinProb α) (f : α → ℝ) : ℝ :=
  expect p (fun y => (f y - expect p f) * (f y - expect p f))

theorem variance_nonneg (p : FinProb α) (f : α → ℝ) : 0 ≤ variance p f :=
  expect_nonneg fun _ => mul_self_nonneg _

theorem variance_eq_expect (p : FinProb α) (f : α → ℝ) :
    variance p f = expect p (fun y => (f y - expect p f) * (f y - expect p f)) := rfl

theorem variance_le_expect_sq (p : FinProb α) (f : α → ℝ) (c : ℝ) :
    variance p f ≤ expect p (fun y => (f y - c) * (f y - c)) := by
  have hpt : ∀ y, (f y - c) * (f y - c)
      = (f y - expect p f) * (f y - expect p f)
        + 2 * (f y - expect p f) * (expect p f - c)
        + (expect p f - c) * (expect p f - c) := by
    intro y; ring
  have hexpand :
      expect p (fun y => (f y - c) * (f y - c))
      = variance p f + (expect p f - c) * (expect p f - c) := by
    have h1 : expect p (fun y => (f y - c) * (f y - c))
        = expect p (fun y =>
            (f y - expect p f) * (f y - expect p f)
            + 2 * (f y - expect p f) * (expect p f - c)
            + (expect p f - c) * (expect p f - c)) := by
      congr 1; funext y; exact hpt y
    rw [h1, expect_add, expect_add]
    have h2 : expect p (fun y => (f y - expect p f) * (f y - expect p f))
        = variance p f := rfl
    have h3 : expect p (fun y => 2 * (f y - expect p f) * (expect p f - c))
        = (2 * (expect p f - c)) * expect p (fun y => f y - expect p f) := by
      have h := expect_smul p (2 * (expect p f - c)) (fun y => f y - expect p f)
      convert h using 2
      funext y; ring
    have h4 : expect p (fun _ => (expect p f - c) * (expect p f - c))
        = (expect p f - c) * (expect p f - c) := expect_const p _
    have h5 : expect p (fun y => f y - expect p f) = 0 := expect_centered p f
    rw [h2, h3, h4, h5]
    ring
  linarith [mul_self_nonneg (expect p f - c)]

/-- Nonneg statistics inflate under a pointwise density upper bound. -/
theorem expect_of_density_upper {ν μ : FinProb α} {K : ℝ}
    (_hK : 0 ≤ K) (h : ∀ y, μ.w y ≤ K * ν.w y) {g : α → ℝ} (hg : ∀ y, 0 ≤ g y) :
    expect μ g ≤ K * expect ν g := by
  simp only [expect]
  calc ∑ y, μ.w y * g y
      ≤ ∑ y, (K * ν.w y) * g y :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (h y) (hg y)
    _ = K * ∑ y, ν.w y * g y := by
      rw [mul_sum]; congr 1; funext y; ring

/-- Paper (2.3): if `μ.w y ≥ e^{-D} ν.w y` then `Var_μ f ≥ e^{-D} Var_ν f`. -/
theorem variance_of_density_lower {ν μ : FinProb α} {D : ℝ}
    (h : ∀ y, Real.exp (-D) * ν.w y ≤ μ.w y) (f : α → ℝ) :
    Real.exp (-D) * variance ν f ≤ variance μ f := by
  -- For every center `c`, `E_μ[(f-c)²] ≥ e^{-D} E_ν[(f-c)²]`.
  have hpt : ∀ (c : ℝ),
      Real.exp (-D) * expect ν (fun y => (f y - c) * (f y - c))
        ≤ expect μ (fun y => (f y - c) * (f y - c)) := by
    intro c
    simp only [expect]
    calc Real.exp (-D) * ∑ y, ν.w y * ((f y - c) * (f y - c))
        = ∑ y, (Real.exp (-D) * ν.w y) * ((f y - c) * (f y - c)) := by
          rw [mul_sum]; congr 1; funext y; ring
      _ ≤ ∑ y, μ.w y * ((f y - c) * (f y - c)) :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (h y) (mul_self_nonneg _)
  -- Chain: Var_μ = E_μ[(f - E_μ f)²] ≥ e^{-D} E_ν[(f - E_μ f)²] ≥ e^{-D} Var_ν.
  have h1 := hpt (expect μ f)
  have h2 : expect ν (fun y => (f y - expect μ f) * (f y - expect μ f))
      ≥ variance ν f :=
    variance_le_expect_sq ν f (expect μ f)
  have h3 : Real.exp (-D) * variance ν f
      ≤ Real.exp (-D) *
          expect ν (fun y => (f y - expect μ f) * (f y - expect μ f)) := by
    exact mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
  have h4 : variance μ f
      = expect μ (fun y => (f y - expect μ f) * (f y - expect μ f)) := rfl
  linarith

end FinProb

/-! ## Two-point conductance -/

/-- `c(η,η') = π(η)π(η') / (π(η)+π(η'))`. -/
noncomputable def conductance {α : Type*} [Fintype α] (p : FinProb α) (η η' : α) : ℝ :=
  p.w η * p.w η' / (p.w η + p.w η')

theorem conductance_nonneg {α : Type*} [Fintype α] (p : FinProb α) (η η' : α) :
    0 ≤ conductance p η η' := by
  unfold conductance
  by_cases h : p.w η + p.w η' = 0
  · rw [h]; simp
  · exact div_nonneg (mul_nonneg (p.nonneg η) (p.nonneg η'))
      (le_of_lt (lt_of_le_of_ne (add_nonneg (p.nonneg η) (p.nonneg η')) (Ne.symm h)))

/-- Algebraic core: for nonneg `r,r',ν,ν'` with `r,r' ≤ R` and positive denominators,
`r r' ν ν' / (r ν + r' ν') ≤ R ν ν' / (ν + ν')`. -/
theorem conductance_ratio_le_max {r r' ν ν' R : ℝ}
    (hr : 0 ≤ r) (hr' : 0 ≤ r') (hν : 0 ≤ ν) (hν' : 0 ≤ ν')
    (hR : r ≤ R) (hR' : r' ≤ R) (_h0 : 0 ≤ R)
    (hνsum : 0 < ν + ν') (hμsum : 0 < r * ν + r' * ν') :
    (r * ν) * (r' * ν') / (r * ν + r' * ν') ≤ R * (ν * ν' / (ν + ν')) := by
  -- Key inequality: r r' (ν+ν') ≤ R (r ν + r' ν')
  have hkey : r * r' * (ν + ν') ≤ R * (r * ν + r' * ν') := by
    calc r * r' * (ν + ν')
        = r * r' * ν + r * r' * ν' := by ring
      _ ≤ R * r * ν + R * r' * ν' := by
        refine add_le_add ?_ ?_
        · calc r * r' * ν = r * (r' * ν) := by ring
            _ ≤ r * (R * ν) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR' hν) hr
            _ = R * r * ν := by ring
        · calc r * r' * ν' = r' * (r * ν') := by ring
            _ ≤ r' * (R * ν') :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR hν') hr'
            _ = R * r' * ν' := by ring
      _ = R * (r * ν + r' * ν') := by ring
  -- Cross-multiply the goal `(rν)(r'ν')/(rν+r'ν') ≤ R · (νν'/(ν+ν'))`.
  -- Rewrite RHS as a single fraction first.
  have hRform : R * (ν * ν' / (ν + ν')) = (R * (ν * ν')) / (ν + ν') := by
    field_simp [ne_of_gt hνsum]
  rw [hRform, div_le_div_iff₀ hμsum hνsum]
  -- Goal: (rν)(r'ν') * (ν+ν') ≤ (R ν ν') * (rν + r'ν')
  have hLHS : (r * ν) * (r' * ν') * (ν + ν')
      = (ν * ν') * (r * r' * (ν + ν')) := by ring
  have hRHS : (R * (ν * ν')) * (r * ν + r' * ν')
      = (ν * ν') * (R * (r * ν + r' * ν')) := by ring
  rw [hLHS, hRHS]
  by_cases hprod : ν * ν' = 0
  · simp [hprod]
  · have hnn : 0 < ν * ν' := lt_of_le_of_ne (mul_nonneg hν hν') (Ne.symm hprod)
    exact mul_le_mul_of_nonneg_left hkey (le_of_lt hnn)

/-- If `μ.w = r · ν.w` with `0 ≤ r ≤ R`, then `c_μ ≤ R · c_ν`. -/
theorem conductance_of_density {α : Type*} [Fintype α] {ν μ : FinProb α}
    {r : α → ℝ} {R : ℝ}
    (hr : ∀ y, 0 ≤ r y) (hR : ∀ y, r y ≤ R) (h0 : 0 ≤ R)
    (hμ : ∀ y, μ.w y = r y * ν.w y) (η η' : α) :
    conductance μ η η' ≤ R * conductance ν η η' := by
  simp only [conductance, hμ]
  by_cases hsum : ν.w η + ν.w η' = 0
  · have hη : ν.w η = 0 := by
      have h1 : ν.w η ≤ 0 := by
        have : ν.w η ≤ ν.w η + ν.w η' := by linarith [ν.nonneg η']
        linarith
      linarith [ν.nonneg η]
    have hη' : ν.w η' = 0 := by
      have h1 : ν.w η' ≤ 0 := by
        have : ν.w η' ≤ ν.w η + ν.w η' := by linarith [ν.nonneg η]
        linarith
      linarith [ν.nonneg η']
    rw [hη, hη']
    have hzz : r η * (0:ℝ) + r η' * (0:ℝ) = 0 := by ring
    rw [hzz]; simp
  · have hsumpos : 0 < ν.w η + ν.w η' := lt_of_le_of_ne
      (add_nonneg (ν.nonneg η) (ν.nonneg η')) (Ne.symm hsum)
    by_cases hμsum : r η * ν.w η + r η' * ν.w η' = 0
    · have : (r η * ν.w η) * (r η' * ν.w η') / (r η * ν.w η + r η' * ν.w η') = 0 := by
        rw [hμsum]; simp
      rw [this]
      exact mul_nonneg h0 (div_nonneg (mul_nonneg (ν.nonneg η) (ν.nonneg η'))
        (le_of_lt hsumpos))
    · have hμsumpos : 0 < r η * ν.w η + r η' * ν.w η' := lt_of_le_of_ne
        (add_nonneg (mul_nonneg (hr η) (ν.nonneg η))
          (mul_nonneg (hr η') (ν.nonneg η'))) (Ne.symm hμsum)
      exact conductance_ratio_le_max (hr η) (hr η') (ν.nonneg η) (ν.nonneg η')
        (hR η) (hR η') h0 hsumpos hμsumpos

end Paper09
