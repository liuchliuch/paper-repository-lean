/-
Copyright (c) 2026. Soft-shell comparison (Lemma 2.2) analytic core.
-/
import Paper09.FiniteProb
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Exp

open Finset BigOperators Classical Real

namespace Paper09

/-- A finite undirected update graph (one-site heat-bath edges). -/
structure UpdateGraph (α : Type*) where
  edge : α → α → Prop
  symm : ∀ {a b}, edge a b → edge b a

namespace UpdateGraph

variable {α : Type*} [Fintype α]

/-- Dirichlet form `Σ_{a,b} 1_{edge a b} c(π,a,b) (f a - f b)²`. -/
noncomputable def dirichlet (G : UpdateGraph α) (π : FinProb α) (f : α → ℝ) : ℝ :=
  ∑ a : α, ∑ b : α, if G.edge a b then conductance π a b * (f a - f b) ^ 2 else 0

theorem dirichlet_nonneg (G : UpdateGraph α) (π : FinProb α) (f : α → ℝ) :
    0 ≤ G.dirichlet π f := by
  unfold dirichlet
  exact sum_nonneg fun a _ => sum_nonneg fun b _ => by
    by_cases h : G.edge a b
    · rw [if_pos h]
      exact mul_nonneg (conductance_nonneg _ _ _) (sq_nonneg _)
    · rw [if_neg h]

/-- Single-edge conductance comparison from a pointwise density upper bound. -/
theorem conductance_le_of_density {ν μ : FinProb α} {R : ℝ}
    (hR : 0 ≤ R) (h : ∀ y, μ.w y ≤ R * ν.w y) (a b : α) :
    conductance μ a b ≤ R * conductance ν a b := by
  unfold conductance
  by_cases ha : ν.w a = 0
  · have hμa : μ.w a = 0 := by
      have := h a; rw [ha, mul_zero] at this; linarith [μ.nonneg a]
    rw [hμa]
    by_cases hb : μ.w b = 0
    · rw [hb]; simp
      exact mul_nonneg hR (div_nonneg (mul_nonneg (ν.nonneg a) (ν.nonneg b))
        (add_nonneg (ν.nonneg a) (ν.nonneg b)))
    · have : (0:ℝ) * μ.w b / (0 + μ.w b) = 0 := by simp
      rw [this]
      have hν0 : ν.w a * ν.w b / (ν.w a + ν.w b) = 0 := by
        rw [ha]; simp
      rw [hν0]
      exact mul_nonneg hR (le_refl 0)
  by_cases hb : ν.w b = 0
  · have hμb : μ.w b = 0 := by
      have := h b; rw [hb, mul_zero] at this; linarith [μ.nonneg b]
    rw [hμb]
    by_cases ha' : μ.w a = 0
    · rw [ha']; simp
      exact mul_nonneg hR (div_nonneg (mul_nonneg (ν.nonneg a) (ν.nonneg b))
        (add_nonneg (ν.nonneg a) (ν.nonneg b)))
    · have : μ.w a * (0:ℝ) / (μ.w a + 0) = 0 := by simp
      rw [this]
      have hν0 : ν.w a * ν.w b / (ν.w a + ν.w b) = 0 := by
        rw [hb]; simp
      rw [hν0]
      exact mul_nonneg hR (le_refl 0)
  · have hνa : 0 < ν.w a := lt_of_le_of_ne (ν.nonneg a) (Ne.symm ha)
    have hνb : 0 < ν.w b := lt_of_le_of_ne (ν.nonneg b) (Ne.symm hb)
    have hra : 0 ≤ μ.w a / ν.w a := div_nonneg (μ.nonneg a) (le_of_lt hνa)
    have hrb : 0 ≤ μ.w b / ν.w b := div_nonneg (μ.nonneg b) (le_of_lt hνb)
    have hra_le : μ.w a / ν.w a ≤ R := (div_le_iff₀ hνa).mpr (h a)
    have hrb_le : μ.w b / ν.w b ≤ R := (div_le_iff₀ hνb).mpr (h b)
    have e1 : μ.w a / ν.w a * ν.w a = μ.w a := by
      field_simp [ne_of_gt hνa]
    have e2 : μ.w b / ν.w b * ν.w b = μ.w b := by
      field_simp [ne_of_gt hνb]
    by_cases hsum : μ.w a + μ.w b = 0
    · rw [hsum]; simp
      have hν0 : ν.w a * ν.w b / (ν.w a + ν.w b) ≥ 0 :=
        div_nonneg (mul_nonneg (ν.nonneg a) (ν.nonneg b)) (le_of_lt (add_pos hνa hνb))
      exact mul_nonneg hR hν0
    · have hsumpos : 0 < μ.w a + μ.w b := lt_of_le_of_ne
        (add_nonneg (μ.nonneg a) (μ.nonneg b)) (Ne.symm hsum)
      have hνsumpos : 0 < ν.w a + ν.w b := add_pos hνa hνb
      have hcore := conductance_ratio_le_max hra hrb
        (le_of_lt hνa) (le_of_lt hνb) hra_le hrb_le hR hνsumpos (by
          have hform : μ.w a / ν.w a * ν.w a + μ.w b / ν.w b * ν.w b = μ.w a + μ.w b := by
            rw [e1, e2]
          rw [hform]; exact hsumpos)
      -- hcore LHS is (ra νa)(rb νb)/(ra νa + rb νb)
      have hrewL : (μ.w a / ν.w a * ν.w a) * (μ.w b / ν.w b * ν.w b)
            / (μ.w a / ν.w a * ν.w a + μ.w b / ν.w b * ν.w b)
          = μ.w a * μ.w b / (μ.w a + μ.w b) := by
        rw [e1, e2]
      rw [hrewL] at hcore
      exact hcore

/-- Paper (2.4): under `μ.w ≤ e^{D} ν.w`, `ℰ_μ(f,f) ≤ e^{D} ℰ_ν(f,f)`. -/
theorem dirichlet_le_of_density {ν μ : FinProb α} {R : ℝ}
    (hR : 0 ≤ R) (h : ∀ y, μ.w y ≤ R * ν.w y)
    (G : UpdateGraph α) (f : α → ℝ) :
    G.dirichlet μ f ≤ R * G.dirichlet ν f := by
  unfold dirichlet
  have hedge : ∀ a b,
      (if G.edge a b then conductance μ a b * (f a - f b) ^ 2 else 0)
      ≤ R * (if G.edge a b then conductance ν a b * (f a - f b) ^ 2 else 0) := by
    intro a b
    by_cases he : G.edge a b
    · rw [if_pos he, if_pos he]
      have hcond := conductance_le_of_density hR h a b
      have hsq : 0 ≤ (f a - f b) ^ 2 := sq_nonneg _
      have hprod : conductance μ a b * (f a - f b) ^ 2
          ≤ (R * conductance ν a b) * (f a - f b) ^ 2 :=
        mul_le_mul_of_nonneg_right hcond hsq
      have hform : (R * conductance ν a b) * (f a - f b) ^ 2
          = R * (conductance ν a b * (f a - f b) ^ 2) := by ring
      rw [hform] at hprod
      exact hprod
    · rw [if_neg he, if_neg he]; simp
  calc ∑ a, ∑ b, (if G.edge a b then conductance μ a b * (f a - f b) ^ 2 else 0)
      ≤ ∑ a, ∑ b, R * (if G.edge a b then conductance ν a b * (f a - f b) ^ 2 else 0) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => hedge a b
    _ = R * ∑ a, ∑ b, (if G.edge a b then conductance ν a b * (f a - f b) ^ 2 else 0) := by
      rw [mul_sum]; congr 1; funext a; rw [mul_sum]

/-- Paper (2.3)–(2.4) product form:
under `e^{-D}ν ≤ μ ≤ e^{D}ν`,
`ℰ_μ(f,f) · Var_ν(f) ≤ e^{2D} ℰ_ν(f,f) · Var_μ(f)`. -/
theorem rayleigh_product_le {ν μ : FinProb α} {G : UpdateGraph α} {D : ℝ}
    (hlo : ∀ y, exp (-D) * ν.w y ≤ μ.w y)
    (hhi : ∀ y, μ.w y ≤ exp D * ν.w y)
    (f : α → ℝ) :
    G.dirichlet μ f * FinProb.variance ν f
      ≤ exp (2 * D) * (G.dirichlet ν f * FinProb.variance μ f) := by
  have hdir : G.dirichlet μ f ≤ exp D * G.dirichlet ν f :=
    dirichlet_le_of_density (exp_nonneg _) hhi G f
  have hvar : exp (-D) * FinProb.variance ν f ≤ FinProb.variance μ f :=
    FinProb.variance_of_density_lower hlo f
  have hνvar : 0 ≤ FinProb.variance ν f := FinProb.variance_nonneg _ _
  have hμdir : 0 ≤ G.dirichlet ν f := G.dirichlet_nonneg _ _
  have hμvar : 0 ≤ FinProb.variance μ f := FinProb.variance_nonneg _ _
  have hvarν_le : FinProb.variance ν f ≤ exp D * FinProb.variance μ f := by
    have h1 : exp (-D) * FinProb.variance ν f ≤ FinProb.variance μ f := hvar
    have h2 : exp D * exp (-D) = (1:ℝ) := by
      rw [← exp_add, add_neg_cancel, exp_zero]
    calc FinProb.variance ν f
        = 1 * FinProb.variance ν f := (one_mul _).symm
      _ = (exp D * exp (-D)) * FinProb.variance ν f := by rw [h2]
      _ = exp D * (exp (-D) * FinProb.variance ν f) := by ring
      _ ≤ exp D * FinProb.variance μ f := mul_le_mul_of_nonneg_left h1 (le_of_lt (exp_pos _))
  have step1 : G.dirichlet μ f * FinProb.variance ν f
      ≤ (exp D * G.dirichlet ν f) * FinProb.variance ν f :=
    mul_le_mul_of_nonneg_right hdir hνvar
  have step2 : (exp D * G.dirichlet ν f) * FinProb.variance ν f
      ≤ exp D * G.dirichlet ν f * (exp D * FinProb.variance μ f) := by
    nlinarith [mul_nonneg (le_of_lt (exp_pos D)) hμdir, hvarν_le,
      mul_nonneg (le_of_lt (exp_pos D)) hμvar]
  have step3 : exp D * G.dirichlet ν f * (exp D * FinProb.variance μ f)
      = exp (2 * D) * (G.dirichlet ν f * FinProb.variance μ f) := by
    have h : exp (2 * D) = exp D * exp D := by
      rw [← exp_add]; ring_nf
    rw [h]; ring
  nlinarith [step1, step2, step3]

end UpdateGraph

/-! ## Lemma 2.2 certificate -/

/-- Abstract Lemma 2.2 (soft-shell Rayleigh comparison).

If `ℰ_ν(f,f) ≤ gapν · Var_ν(f)` and the law `μ` satisfies the oscillation
sandwich `e^{-D}ν ≤ μ ≤ e^{D}ν`, then
`ℰ_μ(f,f) · Var_ν(f) ≤ e^{2D} gapν Var_ν(f) Var_μ(f)`. -/
theorem lemma_2_2_soft_shell {α : Type*} [Fintype α]
    {G : UpdateGraph α} {ν μ : FinProb α} {D gapν : ℝ}
    (f : α → ℝ)
    (hgap : G.dirichlet ν f ≤ gapν * FinProb.variance ν f)
    (hlo : ∀ y, exp (-D) * ν.w y ≤ μ.w y)
    (hhi : ∀ y, μ.w y ≤ exp D * ν.w y) :
    G.dirichlet μ f * FinProb.variance ν f
      ≤ exp (2 * D) * (gapν * FinProb.variance ν f * FinProb.variance μ f) := by
  have hprod := UpdateGraph.rayleigh_product_le (G := G) hlo hhi f
  have hνvar : 0 ≤ FinProb.variance ν f := FinProb.variance_nonneg _ _
  have hμvar : 0 ≤ FinProb.variance μ f := FinProb.variance_nonneg _ _
  have hμdir : 0 ≤ G.dirichlet ν f := G.dirichlet_nonneg _ _
  have hstep : exp (2 * D) * (G.dirichlet ν f * FinProb.variance μ f)
      ≤ exp (2 * D) * (gapν * FinProb.variance ν f * FinProb.variance μ f) := by
    have h1 : G.dirichlet ν f * FinProb.variance μ f
        ≤ gapν * FinProb.variance ν f * FinProb.variance μ f := by
      nlinarith [hgap, hμvar]
    exact mul_le_mul_of_nonneg_left h1 (le_of_lt (exp_pos (2 * D)))
  nlinarith [hprod, hstep]

end Paper09
