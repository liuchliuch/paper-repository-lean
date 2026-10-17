import Paper15.Basic

/-!
# Lemma 7 (Stationary laws coincide)

Every interior stationary point of `M₂` subject to `M₁ = M₃ = 0` for the
exceptional table satisfies `x₁ = x₂ = x₃` and `y₁ = y₂ = y₃`.

Following Section 4, Lagrange multipliers produce constants `a, b, c` with
`b = a + 8/3` and the six derivative equations (22)–(23).  We show that these
equations force all `x_i` to coincide and all `y_i` to coincide.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace Paper15

open Finset Real BigOperators

/-! ## Lagrange coefficients (21) -/

/-- Coefficient `a = 4/3 + 4μ` of (21). -/
def lagA (μ : ℝ) : ℝ := (4 : ℝ) / 3 + 4 * μ

/-- Coefficient `b = 4 + 4μ` of (21). -/
def lagB (μ : ℝ) : ℝ := 4 + 4 * μ

/-- Coefficient `c = -4/3 - (2/3)λ - 2μ` of (21). -/
def lagC (lam μ : ℝ) : ℝ := -(4 : ℝ) / 3 - (2 : ℝ) / 3 * lam - 2 * μ

/-- The identity `b = a + 8/3` used throughout the proof of Lemma 7. -/
theorem lagB_eq_lagA_add (μ : ℝ) : lagB μ = lagA μ + 8 / 3 := by
  simp only [lagA, lagB]
  ring

/-- Same identity in the form used by `lemma7`. -/
theorem lagB_sub_lagA (μ : ℝ) : lagB μ - lagA μ = 8 / 3 := by
  rw [lagB_eq_lagA_add]; ring

/-! ## Helper lemmas for the six derivative equations -/

/-- The three quantities `w_i = (a x_i + c) / y_i` satisfy `w_j + w_k = -b`. -/
theorem w_sum_eq {x y : Fin 3 → ℝ} {a b c : ℝ}
    (hy : ∀ i, 0 < y i)
    (h22 : ∀ j k, j ≠ k →
      c * (y j + y k) + b * (y j * y k) + a * (x j * y k + y j * x k) = 0)
    (j k : Fin 3) (hjk : j ≠ k) :
    (a * x j + c) / y j + (a * x k + c) / y k = -b := by
  have yj : y j ≠ 0 := (hy j).ne'
  have yk : y k ≠ 0 := (hy k).ne'
  have h := h22 j k hjk
  field_simp [yj, yk]
  nlinarith

/-- From `w_j + w_k = -b` for all pairs, every `w_i` equals `-b/2`. -/
theorem w_eq_neg_half {x y : Fin 3 → ℝ} {a b c : ℝ}
    (h22w : ∀ j k, j ≠ k →
      (a * x j + c) / y j + (a * x k + c) / y k = -b) :
    (a * x 0 + c) / y 0 = -b / 2 ∧
    (a * x 1 + c) / y 1 = -b / 2 ∧
    (a * x 2 + c) / y 2 = -b / 2 := by
  have h01 := h22w 0 1 (by decide)
  have h02 := h22w 0 2 (by decide)
  have h12 := h22w 1 2 (by decide)
  have e12 : (a * x 1 + c) / y 1 = (a * x 2 + c) / y 2 := by nlinarith
  have e01 : (a * x 0 + c) / y 0 = (a * x 1 + c) / y 1 := by nlinarith
  have e0 : 2 * ((a * x 0 + c) / y 0) = -b := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- Equation (24): with `h = -c/a` and `d = b/(2a)`, one has `x_i = h - d y_i`. -/
theorem x_eq_h_sub_d_y {x y : Fin 3 → ℝ} {a b c h d : ℝ}
    (hane : a ≠ 0)
    (hdef : h = -c / a) (ddef : d = b / (2 * a))
    (hw : ∀ i, (a * x i + c) / y i = -b / 2)
    (hy : ∀ i, 0 < y i) :
    ∀ i, x i = h - d * y i := by
  intro i
  have hyi : y i ≠ 0 := (hy i).ne'
  have h := hw i
  have key : a * x i + c = -b * y i / 2 := by
    field_simp [hyi] at h ⊢
    nlinarith
  rw [hdef, ddef]
  field_simp [hane]
  nlinarith [key]

/-- Substituting `x_i = h - d y_i`, `b = 2 a d`, `c = -a h` into (23) and
dividing by `a` yields equation (25). -/
theorem eq25 {x y : Fin 3 → ℝ} {a b c h d : ℝ}
    (hane : a ≠ 0)
    (hdef : h = -c / a) (ddef : d = b / (2 * a))
    (hx : ∀ i, x i = h - d * y i)
    (h23 : ∀ j k, j ≠ k →
      c * (x j + y j + x k + y k) + b * (y j * y k + x j * y k + y j * x k)
        + a * (x j * x k) = 0)
    (j k : Fin 3) (hjk : j ≠ k) :
    -h ^ 2 + h * (2 * d - 1) * (y j + y k) + d * (2 - 3 * d) * (y j * y k) = 0 := by
  have h23' := h23 j k hjk
  have c_eq : c = -a * h := by
    rw [hdef]; field_simp [hane]
  have b_eq : b = 2 * a * d := by
    rw [ddef]; field_simp [hane]
  rw [c_eq, b_eq, hx j, hx k] at h23'
  have poly :
      -a * h * (h - d * y j + y j + (h - d * y k) + y k)
        + 2 * a * d * (y j * y k + (h - d * y j) * y k + y j * (h - d * y k))
        + a * ((h - d * y j) * (h - d * y k))
      = a * (-h ^ 2 + h * (2 * d - 1) * (y j + y k) + d * (2 - 3 * d) * (y j * y k)) := by
    ring
  rw [poly] at h23'
  exact (mul_eq_zero.mp h23').resolve_left hane

/-- Equation (26): subtracting pairs of (25) gives `(y_i - y_j)(P + Q y_k) = 0`
for pairwise distinct `i, j, k`. -/
theorem eq26 {h P Q : ℝ} {y : Fin 3 → ℝ}
    (h25 : ∀ j k, j ≠ k →
      -h ^ 2 + P * (y j + y k) + Q * (y j * y k) = 0)
    {i j k : Fin 3} (hik : i ≠ k) (hjk : j ≠ k) :
    (y i - y j) * (P + Q * y k) = 0 := by
  have e1 := h25 i k hik
  have e2 := h25 j k hjk
  nlinarith [e1, e2]

/-! ## The case `a = 0` -/

/-- If `a = 0`, equation (22) forces all `y_i` to coincide. -/
theorem y_eq_of_a_zero_eq22 {y : Fin 3 → ℝ} {b c : ℝ}
    (hy : ∀ i, 0 < y i) (hb : b ≠ 0)
    (g01 : c * (y 0 + y 1) + b * (y 0 * y 1) = 0)
    (g02 : c * (y 0 + y 2) + b * (y 0 * y 2) = 0)
    (g12 : c * (y 1 + y 2) + b * (y 1 * y 2) = 0) :
    y 0 = y 1 ∧ y 1 = y 2 := by
  have y0 : 0 < y 0 := hy 0
  have y1 : 0 < y 1 := hy 1
  have y2 : 0 < y 2 := hy 2
  by_cases he : y 0 = y 1
  · by_cases he2 : y 1 = y 2
    · exact ⟨he, he2⟩
    · -- y0 = y1 ≠ y2
      have ceq : c = -b * y 0 / 2 := by
        have h : c * (y 0 + y 0) + b * (y 0 * y 0) = 0 := by
          rw [← he] at g01
          exact g01
        have h2 : y 0 * (2 * c + b * y 0) = 0 := by nlinarith [h]
        have h3 : 2 * c + b * y 0 = 0 := by
          rcases mul_eq_zero.mp h2 with h | h
          · exact absurd h y0.ne'
          · exact h
        nlinarith [h3]
      have y0eq2 : y 0 = y 2 := by
        have h := g02
        rw [ceq] at h
        have h2 : b * y 0 * (y 2 - y 0) = 0 := by nlinarith
        have h3 : y 2 - y 0 = 0 := by
          rcases mul_eq_zero.mp h2 with h | h
          · exact absurd h (mul_ne_zero hb y0.ne')
          · exact h
        exact (sub_eq_zero.mp h3).symm
      exact absurd y0eq2 (fun h => he2 (he.symm.trans h))
  · -- y0 ≠ y1
    by_cases he2 : y 1 = y 2
    · -- y1 = y2 ≠ y0
      have ceq : c = -b * y 1 / 2 := by
        have h : c * (y 1 + y 1) + b * (y 1 * y 1) = 0 := by
          rw [← he2] at g12
          exact g12
        have h2 : y 1 * (2 * c + b * y 1) = 0 := by nlinarith [h]
        have h3 : 2 * c + b * y 1 = 0 := by
          rcases mul_eq_zero.mp h2 with h | h
          · exact absurd h y1.ne'
          · exact h
        nlinarith [h3]
      have y0eq1 : y 0 = y 1 := by
        have h := g01
        rw [ceq] at h
        have h2 : b * y 1 * (y 0 - y 1) = 0 := by nlinarith
        have h3 : y 0 - y 1 = 0 := by
          rcases mul_eq_zero.mp h2 with h | h
          · exact absurd h (mul_ne_zero hb y1.ne')
          · exact h
        exact sub_eq_zero.mp h3
      exact absurd y0eq1 he
    · -- y0 ≠ y1, y1 ≠ y2
      have f1 : (y 1 - y 2) * (c + b * y 0) = 0 := by nlinarith [g01, g02]
      have ceq : c = -b * y 0 := by
        rcases mul_eq_zero.mp f1 with h | h
        · exact absurd h (sub_ne_zero.mpr he2)
        · linarith
      have y0eq : y 0 = 0 := by
        have h := g01
        rw [ceq] at h
        have h2 : b * y 0 * y 0 = 0 := by nlinarith
        have h3 : y 0 = 0 := by
          rcases mul_eq_zero.mp h2 with h | h
          · exact absurd h (mul_ne_zero hb y0.ne')
          · exact h
        exact h3
      exact absurd y0eq y0.ne'

/-- When `a = 0`, equations (22)–(23) are contradictory on the positive orthant. -/
theorem a_zero_contradiction {x y : Fin 3 → ℝ} {b c : ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hbpos : 0 < b)
    (g01 : c * (y 0 + y 1) + b * (y 0 * y 1) = 0)
    (g02 : c * (y 0 + y 2) + b * (y 0 * y 2) = 0)
    (g12 : c * (y 1 + y 2) + b * (y 1 * y 2) = 0)
    (h23_01 : c * (x 0 + y 0 + x 1 + y 1) + b * (y 0 * y 1 + x 0 * y 1 + y 0 * x 1) = 0) :
    False := by
  have hb : b ≠ 0 := hbpos.ne'
  have yeq := y_eq_of_a_zero_eq22 hy hb g01 g02 g12
  have y0 : 0 < y 0 := hy 0
  have x0 : 0 < x 0 := hx 0
  have x1 : 0 < x 1 := hx 1
  have ceq : c = -b * y 0 / 2 := by
    have h : c * (y 0 + y 0) + b * (y 0 * y 0) = 0 := by
      rw [← yeq.1] at g01
      exact g01
    have h2 : y 0 * (2 * c + b * y 0) = 0 := by nlinarith [h]
    have h3 : 2 * c + b * y 0 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h y0.ne'
      · exact h
    nlinarith [h3]
  have key : (b * y 0 / 2) * (x 0 + x 1) = 0 := by
    have h := h23_01
    rw [ceq, yeq.1, yeq.2] at h
    ring_nf at h
    nlinarith
  have pos : 0 < (b * y 0 / 2) * (x 0 + x 1) :=
    mul_pos (by nlinarith [hbpos, y0]) (add_pos x0 x1)
  exact absurd key pos.ne'

/-! ## Equation (25) forces `h ≠ 0` and then all `y_i` coincide -/

/-- If `h = 0`, positivity forces `d < 0` while (25) forces `d = 0` or `d = 2/3`. -/
theorem h_ne_zero_of_eq25 {x y : Fin 3 → ℝ} {h d : ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (xsub : ∀ i, x i = h - d * y i)
    (h25_01 : -h ^ 2 + h * (2 * d - 1) * (y 0 + y 1) + d * (2 - 3 * d) * (y 0 * y 1) = 0) :
    h ≠ 0 := by
  intro hh
  have y0 : 0 < y 0 := hy 0
  have y1 : 0 < y 1 := hy 1
  have x0 : 0 < x 0 := hx 0
  have dneg : d < 0 := by
    have := xsub 0
    rw [hh] at this
    nlinarith [x0, y0]
  have h01 := h25_01
  rw [hh] at h01
  have dz : d * (2 - 3 * d) * (y 0 * y 1) = 0 := by nlinarith
  have d2 : d * (2 - 3 * d) = 0 := by
    rcases mul_eq_zero.mp dz with h | h
    · exact h
    · exact absurd h (mul_ne_zero y0.ne' y1.ne')
  rcases mul_eq_zero.mp d2 with h | h
  · exact absurd h (by linarith)
  · have : d = 2 / 3 := by nlinarith
    exact absurd this (by linarith)

/-- Given (25) in the form with `P, Q`, if two `y` values coincide and `P + Q y = 0`
for that value, one reaches a contradiction. -/
theorem two_y_eq_contradiction {x y : Fin 3 → ℝ} {h d P Q : ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hh : h ≠ 0)
    (xsub : ∀ i, x i = h - d * y i)
    (Pdef : P = h * (2 * d - 1)) (Qdef : Q = d * (2 - 3 * d))
    (h25P : ∀ j k, j ≠ k → -h ^ 2 + P * (y j + y k) + Q * (y j * y k) = 0)
    (i j : Fin 3) (hij : i ≠ j)
    (veq : y i = y j)
    (pqi : P + Q * y i = 0) :
    False := by
  have xipos : 0 < x i := hx i
  have xjpos : 0 < x j := hx j
  have yipos : 0 < y i := hy i
  have h25_ij := h25P i j hij
  -- P = -Q * y i
  have peq : P = -Q * y i := by nlinarith [pqi]
  -- -h² - Q y_i² = 0
  have e1 : h ^ 2 + Q * y i ^ 2 = 0 := by
    have := h25_ij
    rw [veq, peq] at this
    nlinarith
  -- h² Q + P² = Q (h² + Q y_i²) = 0
  have key : h ^ 2 * Q + P ^ 2 = 0 := by
    rw [peq]
    have factor : h ^ 2 * Q + (-Q * y i) ^ 2 = Q * (h ^ 2 + Q * y i ^ 2) := by ring
    rw [factor]
    exact mul_eq_zero_of_right _ e1
  have factor : h ^ 2 * Q + P ^ 2 = h ^ 2 * (d - 1) ^ 2 := by
    rw [Pdef, Qdef]
    ring
  have h2d : h ^ 2 * (d - 1) ^ 2 = 0 := by
    rw [← factor]; exact key
  have d1 : d = 1 := by
    rcases mul_eq_zero.mp h2d with hsq | hsq
    · exact absurd (pow_eq_zero hsq) hh
    · exact sub_eq_zero.mp (pow_eq_zero hsq)
  -- then (25) reads -x_i x_j = 0
  have xprod : x i * x j = 0 := by
    have h25' := h25P i j hij
    rw [Pdef, Qdef, d1] at h25'
    have xieq : x i = h - y i := by rw [xsub i, d1]; ring
    have xjeq : x j = h - y j := by rw [xsub j, d1]; ring
    have : x i * x j = h ^ 2 - h * (y i + y j) + y i * y j := by
      rw [xieq, xjeq, veq]; ring
    rw [this]
    nlinarith [h25']
  exact absurd xprod (mul_ne_zero xipos.ne' xjpos.ne')

/-- All `y_i` coincide under the hypotheses of the main argument. -/
theorem y_all_eq {x y : Fin 3 → ℝ} {h d P Q : ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hh : h ≠ 0)
    (xsub : ∀ i, x i = h - d * y i)
    (Pdef : P = h * (2 * d - 1)) (Qdef : Q = d * (2 - 3 * d))
    (h25P : ∀ j k, j ≠ k → -h ^ 2 + P * (y j + y k) + Q * (y j * y k) = 0)
    (e26_01 : (y 0 - y 1) * (P + Q * y 2) = 0)
    (e26_02 : (y 0 - y 2) * (P + Q * y 1) = 0)
    (e26_12 : (y 1 - y 2) * (P + Q * y 0) = 0) :
    y 0 = y 1 ∧ y 1 = y 2 := by
  have hy01 : y 0 = y 1 := by
    by_contra hne
    push_neg at hne
    -- y0 ≠ y1
    by_cases h12 : y 1 = y 2
    · -- y1 = y2 ≠ y0: use the equal pair (1,2)
      have y02ne : y 0 ≠ y 2 := fun h => hne (h.trans h12.symm)
      have pq1 : P + Q * y 1 = 0 := by
        rcases mul_eq_zero.mp e26_02 with h | h
        · exact absurd h (sub_ne_zero.mpr y02ne)
        · exact h
      exact two_y_eq_contradiction hx hy hh xsub Pdef Qdef h25P 1 2 (by decide) h12 pq1
    · by_cases h02 : y 0 = y 2
      · -- y0 = y2 ≠ y1: use the equal pair (0,2)
        have y12ne : y 1 ≠ y 2 := h12
        have pq0 : P + Q * y 0 = 0 := by
          rcases mul_eq_zero.mp e26_12 with h | h
          · exact absurd h (sub_ne_zero.mpr y12ne)
          · exact h
        exact two_y_eq_contradiction hx hy hh xsub Pdef Qdef h25P 0 2 (by decide) h02 pq0
      · -- all three distinct
        have pq2 : P + Q * y 2 = 0 := by
          rcases mul_eq_zero.mp e26_01 with h | h
          · exact absurd h (sub_ne_zero.mpr hne)
          · exact h
        have pq1 : P + Q * y 1 = 0 := by
          rcases mul_eq_zero.mp e26_02 with h | h
          · exact absurd h (sub_ne_zero.mpr h02)
          · exact h
        have pq0 : P + Q * y 0 = 0 := by
          rcases mul_eq_zero.mp e26_12 with h | h
          · exact absurd h (sub_ne_zero.mpr h12)
          · exact h
        by_cases hQ : Q = 0
        · -- Q = 0, P = 0, (25) gives h = 0
          have P0 : P = 0 := by
            have := pq0
            rw [hQ] at this
            nlinarith
          have h25_01 := h25P 0 1 (by decide)
          rw [hQ, P0] at h25_01
          have : h ^ 2 = 0 := by nlinarith
          exact absurd (pow_eq_zero this) hh
        · -- Q ≠ 0: all y equal to -P/Q
          have y01eq : y 0 = y 1 := by
            have : Q * (y 0 - y 1) = 0 := by nlinarith [pq0, pq1]
            rcases mul_eq_zero.mp this with h | h
            · exact absurd h hQ
            · exact sub_eq_zero.mp h
          exact hne y01eq
  have hy12 : y 1 = y 2 := by
    by_contra hne
    push_neg at hne
    -- y1 ≠ y2, y0 = y1 so y0 ≠ y2
    have y02ne : y 0 ≠ y 2 := fun h => hne (hy01.symm.trans h)
    have pq1 : P + Q * y 1 = 0 := by
      rcases mul_eq_zero.mp e26_02 with h | h
      · exact absurd h (sub_ne_zero.mpr y02ne)
      · exact h
    have pq0 : P + Q * y 0 = 0 := by
      rw [← hy01] at pq1
      exact pq1
    exact two_y_eq_contradiction hx hy hh xsub Pdef Qdef h25P 0 1 (by decide) hy01 pq0
  exact ⟨hy01, hy12⟩

/-! ## Lemma 7 (Stationary laws coincide) -/

set_option linter.unusedVariables false

/-- Lemma 7 (Stationary laws coincide).  Given positive interior coordinates
and constants `a, b, c` with `b = a + 8/3` satisfying the six derivative
equations (22)–(23), one has `x₀ = x₁ = x₂` and `y₀ = y₁ = y₂`. -/
theorem lemma7 {x y : Fin 3 → ℝ} {a b c : ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hsum : ∀ i, x i + y i < 1)
    (hb : b = a + 8 / 3)
    (h22 : ∀ j k, j ≠ k →
      c * (y j + y k) + b * (y j * y k) + a * (x j * y k + y j * x k) = 0)
    (h23 : ∀ j k, j ≠ k →
      c * (x j + y j + x k + y k) + b * (y j * y k + x j * y k + y j * x k)
        + a * (x j * x k) = 0) :
    x 0 = x 1 ∧ x 1 = x 2 ∧ y 0 = y 1 ∧ y 1 = y 2 := by
  -- Step 1: a ≠ 0
  by_cases hane : a = 0
  · -- a = 0, so b = 8/3 > 0; (22) forces all y equal, then (23) contradicts
    subst hane
    have bpos : 0 < b := by rw [hb]; norm_num
    have g01 : c * (y 0 + y 1) + b * (y 0 * y 1) = 0 := by simpa using h22 0 1 (by decide)
    have g02 : c * (y 0 + y 2) + b * (y 0 * y 2) = 0 := by simpa using h22 0 2 (by decide)
    have g12 : c * (y 1 + y 2) + b * (y 1 * y 2) = 0 := by simpa using h22 1 2 (by decide)
    have h23' : c * (x 0 + y 0 + x 1 + y 1) + b * (y 0 * y 1 + x 0 * y 1 + y 0 * x 1) = 0 := by
      simpa using h23 0 1 (by decide)
    exact (a_zero_contradiction hx hy bpos g01 g02 g12 h23').elim
  · -- a ≠ 0
    push_neg at hane
    set h : ℝ := -c / a with hdef
    set d : ℝ := b / (2 * a) with ddef
    have hw : ∀ i, (a * x i + c) / y i = -b / 2 := by
      intro i
      have w := w_eq_neg_half (fun j k hjk => w_sum_eq hy h22 j k hjk)
      match i with
      | 0 => exact w.1
      | 1 => exact w.2.1
      | 2 => exact w.2.2
    have xsub : ∀ i, x i = h - d * y i :=
      x_eq_h_sub_d_y hane hdef ddef hw hy
    have h25 : ∀ j k, j ≠ k →
        -h ^ 2 + h * (2 * d - 1) * (y j + y k) + d * (2 - 3 * d) * (y j * y k) = 0 :=
      fun j k hjk => eq25 hane hdef ddef xsub h23 j k hjk
    set P : ℝ := h * (2 * d - 1) with Pdef
    set Q : ℝ := d * (2 - 3 * d) with Qdef
    have h25P : ∀ j k, j ≠ k →
        -h ^ 2 + P * (y j + y k) + Q * (y j * y k) = 0 := by
      intro j k hjk
      simpa [Pdef, Qdef] using h25 j k hjk
    have e26_01 : (y 0 - y 1) * (P + Q * y 2) = 0 :=
      eq26 h25P (by decide) (by decide)
    have e26_02 : (y 0 - y 2) * (P + Q * y 1) = 0 :=
      eq26 h25P (by decide) (by decide)
    have e26_12 : (y 1 - y 2) * (P + Q * y 0) = 0 :=
      eq26 h25P (by decide) (by decide)
    have hh : h ≠ 0 :=
      h_ne_zero_of_eq25 hx hy xsub (h25 0 1 (by decide))
    have yeq : y 0 = y 1 ∧ y 1 = y 2 :=
      y_all_eq hx hy hh xsub Pdef Qdef h25P e26_01 e26_02 e26_12
    have xeq : x 0 = x 1 ∧ x 1 = x 2 := by
      constructor
      · rw [xsub 0, xsub 1, yeq.1]
      · rw [xsub 1, xsub 2, yeq.2]
    exact ⟨xeq.1, xeq.2, yeq.1, yeq.2⟩

end Paper15
