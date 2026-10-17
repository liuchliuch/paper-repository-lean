/-
Copyright (c) 2026. Finite-field incidence bound (Lemma 3.3) for the
CHSH_r game value.

Core algebraic chain: if `I² ≤ r·I + r²(r-1)` then
`I/r ≤ β_r = (1+√(4r-3))/(2r) ≤ 3/(2√r)`.
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Field

open Real Set BigOperators
open scoped Classical

namespace Paper06

/-! ### Game value and incidence count -/

/-- Winning pairs of the finite-field game: `f(x) + g(y) = x * y`. -/
noncomputable def gameWin {R : Type*} [Fintype R] [Add R] [Mul R]
    (f g : R → R) : Finset (R × R) :=
  Finset.univ.filter fun p => f p.1 + g p.2 = p.1 * p.2

/-- Number of winning pairs `I(f,g)`. -/
noncomputable def Ifg {R : Type*} [Fintype R] [Add R] [Mul R]
    (f g : R → R) : ℕ :=
  (gameWin f g).card

/-- Closed-form incidence bound `β_r = (1 + sqrt(4r-3)) / (2r)`. -/
noncomputable def betaR (r : ℝ) : ℝ :=
  (1 + sqrt (4 * r - 3)) / (2 * r)

/-- The elementary chain `β_r ≤ 3 / (2 √r)` for `r ≥ 1`. -/
theorem betaR_le (r : ℝ) (hr : 1 ≤ r) :
    betaR r ≤ 3 / (2 * sqrt r) := by
  unfold betaR
  have h4r : (0:ℝ) ≤ 4 * r - 3 := by nlinarith
  have hsr : 0 < sqrt r := Real.sqrt_pos.mpr (by linarith)
  have hsqrt : sqrt (4 * r - 3) ≤ 2 * sqrt r := by
    have hmon : (4 * r - 3 : ℝ) ≤ 4 * r := by linarith
    have h := Real.sqrt_le_sqrt hmon
    have h4 : sqrt (4 * r : ℝ) = 2 * sqrt r := by
      have hmul : sqrt ((4:ℝ) * r) = sqrt 4 * sqrt r :=
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) _
      rw [hmul]
      have h2 : sqrt (4:ℝ) = 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num : (0:ℝ) ≤ 4) (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      rw [h2]
    linarith
  have hden : (0:ℝ) < 2 * r := by positivity
  have h1 : (1 + sqrt (4 * r - 3)) / (2 * r)
      ≤ (1 + 2 * sqrt r) / (2 * r) := by
    exact div_le_div_of_nonneg_right (add_le_add_left hsqrt _) (le_of_lt hden)
  have h2 : (1 + 2 * sqrt r) / (2 * r) ≤ 3 / (2 * sqrt r) := by
    have hcross : ((1 + 2 * sqrt r) : ℝ) * (2 * sqrt r) ≤ 3 * (2 * r) := by
      have hsq : sqrt r * sqrt r = r := Real.mul_self_sqrt (by linarith)
      nlinarith
    have hden1 : (0:ℝ) < 2 * r := hden
    have hden2 : (0:ℝ) < 2 * sqrt r := by positivity
    exact (div_le_div_iff₀ hden1 hden2).mpr hcross
  linarith

/-! ### Quadratic incidence inequality -/

/-- Cauchy–Schwarz for a finite family of reals:
`(∑ t)² ≤ r ∑ t²`. -/
theorem sq_sum_le_card_mul_sum_sq' {r : ℕ} (t : Fin r → ℝ) :
    (∑ x : Fin r, t x) ^ 2 ≤ r * ∑ x : Fin r, t x ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin r))) (f := t)
  -- h : (∑ i ∈ univ, t i)² ≤ univ.card * ∑ i ∈ univ, (t i)²
  simpa [Finset.card_fin] using h

/-- Cauchy–Schwarz step: if `I = ∑_{x : Fin r} t x` and
`∑ t x * (t x - 1) ≤ r * (r - 1)` (real form), then `I² ≤ r I + r²(r-1)`. -/
theorem incidence_quadratic_of_pair_bound
    (t : Fin r → ℕ) (I : ℕ)
    (hI : I = ∑ x, t x)
    (hpair : (∑ x, (t x : ℝ) * ((t x : ℝ) - 1)) ≤ r * ((r : ℝ) - 1)) :
    (I : ℝ) * I ≤ r * I + r * r * (r - 1) := by
  classical
  have hIR : (I : ℝ) = ∑ x, (t x : ℝ) := by exact_mod_cast hI
  have hsq : ∑ x, ((t x : ℝ) ^ 2)
      = ∑ x, (t x : ℝ) * ((t x : ℝ) - 1) + ∑ x, (t x : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro x _
    rcases t x with _ | m
    · simp
    · push_cast
      ring
  have hsum : ∑ x, ((t x : ℝ) ^ 2) ≤ r * (r - 1) + I := by
    rw [hsq]
    have h2 : ∑ x, (t x : ℝ) = I := hIR.symm
    nlinarith
  have hcs : (∑ x, (t x : ℝ)) ^ 2 ≤ r * ∑ x, ((t x : ℝ) ^ 2) :=
    sq_sum_le_card_mul_sum_sq' _
  have hfinal : (I : ℝ) * I ≤ r * I + r * r * (r - 1) := by
    have h1 : (I : ℝ) ^ 2 ≤ r * ∑ x, ((t x : ℝ) ^ 2) := by
      have : (I : ℝ) ^ 2 = (∑ x, (t x : ℝ)) ^ 2 := by rw [hIR]
      rw [this]
      exact hcs
    have h2 : r * ∑ x, ((t x : ℝ) ^ 2) ≤ r * (r * (r - 1) + I) := by
      exact mul_le_mul_of_nonneg_left hsum (by exact_mod_cast (Nat.zero_le r))
    nlinarith
  exact hfinal

/-- Root bound: if `I² ≤ r I + r²(r-1)` and `r > 0`, then
`I ≤ r · (1 + sqrt(4r-3)) / 2`. -/
theorem quadratic_root_bound (I r : ℕ) (hr : 0 < r)
    (h : (I : ℝ) * I ≤ r * I + r * r * (r - 1)) :
    (I : ℝ) ≤ r * (1 + sqrt (4 * (r : ℝ) - 3)) / 2 := by
  have hpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hI : (I:ℝ) * I ≤ (r:ℝ) * I + (r:ℝ) * (r:ℝ) * ((r:ℝ) - 1) := h
  have hq : (I:ℝ) ^ 2 - (r:ℝ) * I - (r:ℝ) ^ 2 * ((r:ℝ) - 1) ≤ 0 := by nlinarith
  have hdisc : (r:ℝ) ^ 2 + 4 * (r:ℝ) ^ 2 * ((r:ℝ) - 1)
      = (r:ℝ) ^ 2 * (4 * (r:ℝ) - 3) := by ring_nf
  have h2x : (2 * (I:ℝ) - (r:ℝ)) ^ 2
      ≤ (r:ℝ) ^ 2 + 4 * (r:ℝ) ^ 2 * ((r:ℝ) - 1) := by nlinarith
  by_cases hnn : (0:ℝ) ≤ 2 * (I:ℝ) - (r:ℝ)
  · have hle := Real.sqrt_le_sqrt h2x
    rw [Real.sqrt_sq_eq_abs] at hle
    rw [abs_of_nonneg hnn] at hle
    have hbound : 2 * (I:ℝ) - (r:ℝ)
        ≤ sqrt ((r:ℝ) ^ 2 + 4 * (r:ℝ) ^ 2 * ((r:ℝ) - 1)) := hle
    have hsplit : sqrt ((r:ℝ) ^ 2 * (4 * (r:ℝ) - 3))
        = (r:ℝ) * sqrt (4 * (r:ℝ) - 3) := by
      by_cases h3 : (0:ℝ) ≤ 4 * (r:ℝ) - 3
      · rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (r:ℝ) ^ 2),
            Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hpos)]
      · push_neg at h3
        have hlt : (r:ℝ) < 3/4 := by nlinarith
        have hlt1 : (r:ℝ) < 1 := by nlinarith
        have hr0 : r = 0 := by
          have : r < 1 := by exact_mod_cast hlt1
          omega
        have hz : (r:ℝ) = 0 := by exact_mod_cast hr0
        rw [hz] at hpos
        exact absurd hpos (by norm_num)
    rw [hdisc, hsplit] at hbound
    have : (2:ℝ) * I ≤ (r:ℝ) * (1 + sqrt (4 * (r:ℝ) - 3)) := by nlinarith
    nlinarith
  · push_neg at hnn
    have hIlt : (I:ℝ) < (r:ℝ) / 2 := by nlinarith
    by_cases hrt : (0:ℝ) ≤ 4 * (r:ℝ) - 3
    · have hsqrt : (0:ℝ) ≤ sqrt (4 * (r:ℝ) - 3) := Real.sqrt_nonneg _
      have hge : (1:ℝ) ≤ 1 + sqrt (4 * (r:ℝ) - 3) := by linarith
      have hnonneg : (0:ℝ) ≤ (r:ℝ) := le_of_lt hpos
      have hmul := mul_le_mul_of_nonneg_left hge hnonneg
      have : (r:ℝ) / 2 ≤ (r:ℝ) * (1 + sqrt (4 * (r:ℝ) - 3)) / 2 := by
        nlinarith
      nlinarith
    · push_neg at hrt
      have hlt : (r:ℝ) < 3/4 := by nlinarith
      have hlt1 : (r:ℝ) < 1 := by nlinarith
      have hr0 : r = 0 := by
        have : r < 1 := by exact_mod_cast hlt1
        omega
      have hz : (r:ℝ) = 0 := by exact_mod_cast hr0
      rw [hz] at hpos
      exact absurd hpos (by norm_num)

/-- Dividing the quadratic root bound by `r` yields `I/r ≤ β_r`. -/
theorem quadratic_root_bound_beta (I r : ℕ) (hr : 0 < r)
    (h : (I : ℝ) * I ≤ r * I + r * r * (r - 1)) :
    (I : ℝ) / (r * r) ≤ betaR r := by
  have hpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hroot := quadratic_root_bound I r hr h
  unfold betaR
  have hden1 : (0:ℝ) < (r:ℝ) * (r:ℝ) := by positivity
  have hden2 : (0:ℝ) < 2 * (r:ℝ) := by positivity
  have hbound : (2 * (r:ℝ)) * I
      ≤ (1 + sqrt (4 * (r:ℝ) - 3)) * ((r:ℝ) * (r:ℝ)) := by
    have h2pos : (0:ℝ) < 2 * (r:ℝ) := hden2
    have hmul : (2 * (r:ℝ)) * I
        ≤ (2 * (r:ℝ)) * ((r:ℝ) * (1 + sqrt (4 * (r:ℝ) - 3)) / 2) :=
      mul_le_mul_of_nonneg_left hroot (le_of_lt h2pos)
    have hsimp : (2 * (r:ℝ)) * ((r:ℝ) * (1 + sqrt (4 * (r:ℝ) - 3)) / 2)
        = (1 + sqrt (4 * (r:ℝ) - 3)) * ((r:ℝ) * (r:ℝ)) := by
      field_simp
    rw [hsimp] at hmul
    exact hmul
  have hbound' : (I:ℝ) * (2 * (r:ℝ))
      ≤ (1 + sqrt (4 * (r:ℝ) - 3)) * ((r:ℝ) * (r:ℝ)) := by
    have : (I:ℝ) * (2 * (r:ℝ)) = (2 * (r:ℝ)) * I := by ring
    rw [this]
    exact hbound
  have hbound' : (I:ℝ) * (2 * (r:ℝ))
      ≤ (1 + sqrt (4 * (r:ℝ) - 3)) * ((r:ℝ) * (r:ℝ)) := by
    have hcomm : (I:ℝ) * (2 * (r:ℝ)) = (2 * (r:ℝ)) * I := by ring
    rw [hcomm]
    exact hbound
  exact (div_le_div_iff₀ hden1 hden2).mpr hbound'

/-- **Lemma 3.3**, incidence chain. Given the quadratic bound in real form,
`I/|F|² ≤ β_|F|` and `β_|F| ≤ 3/(2√|F|)`. -/
theorem lemma_3_3_beta_chain
    {F : Type*} [Fintype F] [Field F]
    (I : ℕ)
    (hquad : (I : ℝ) * I ≤ (Fintype.card F : ℝ) * I
        + (Fintype.card F : ℝ) * Fintype.card F * ((Fintype.card F : ℝ) - 1))
    (hcard : 0 < Fintype.card F) :
    (I : ℝ) / (Fintype.card F * Fintype.card F) ≤ betaR (Fintype.card F) ∧
    betaR (Fintype.card F) ≤ 3 / (2 * sqrt (Fintype.card F)) := by
  constructor
  · exact quadratic_root_bound_beta _ _ hcard hquad
  · exact betaR_le _ (by exact_mod_cast (Nat.succ_le_of_lt hcard))

end Paper06
