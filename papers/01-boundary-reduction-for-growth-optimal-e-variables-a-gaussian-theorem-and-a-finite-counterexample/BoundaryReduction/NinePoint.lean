/-
Copyright (c) 2026. Nine-point natural exponential family and the
explicit exterior mixture Q_t of Appendix A in
"Boundary reduction for growth-optimal e-variables".

Complete sorry-free construction of the finite alphabet, base masses,
exponential tilts, the eight exposing normals, and the analytic bounds
of Lemma A.1 (exposure gap, A.2, exterior feasibility, χ² estimate A.4).
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import BoundaryReduction.Numerical
import BoundaryReduction.FiniteKL

open Real Set BigOperators
open scoped Classical

namespace BoundaryReduction.NinePoint

/-! ## Constants -/

/-- Origin mass of `P₀`. -/
noncomputable def ε : ℝ := Numerical.ε

/-- Uniform mass of each of the eight nonzero alphabet points. -/
noncomputable def w : ℝ := (1 - ε) / 8

/-- Diagonal radius. -/
noncomputable def ρ : ℝ := Numerical.ρ

/-- Excluded ball radius in mean space. -/
noncomputable def r₀ : ℝ := Numerical.r₀

theorem ε_eq : ε = 1 / 10 ^ 15 := by
  unfold ε Numerical.ε; norm_num

theorem ε_pos : 0 < ε := by
  unfold ε; exact Numerical.ε_pos

theorem ε_lt_one : ε < 1 := by
  unfold ε; exact Numerical.ε_lt_one

theorem w_eq : w = (1 - ε) / 8 := rfl

theorem w_pos : 0 < w := by
  unfold w
  have : 0 < 1 - ε := by
    have := ε_lt_one; linarith
  positivity

theorem eight_w : 8 * w = 1 - ε := by
  unfold w
  field_simp

theorem ρ_eq : ρ = 4 / (5 * Real.sqrt 2) := by
  unfold ρ Numerical.ρ; rfl

theorem ρ_sq : ρ ^ 2 = 8 / 25 := by
  unfold ρ; exact Numerical.ρ_sq

theorem ρ_pos : 0 < ρ := by
  unfold ρ; exact Numerical.ρ_pos

theorem r₀_eq : r₀ = 1 / 100 := by
  unfold r₀ Numerical.r₀; rfl

theorem r₀_pos : 0 < r₀ := by
  unfold r₀; exact Numerical.r₀_pos

theorem r₀_sq : r₀ ^ 2 = 1 / 10000 := by
  unfold r₀; exact Numerical.r₀_sq

/-! ## The nine-point alphabet

Indexing of the nine points of `𝒴` as `Fin 9`:
`0` is the origin; `1..4` the axis points `(±1,0),(0,±1)`;
`5..8` the diagonal points `(±ρ,±ρ)`.
-/

/-- Coordinates of the nine points in `ℝ²`. -/
noncomputable def coord : Fin 9 → ℝ × ℝ
  | ⟨0, _⟩ => (0, 0)
  | ⟨1, _⟩ => (1, 0)
  | ⟨2, _⟩ => (-1, 0)
  | ⟨3, _⟩ => (0, 1)
  | ⟨4, _⟩ => (0, -1)
  | ⟨5, _⟩ => (ρ, ρ)
  | ⟨6, _⟩ => (ρ, -ρ)
  | ⟨7, _⟩ => (-ρ, ρ)
  | ⟨_, _⟩ => (-ρ, -ρ)

/-- Base masses of `P₀`: `ε` at the origin, `w` at each nonzero point. -/
noncomputable def p0 : Fin 9 → ℝ
  | ⟨0, _⟩ => ε
  | ⟨_, _⟩ => w

theorem p0_nonneg : ∀ y, 0 ≤ p0 y := by
  intro y
  match y with
  | ⟨0, _⟩ => exact le_of_lt ε_pos
  | ⟨n+1, _⟩ => exact le_of_lt w_pos

theorem p0_pos : ∀ y, 0 < p0 y := by
  intro y
  match y with
  | ⟨0, _⟩ => exact ε_pos
  | ⟨n+1, _⟩ => exact w_pos

theorem p0_eq : ∀ y : Fin 9, p0 y = if y.val = 0 then ε else w := by
  intro y
  match y with
  | ⟨0, _⟩ => simp [p0]
  | ⟨n+1, h⟩ => simp [p0, show (n+1 : ℕ) ≠ 0 from by omega]

theorem p0_sum : ∑ y : Fin 9, p0 y = 1 := by
  have hex : (∑ y : Fin 9, p0 y)
      = p0 0 + p0 1 + p0 2 + p0 3 + p0 4 + p0 5 + p0 6 + p0 7 + p0 8 := by
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    simp [Fin.sum_univ_zero]
    ring
  rw [hex]
  have e0 : p0 0 = ε := rfl
  have e1 : p0 1 = w := rfl
  have e2 : p0 2 = w := rfl
  have e3 : p0 3 = w := rfl
  have e4 : p0 4 = w := rfl
  have e5 : p0 5 = w := rfl
  have e6 : p0 6 = w := rfl
  have e7 : p0 7 = w := rfl
  have e8 : p0 8 = w := rfl
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8]
  have : (ε + w + w + w + w + w + w + w + w : ℝ) = ε + 8 * w := by ring
  rw [this, eight_w]
  ring


/-! ## Exponential tilts -/

/-- Dot product in `ℝ²`. -/
noncomputable def dot (θ y : ℝ × ℝ) : ℝ := θ.1 * y.1 + θ.2 * y.2

theorem dot_comm (θ y : ℝ × ℝ) : dot θ y = dot y θ := by
  unfold dot; ring

/-- Unnormalised tilted mass `exp(θ·y) p₀(y)`. -/
noncomputable def un (θ : ℝ × ℝ) (y : Fin 9) : ℝ :=
  Real.exp (dot θ (coord y)) * p0 y

/-- Partition function `Z(θ) = ∑_y exp(θ·y) p₀(y)`. -/
noncomputable def Z (θ : ℝ × ℝ) : ℝ := ∑ y, un θ y

theorem Z_pos (θ : ℝ × ℝ) : 0 < Z θ := by
  unfold Z un
  exact Finset.sum_pos (fun y _ => mul_pos (Real.exp_pos _) (p0_pos y))
    Finset.univ_nonempty

/-- Tilted probability mass. -/
noncomputable def pt (θ : ℝ × ℝ) (y : Fin 9) : ℝ := un θ y / Z θ

theorem pt_pos (θ : ℝ × ℝ) (y : Fin 9) : 0 < pt θ y := by
  unfold pt un
  exact div_pos (mul_pos (Real.exp_pos _) (p0_pos y)) (Z_pos θ)

theorem pt_sum (θ : ℝ × ℝ) : ∑ y, pt θ y = 1 := by
  unfold pt
  have h : ∀ y, un θ y / Z θ = un θ y * (Z θ)⁻¹ := fun _ => div_eq_mul_inv _ _
  rw [Finset.sum_congr rfl (fun y _ => h y)]
  have h2 : (∑ y, un θ y * (Z θ)⁻¹) = (∑ y, un θ y) * (Z θ)⁻¹ :=
    (Finset.sum_mul (s := Finset.univ) (f := fun y => un θ y) (a := (Z θ)⁻¹)).symm
  rw [h2]
  have : (∑ y, un θ y) = Z θ := rfl
  rw [this]
  exact mul_inv_cancel₀ (ne_of_gt (Z_pos θ))

theorem pt_eq (θ : ℝ × ℝ) (y : Fin 9) :
    pt θ y = Real.exp (dot θ (coord y)) * p0 y / Z θ := rfl

/-! ## The eight exposing normals -/

/-- Axis normals: `n = (±1,0)` and `n = (0,±1)`. -/
noncomputable def axisNormal : Fin 4 → ℝ × ℝ
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (-1, 0)
  | ⟨2, _⟩ => (0, 1)
  | ⟨_, _⟩ => (0, -1)

/-- Diagonal normals: `n = (±1,±1)`. -/
noncomputable def diagNormal : Fin 4 → ℝ × ℝ
  | ⟨0, _⟩ => (1, 1)
  | ⟨1, _⟩ => (1, -1)
  | ⟨2, _⟩ => (-1, 1)
  | ⟨_, _⟩ => (-1, -1)

/-- Target axis point of the `i`-th axis normal. -/
noncomputable def axisTarget : Fin 4 → Fin 9
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨_, _⟩ => 4

/-- Target diagonal point of the `i`-th diagonal normal. -/
noncomputable def diagTarget : Fin 4 → Fin 9
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 6
  | ⟨2, _⟩ => 7
  | ⟨_, _⟩ => 8

theorem coord_axisTarget (i : Fin 4) :
    coord (axisTarget i) = match i.val with
      | 0 => (1, 0) | 1 => (-1, 0) | 2 => (0, 1) | _ => (0, -1) := by
  fin_cases i <;> rfl

theorem coord_diagTarget (i : Fin 4) :
    coord (diagTarget i) = match i.val with
      | 0 => (ρ, ρ) | 1 => (ρ, -ρ) | 2 => (-ρ, ρ) | _ => (-ρ, -ρ) := by
  fin_cases i <;> rfl

/-! ## Exposure gaps (Appendix A) -/

/-- Exposure gap of an axis normal: `n·(y_j - y) ≥ 1 - ρ` for `y ≠ y_j`. -/
noncomputable def γ : ℝ := 2 * ρ - 1

theorem γ_eq : γ = 2 * ρ - 1 := rfl

theorem γ_pos : 0 < γ := by
  unfold γ
  have h : (1 : ℝ) < 2 * ρ := by
    unfold ρ; exact Numerical.two_ρ_gt_one
  have : (0:ℝ) < 2 * ρ - 1 := by linarith
  exact this

theorem γ_gt : (13 / 100 : ℝ) < γ := by
  unfold γ
  have h := Numerical.gamma_exposure_gap
  -- h : 13/100 < 2 * Numerical.ρ - 1
  exact h

theorem one_sub_ρ_gt_third : (1 / 3 : ℝ) < 1 - ρ := by
  have h2 : ρ < 2 / 3 := by
    unfold ρ; exact Numerical.ρ_lt_two_thirds
  have : (1 / 3 : ℝ) < 1 - ρ := by linarith
  exact this

theorem one_sub_ρ_gt_γ : γ < 1 - ρ := by
  unfold γ
  have h2 : ρ < 2 / 3 := by
    unfold ρ; exact Numerical.ρ_lt_two_thirds
  have : (2 * ρ - 1 : ℝ) < 1 - ρ := by linarith
  exact this


/-! ## Exposure inequality (A.2)

For an axis normal `n` and its target `y_j`, every other alphabet point
satisfies `n·(y_j - y) ≥ γ`. Hence after normalising by the target mass,
the total non-target mass is at most `β_t = 8 exp(-t γ)`.
-/

/-- `n·(y_j - y)` for an axis normal. -/
noncomputable def axisGap (i : Fin 4) (y : Fin 9) : ℝ :=
  dot (axisNormal i) (coord (axisTarget i)) - dot (axisNormal i) (coord y)

/-- `n·(y_j - y)` for a diagonal normal. -/
noncomputable def diagGap (i : Fin 4) (y : Fin 9) : ℝ :=
  dot (diagNormal i) (coord (diagTarget i)) - dot (diagNormal i) (coord y)

/-- Base-mass ratio `p₀(y)/p₀(y_j)` for an axis target (mass `w`). -/
theorem p0_ratio_axis (y : Fin 9) (i : Fin 4) :
    p0 y / p0 (axisTarget i) = if y.val = 0 then 8 * ε / (1 - ε) else 1 := by
  have ht : p0 (axisTarget i) = w := by fin_cases i <;> rfl
  rw [ht]
  by_cases hy : y = (0 : Fin 9)
  · subst hy
    have hp : p0 (0 : Fin 9) = ε := rfl
    have hv : (0 : Fin 9).val = 0 := rfl
    rw [hp, if_pos hv]
    unfold w
    field_simp
  · have hval : y.val ≠ 0 := by
      intro h
      apply hy
      ext
      simpa using h
    have hp : p0 y = w := by
      match y with
      | ⟨0, _⟩ => exact absurd rfl hy
      | ⟨n+1, _⟩ => rfl
    rw [hp, if_neg hval, div_self (ne_of_gt w_pos)]

/-- The origin ratio is `< 1`. -/
theorem origin_ratio_lt_one : 8 * ε / (1 - ε) < 1 := by
  have h := Numerical.ε_div_one_sub_lt
  have h2 : ε / (1 - ε) < 2 * (10 : ℝ) ^ (-15 : ℤ) := by
    unfold ε
    exact Numerical.ε_div_one_sub_lt
  have h3 : (2 * (10:ℝ) ^ (-15:ℤ)) < 1 := by
    norm_num [zpow_neg, zpow_ofNat]
  have : 8 * (ε / (1 - ε)) < 8 * (2 * (10:ℝ) ^ (-15:ℤ)) := by
    have h4 : 0 < 1 - ε := by
      have := ε_lt_one; linarith
    nlinarith
  have h5 : 8 * ε / (1 - ε) = 8 * (ε / (1 - ε)) := by ring
  rw [h5]
  nlinarith


/-! ## Concrete gap computations

Each exposure gap is an explicit algebraic number. We record the four
representative axis gaps and the diagonal minimum `γ`.
-/

theorem axisGap_self (i : Fin 4) : axisGap i (axisTarget i) = 0 := by
  unfold axisGap
  ring

theorem axisGap_origin (i : Fin 4) : axisGap i 0 = 1 := by
  unfold axisGap dot
  fin_cases i <;> simp [axisNormal, axisTarget, coord] <;> ring


/-- Minimum diagonal gap equals `γ = 2ρ - 1`. -/
theorem diagGap_min : γ = 2 * ρ - 1 := rfl


/-- Axis exposure gap is at least `γ` away from the target. -/
theorem axisGap_ge (i : Fin 4) (y : Fin 9) (h : y ≠ axisTarget i) :
    γ ≤ axisGap i y := by
  revert h
  unfold γ axisGap dot
  fin_cases i <;> fin_cases y <;>
    simp only [axisNormal, axisTarget, coord] <;>
    intro h <;>
    first
    | exact absurd rfl h
    | nlinarith [ρ_pos, Numerical.ρ_gt_half, Numerical.ρ_lt_two_thirds, ρ_sq]

/-- Diagonal exposure gap is at least `γ` away from the target. -/
theorem diagGap_ge (i : Fin 4) (y : Fin 9) (h : y ≠ diagTarget i) :
    γ ≤ diagGap i y := by
  revert h
  unfold γ diagGap dot
  fin_cases i <;> fin_cases y <;>
    simp only [diagNormal, diagTarget, coord] <;>
    intro h <;>
    first
    | exact absurd rfl h
    | nlinarith [ρ_pos, Numerical.ρ_gt_half, Numerical.ρ_lt_two_thirds, ρ_sq]


/-! ## Pointwise tilt ratios (key step of A.2) -/

theorem dot_smul (t : ℝ) (θ y : ℝ × ℝ) : dot (t • θ) y = t * dot θ y := by
  unfold dot
  simp [smul_eq_mul]
  ring

theorem un_smul (t : ℝ) (θ : ℝ × ℝ) (y : Fin 9) :
    un (t • θ) y = Real.exp (t * dot θ (coord y)) * p0 y := by
  unfold un
  rw [dot_smul]

/-- **Pointwise ratio for an axis normal.**
`un(t•n)(y) / un(t•n)(target) = (p₀ y / p₀ target) * exp(-t * gap)`. -/
theorem axis_un_ratio (i : Fin 4) (t : ℝ) (y : Fin 9) :
    un (t • axisNormal i) y / un (t • axisNormal i) (axisTarget i)
      = (p0 y / p0 (axisTarget i)) * Real.exp (-t * axisGap i y) := by
  unfold axisGap
  have hnum : un (t • axisNormal i) y
      = Real.exp (t * dot (axisNormal i) (coord y)) * p0 y :=
    un_smul t (axisNormal i) y
  have hden : un (t • axisNormal i) (axisTarget i)
      = Real.exp (t * dot (axisNormal i) (coord (axisTarget i))) * p0 (axisTarget i) :=
    un_smul t (axisNormal i) (axisTarget i)
  rw [hnum, hden]
  have hp : 0 < p0 (axisTarget i) := p0_pos _
  have hexp : Real.exp (t * dot (axisNormal i) (coord (axisTarget i))) > 0 :=
    Real.exp_pos _
  have h : (Real.exp (t * dot (axisNormal i) (coord y)) * p0 y)
      / (Real.exp (t * dot (axisNormal i) (coord (axisTarget i))) * p0 (axisTarget i))
      = (p0 y / p0 (axisTarget i))
        * (Real.exp (t * dot (axisNormal i) (coord y))
            / Real.exp (t * dot (axisNormal i) (coord (axisTarget i)))) := by
    field_simp
  rw [h]
  have hexp2 : Real.exp (t * dot (axisNormal i) (coord y))
      / Real.exp (t * dot (axisNormal i) (coord (axisTarget i)))
      = Real.exp (t * dot (axisNormal i) (coord y)
          - t * dot (axisNormal i) (coord (axisTarget i))) := by
    rw [← Real.exp_sub]
  rw [hexp2]
  have harg : t * dot (axisNormal i) (coord y)
      - t * dot (axisNormal i) (coord (axisTarget i))
      = -t * (dot (axisNormal i) (coord (axisTarget i))
          - dot (axisNormal i) (coord y)) := by
    ring
  rw [harg]

/-- Pointwise ratio for a diagonal normal. -/
theorem diag_un_ratio (i : Fin 4) (t : ℝ) (y : Fin 9) :
    un (t • diagNormal i) y / un (t • diagNormal i) (diagTarget i)
      = (p0 y / p0 (diagTarget i)) * Real.exp (-t * diagGap i y) := by
  unfold diagGap
  have hnum : un (t • diagNormal i) y
      = Real.exp (t * dot (diagNormal i) (coord y)) * p0 y :=
    un_smul t (diagNormal i) y
  have hden : un (t • diagNormal i) (diagTarget i)
      = Real.exp (t * dot (diagNormal i) (coord (diagTarget i))) * p0 (diagTarget i) :=
    un_smul t (diagNormal i) (diagTarget i)
  rw [hnum, hden]
  have h : (Real.exp (t * dot (diagNormal i) (coord y)) * p0 y)
      / (Real.exp (t * dot (diagNormal i) (coord (diagTarget i))) * p0 (diagTarget i))
      = (p0 y / p0 (diagTarget i))
        * (Real.exp (t * dot (diagNormal i) (coord y))
            / Real.exp (t * dot (diagNormal i) (coord (diagTarget i)))) := by
    field_simp
  rw [h]
  have hexp2 : Real.exp (t * dot (diagNormal i) (coord y))
      / Real.exp (t * dot (diagNormal i) (coord (diagTarget i)))
      = Real.exp (t * dot (diagNormal i) (coord y)
          - t * dot (diagNormal i) (coord (diagTarget i))) := by
    rw [← Real.exp_sub]
  rw [hexp2]
  have harg : t * dot (diagNormal i) (coord y)
      - t * dot (diagNormal i) (coord (diagTarget i))
      = -t * (dot (diagNormal i) (coord (diagTarget i))
          - dot (diagNormal i) (coord y)) := by
    ring
  rw [harg]


/-- Base-mass ratio at a diagonal target (also mass `w`). -/
theorem p0_ratio_diag (y : Fin 9) (i : Fin 4) :
    p0 y / p0 (diagTarget i) = if y.val = 0 then 8 * ε / (1 - ε) else 1 := by
  have ht : p0 (diagTarget i) = w := by fin_cases i <;> rfl
  rw [ht]
  by_cases hy : y = (0 : Fin 9)
  · subst hy
    have hp : p0 (0 : Fin 9) = ε := rfl
    have hv : (0 : Fin 9).val = 0 := rfl
    rw [hp, if_pos hv]
    unfold w
    field_simp
  · have hval : y.val ≠ 0 := by
      intro h
      apply hy
      ext
      simpa using h
    have hp : p0 y = w := by
      match y with
      | ⟨0, _⟩ => exact absurd rfl hy
      | ⟨n+1, _⟩ => rfl
    rw [hp, if_neg hval, div_self (ne_of_gt w_pos)]

/-- Mass ratio is at most 1 at an axis target. -/
theorem p0_ratio_axis_le_one (y : Fin 9) (i : Fin 4) :
    p0 y / p0 (axisTarget i) ≤ 1 := by
  rw [p0_ratio_axis]
  by_cases hy : y.val = 0
  · rw [if_pos hy]
    have h := origin_ratio_lt_one
    linarith
  · rw [if_neg hy]

/-- Mass ratio is at most 1 at a diagonal target. -/
theorem p0_ratio_diag_le_one (y : Fin 9) (i : Fin 4) :
    p0 y / p0 (diagTarget i) ≤ 1 := by
  rw [p0_ratio_diag]
  by_cases hy : y.val = 0
  · rw [if_pos hy]
    have h := origin_ratio_lt_one
    linarith
  · rw [if_neg hy]

/-- **A.2 pointwise (axis).** For `t ≥ 0` and `y ≠ target`,
`un(t•n)(y)/un(t•n)(target) ≤ exp(-t γ)`. -/
theorem axis_ratio_le_exp (i : Fin 4) (t : ℝ) (ht : 0 ≤ t)
    (y : Fin 9) (hy : y ≠ axisTarget i) :
    un (t • axisNormal i) y / un (t • axisNormal i) (axisTarget i)
      ≤ Real.exp (-t * γ) := by
  rw [axis_un_ratio]
  have hmass : p0 y / p0 (axisTarget i) ≤ 1 := p0_ratio_axis_le_one y i
  have hgap : γ ≤ axisGap i y := axisGap_ge i y hy
  have h1 : Real.exp (-t * axisGap i y) ≤ Real.exp (-t * γ) := by
    rw [Real.exp_le_exp]
    -- -t * gap ≤ -t * γ  since t≥0 and γ≤gap
    have : -t * axisGap i y ≤ -t * γ := by nlinarith
    exact this
  have hprod : (p0 y / p0 (axisTarget i)) * Real.exp (-t * axisGap i y)
      ≤ 1 * Real.exp (-t * γ) := by
    have hne : 0 ≤ Real.exp (-t * axisGap i y) := le_of_lt (Real.exp_pos _)
    nlinarith
  have h1' : (1 : ℝ) * Real.exp (-t * γ) = Real.exp (-t * γ) := by ring
  rw [h1'] at hprod
  exact hprod

/-- **A.2 pointwise (diagonal).** For `t ≥ 0` and `y ≠ target`,
`un(t•n)(y)/un(t•n)(target) ≤ exp(-t γ)`. -/
theorem diag_ratio_le_exp (i : Fin 4) (t : ℝ) (ht : 0 ≤ t)
    (y : Fin 9) (hy : y ≠ diagTarget i) :
    un (t • diagNormal i) y / un (t • diagNormal i) (diagTarget i)
      ≤ Real.exp (-t * γ) := by
  rw [diag_un_ratio]
  have hmass : p0 y / p0 (diagTarget i) ≤ 1 := p0_ratio_diag_le_one y i
  have hgap : γ ≤ diagGap i y := diagGap_ge i y hy
  have h1 : Real.exp (-t * diagGap i y) ≤ Real.exp (-t * γ) := by
    rw [Real.exp_le_exp]
    have : -t * diagGap i y ≤ -t * γ := by nlinarith
    exact this
  have hprod : (p0 y / p0 (diagTarget i)) * Real.exp (-t * diagGap i y)
      ≤ 1 * Real.exp (-t * γ) := by
    have hne : 0 ≤ Real.exp (-t * diagGap i y) := le_of_lt (Real.exp_pos _)
    nlinarith
  have h1' : (1 : ℝ) * Real.exp (-t * γ) = Real.exp (-t * γ) := by ring
  rw [h1'] at hprod
  exact hprod


/-! ## Sum of non-target masses (A.2) -/

theorem un_pos (θ : ℝ × ℝ) (y : Fin 9) : 0 < un θ y :=
  mul_pos (Real.exp_pos _) (p0_pos y)

/-- Z splits as target plus non-target unnormalised mass. -/
theorem Z_axis_split (i : Fin 4) (t : ℝ) :
    Z (t • axisNormal i)
      = un (t • axisNormal i) (axisTarget i)
        + ∑ y, (if y = axisTarget i then (0 : ℝ) else un (t • axisNormal i) y) := by
  unfold Z
  have hsum := Finset.sum_eq_add_sum_diff_singleton
    (s := Finset.univ) (f := un (t • axisNormal i))
    (i := axisTarget i) (h := Finset.mem_univ (axisTarget i))
  rw [hsum]
  have h : ∑ y ∈ Finset.univ \ {axisTarget i}, un (t • axisNormal i) y
      = ∑ y, (if y = axisTarget i then (0 : ℝ) else un (t • axisNormal i) y) := by
    rw [Finset.sum_ite]
    have h1 : (∑ x with x = axisTarget i, (0:ℝ)) = 0 := by simp
    have h2 : (∑ x with ¬ x = axisTarget i, un (t • axisNormal i) x)
        = ∑ y ∈ Finset.univ \ {axisTarget i}, un (t • axisNormal i) y := by
      have : Finset.univ.filter (fun x => ¬ x = axisTarget i)
          = Finset.univ \ {axisTarget i} := by
        ext y
        simp [not_iff_not]
      rw [this]
    rw [h1, h2, zero_add]
  rw [h]

/-- A.2 sum form (axis): non-target mass / target mass ≤ 8 exp(-tγ). -/
theorem axis_nontarget_ratio (i : Fin 4) (t : ℝ) (ht : 0 ≤ t) :
    (∑ y, (if y = axisTarget i then (0 : ℝ) else un (t • axisNormal i) y))
      / un (t • axisNormal i) (axisTarget i)
      ≤ 8 * Real.exp (-t * γ) := by
  have hfilter : (∑ y, (if y = axisTarget i then (0 : ℝ)
      else un (t • axisNormal i) y))
      = ∑ y ∈ Finset.univ.filter (fun y => y ≠ axisTarget i),
          un (t • axisNormal i) y := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro y _
    by_cases hy : y = axisTarget i
    · rw [if_pos hy]
      have hnn : ¬ (y ≠ axisTarget i) := fun h => h hy
      rw [if_neg hnn]
    · rw [if_neg hy, if_pos hy]
  have hdiv : (∑ y ∈ Finset.univ.filter (fun y => y ≠ axisTarget i),
      un (t • axisNormal i) y) / un (t • axisNormal i) (axisTarget i)
      = ∑ y ∈ Finset.univ.filter (fun y => y ≠ axisTarget i),
          un (t • axisNormal i) y / un (t • axisNormal i) (axisTarget i) := by
    have key := Finset.sum_mul
      (s := Finset.univ.filter (fun y => y ≠ axisTarget i))
      (f := fun y => un (t • axisNormal i) y)
      (a := (un (t • axisNormal i) (axisTarget i))⁻¹)
    rw [div_eq_mul_inv, key]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [div_eq_mul_inv]
  rw [hfilter, hdiv]
  have h8 : (Finset.univ.filter (fun y : Fin 9 => y ≠ axisTarget i)).card = 8 := by
    have heq : Finset.univ.filter (fun y : Fin 9 => y ≠ axisTarget i)
        = Finset.univ \ {axisTarget i} := by
      ext y
      simp [and_comm]
    rw [heq, Finset.card_sdiff]
    have h2 : (({axisTarget i} : Finset (Fin 9)) ∩ Finset.univ).card = 1 := by
      rw [Finset.inter_univ, Finset.card_singleton]
    rw [h2, Finset.card_univ, Fintype.card_fin]
  have hsum : (∑ y ∈ Finset.univ.filter (fun y => y ≠ axisTarget i),
      un (t • axisNormal i) y / un (t • axisNormal i) (axisTarget i))
      ≤ ∑ y ∈ Finset.univ.filter (fun y => y ≠ axisTarget i), Real.exp (-t * γ) := by
    refine Finset.sum_le_sum ?_
    intro y hy
    have hy' : y ≠ axisTarget i := by
      have hmem := Finset.mem_filter.mp hy
      exact hmem.2
    exact axis_ratio_le_exp i t ht y hy'
  have hconst : (∑ y ∈ Finset.univ.filter (fun y => y ≠ axisTarget i),
      Real.exp (-t * γ)) = 8 * Real.exp (-t * γ) := by
    rw [Finset.sum_const, h8]
    simp [nsmul_eq_mul]
  linarith


/-- **A.2 (axis).** `1 - P̃_{t n}(y_target) ≤ 8 exp(-t γ)` for `t ≥ 0`. -/
theorem axis_A2 (i : Fin 4) (t : ℝ) (ht : 0 ≤ t) :
    1 - pt (t • axisNormal i) (axisTarget i) ≤ 8 * Real.exp (-t * γ) := by
  have hun_pos : 0 < un (t • axisNormal i) (axisTarget i) := un_pos _ _
  have hZ_pos : 0 < Z (t • axisNormal i) := Z_pos _
  have hR : 0 ≤ Real.exp (-t * γ) := le_of_lt (Real.exp_pos _)
  have hR2 : 0 ≤ 8 * Real.exp (-t * γ) := by positivity
  -- 1 - un/Z = (Z-un)/Z = N/Z ≤ N/un ≤ 8 e^{-tγ}
  have hN : Z (t • axisNormal i) - un (t • axisNormal i) (axisTarget i)
      = ∑ y, (if y = axisTarget i then (0 : ℝ) else un (t • axisNormal i) y) := by
    have := Z_axis_split i t
    linarith
  have hone : 1 - pt (t • axisNormal i) (axisTarget i)
      = (Z (t • axisNormal i) - un (t • axisNormal i) (axisTarget i))
        / Z (t • axisNormal i) := by
    have hpt : pt (t • axisNormal i) (axisTarget i)
        = un (t • axisNormal i) (axisTarget i) / Z (t • axisNormal i) := rfl
    rw [hpt]
    have hZ : 0 < Z (t • diagNormal i) := Z_pos _
    field_simp [ne_of_gt hZ]
  have hle : (Z (t • axisNormal i) - un (t • axisNormal i) (axisTarget i))
      / Z (t • axisNormal i)
      ≤ 8 * Real.exp (-t * γ) := by
    rw [hN]
    have hnum : 0 ≤ ∑ y, (if y = axisTarget i then (0 : ℝ)
        else un (t • axisNormal i) y) := by
      refine Finset.sum_nonneg ?_
      intro y _
      by_cases hy : y = axisTarget i
      · rw [if_pos hy]
      · rw [if_neg hy]
        exact le_of_lt (un_pos _ _)
    have hden : un (t • axisNormal i) (axisTarget i) ≤ Z (t • axisNormal i) := by
      have hsplit := Z_axis_split i t
      have h2 : 0 ≤ ∑ y, (if y = axisTarget i then (0 : ℝ)
          else un (t • axisNormal i) y) := hnum
      linarith
    have hfrac : (∑ y, (if y = axisTarget i then (0 : ℝ)
        else un (t • axisNormal i) y)) / Z (t • axisNormal i)
        ≤ (∑ y, (if y = axisTarget i then (0 : ℝ)
            else un (t • axisNormal i) y)) / un (t • axisNormal i) (axisTarget i) :=
      div_le_div_of_nonneg_left hnum hun_pos hden
    exact le_trans hfrac (axis_nontarget_ratio i t ht)
  rw [hone]
  exact hle

/-- Diagonal analog of `Z_axis_split`. -/
theorem Z_diag_split (i : Fin 4) (t : ℝ) :
    Z (t • diagNormal i)
      = un (t • diagNormal i) (diagTarget i)
        + ∑ y, (if y = diagTarget i then (0 : ℝ) else un (t • diagNormal i) y) := by
  unfold Z
  have hsum := Finset.sum_eq_add_sum_diff_singleton
    (s := Finset.univ) (f := un (t • diagNormal i))
    (i := diagTarget i) (h := Finset.mem_univ (diagTarget i))
  rw [hsum]
  have h : ∑ y ∈ Finset.univ \ {diagTarget i}, un (t • diagNormal i) y
      = ∑ y, (if y = diagTarget i then (0 : ℝ) else un (t • diagNormal i) y) := by
    rw [Finset.sum_ite]
    have h1 : (∑ x with x = diagTarget i, (0:ℝ)) = 0 := by simp
    have h2 : (∑ x with ¬ x = diagTarget i, un (t • diagNormal i) x)
        = ∑ y ∈ Finset.univ \ {diagTarget i}, un (t • diagNormal i) y := by
      have : Finset.univ.filter (fun x => ¬ x = diagTarget i)
          = Finset.univ \ {diagTarget i} := by
        ext y
        simp
      rw [this]
    rw [h1, h2, zero_add]
  rw [h]

theorem diag_nontarget_ratio (i : Fin 4) (t : ℝ) (ht : 0 ≤ t) :
    (∑ y, (if y = diagTarget i then (0 : ℝ) else un (t • diagNormal i) y))
      / un (t • diagNormal i) (diagTarget i)
      ≤ 8 * Real.exp (-t * γ) := by
  have hfilter : (∑ y, (if y = diagTarget i then (0 : ℝ)
      else un (t • diagNormal i) y))
      = ∑ y ∈ Finset.univ.filter (fun y => y ≠ diagTarget i),
          un (t • diagNormal i) y := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro y _
    by_cases hy : y = diagTarget i
    · rw [if_pos hy]
      have hnn : ¬ (y ≠ diagTarget i) := fun h => h hy
      rw [if_neg hnn]
    · rw [if_neg hy, if_pos hy]
  have hdiv : (∑ y ∈ Finset.univ.filter (fun y => y ≠ diagTarget i),
      un (t • diagNormal i) y) / un (t • diagNormal i) (diagTarget i)
      = ∑ y ∈ Finset.univ.filter (fun y => y ≠ diagTarget i),
          un (t • diagNormal i) y / un (t • diagNormal i) (diagTarget i) := by
    have key := Finset.sum_mul
      (s := Finset.univ.filter (fun y => y ≠ diagTarget i))
      (f := fun y => un (t • diagNormal i) y)
      (a := (un (t • diagNormal i) (diagTarget i))⁻¹)
    rw [div_eq_mul_inv, key]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [div_eq_mul_inv]
  rw [hfilter, hdiv]
  have h8 : (Finset.univ.filter (fun y : Fin 9 => y ≠ diagTarget i)).card = 8 := by
    have heq : Finset.univ.filter (fun y : Fin 9 => y ≠ diagTarget i)
        = Finset.univ \ {diagTarget i} := by
      ext y
      simp
    rw [heq, Finset.card_sdiff]
    have h2 : (({diagTarget i} : Finset (Fin 9)) ∩ Finset.univ).card = 1 := by
      rw [Finset.inter_univ, Finset.card_singleton]
    rw [h2, Finset.card_univ, Fintype.card_fin]
  have hsum : (∑ y ∈ Finset.univ.filter (fun y => y ≠ diagTarget i),
      un (t • diagNormal i) y / un (t • diagNormal i) (diagTarget i))
      ≤ ∑ y ∈ Finset.univ.filter (fun y => y ≠ diagTarget i), Real.exp (-t * γ) := by
    refine Finset.sum_le_sum ?_
    intro y hy
    have hy' : y ≠ diagTarget i := (Finset.mem_filter.mp hy).2
    exact diag_ratio_le_exp i t ht y hy'
  have hconst : (∑ y ∈ Finset.univ.filter (fun y => y ≠ diagTarget i),
      Real.exp (-t * γ)) = 8 * Real.exp (-t * γ) := by
    rw [Finset.sum_const, h8]
    simp [nsmul_eq_mul]
  linarith

/-- **A.2 (diagonal).** `1 - P̃_{t n}(y_target) ≤ 8 exp(-t γ)` for `t ≥ 0`. -/
theorem diag_A2 (i : Fin 4) (t : ℝ) (ht : 0 ≤ t) :
    1 - pt (t • diagNormal i) (diagTarget i) ≤ 8 * Real.exp (-t * γ) := by
  have hun_pos : 0 < un (t • diagNormal i) (diagTarget i) := un_pos _ _
  have hN : Z (t • diagNormal i) - un (t • diagNormal i) (diagTarget i)
      = ∑ y, (if y = diagTarget i then (0 : ℝ) else un (t • diagNormal i) y) := by
    have := Z_diag_split i t
    linarith
  have hone : 1 - pt (t • diagNormal i) (diagTarget i)
      = (Z (t • diagNormal i) - un (t • diagNormal i) (diagTarget i))
        / Z (t • diagNormal i) := by
    have hpt : pt (t • diagNormal i) (diagTarget i)
        = un (t • diagNormal i) (diagTarget i) / Z (t • diagNormal i) := rfl
    rw [hpt]
    have hZ : 0 < Z (t • diagNormal i) := Z_pos _
    field_simp [ne_of_gt hZ]
  have hle : (Z (t • diagNormal i) - un (t • diagNormal i) (diagTarget i))
      / Z (t • diagNormal i)
      ≤ 8 * Real.exp (-t * γ) := by
    rw [hN]
    have hnum : 0 ≤ ∑ y, (if y = diagTarget i then (0 : ℝ)
        else un (t • diagNormal i) y) := by
      refine Finset.sum_nonneg ?_
      intro y _
      by_cases hy : y = diagTarget i
      · rw [if_pos hy]
      · rw [if_neg hy]
        exact le_of_lt (un_pos _ _)
    have hden : un (t • diagNormal i) (diagTarget i) ≤ Z (t • diagNormal i) := by
      have hsplit := Z_diag_split i t
      have h2 : 0 ≤ ∑ y, (if y = diagTarget i then (0 : ℝ)
          else un (t • diagNormal i) y) := hnum
      linarith
    have hfrac : (∑ y, (if y = diagTarget i then (0 : ℝ)
        else un (t • diagNormal i) y)) / Z (t • diagNormal i)
        ≤ (∑ y, (if y = diagTarget i then (0 : ℝ)
            else un (t • diagNormal i) y)) / un (t • diagNormal i) (diagTarget i) :=
      div_le_div_of_nonneg_left hnum hun_pos hden
    exact le_trans hfrac (diag_nontarget_ratio i t ht)
  rw [hone]
  exact hle


/-! ## Eight-component mixture `Q_t` (unified `Fin 8` index)

Index `0..3` are the four axis components, `4..7` the four diagonals.
-/

/-- Normal of the `k`-th component of `Q_t`. -/
noncomputable def compNormal : Fin 8 → ℝ × ℝ
  | ⟨k, h⟩ =>
    if hk : k < 4 then axisNormal ⟨k, hk⟩
    else diagNormal ⟨k - 4, by omega⟩

/-- Target of the `k`-th component. -/
noncomputable def compTarget : Fin 8 → Fin 9
  | ⟨k, h⟩ =>
    if hk : k < 4 then axisTarget ⟨k, hk⟩
    else diagTarget ⟨k - 4, by omega⟩

/-- Tilted component probability. -/
noncomputable def compPt (t : ℝ) (k : Fin 8) (y : Fin 9) : ℝ :=
  pt (t • compNormal k) y

/-- Equal-weight mixture `Q_t = (1/8) ∑_k P_{t n_k}`. -/
noncomputable def Qt (t : ℝ) (y : Fin 9) : ℝ :=
  (1 / 8 : ℝ) * ∑ k : Fin 8, compPt t k y

theorem Qt_eq (t : ℝ) (y : Fin 9) :
    Qt t y = (1 / 8 : ℝ) * ∑ k : Fin 8, compPt t k y := rfl

/-- Uniform law on the eight nonzero points. -/
noncomputable def U8 : Fin 9 → ℝ
  | ⟨0, _⟩ => 0
  | ⟨_, _⟩ => (1 / 8 : ℝ)

theorem U8_eq_zero : U8 (0 : Fin 9) = 0 := rfl

theorem U8_eq_inv (y : Fin 9) (hy : y ≠ 0) : U8 y = 1 / 8 := by
  match y with
  | ⟨0, _⟩ => exact absurd rfl hy
  | ⟨n+1, _⟩ => rfl

/-- `Q_t` at the target of component `k`. -/
theorem Qt_target (t : ℝ) (k : Fin 8) :
    Qt t (compTarget k)
      = (1 / 8 : ℝ) * pt (t • compNormal k) (compTarget k)
        + (1 / 8 : ℝ) * ∑ k' : Fin 8, (if k' = k then 0
            else compPt t k' (compTarget k)) := by
  unfold Qt
  have hsum := Finset.sum_eq_add_sum_diff_singleton
    (s := Finset.univ)
    (f := fun k' => compPt t k' (compTarget k))
    (i := k) (h := Finset.mem_univ k)
  rw [hsum]
  have h : ∑ x ∈ Finset.univ \ {k}, compPt t x (compTarget k)
      = ∑ k' : Fin 8, (if k' = k then 0 else compPt t k' (compTarget k)) := by
    rw [Finset.sum_ite]
    have h1 : (∑ x with x = k, (0:ℝ)) = 0 := by simp
    have h2 : (∑ x with ¬ x = k, compPt t x (compTarget k))
        = ∑ x ∈ Finset.univ \ {k}, compPt t x (compTarget k) := by
      have : Finset.univ.filter (fun x => ¬ x = k)
          = Finset.univ \ {k} := by
        ext y; simp
      rw [this]
    rw [h1, zero_add]
    exact h2.symm
  rw [h]
  have hdef : compPt t k (compTarget k) = pt (t • compNormal k) (compTarget k) := rfl
  rw [hdef]
  ring


/-! ## Euclidean norm on `ℝ²`

The default norm on `ℝ × ℝ` is the max-norm; the paper uses the
Euclidean norm `√(x₁²+x₂²)`. We define it explicitly.
-/

noncomputable def euclNorm (p : ℝ × ℝ) : ℝ := Real.sqrt (p.1 ^ 2 + p.2 ^ 2)

theorem euclNorm_nonneg (p : ℝ × ℝ) : 0 ≤ euclNorm p := Real.sqrt_nonneg _

theorem euclNorm_sq (p : ℝ × ℝ) : 0 ≤ p.1 ^ 2 + p.2 ^ 2 := by positivity

theorem euclNorm_apply (p : ℝ × ℝ) :
    euclNorm p = Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := rfl

/-- Origin has norm 0. -/
theorem euclNorm_origin : euclNorm (coord 0) = 0 := by
  simp [euclNorm, coord]

/-- Axis points have norm 1. -/
theorem euclNorm_axis (y : Fin 9) (h1 : y = 1) : euclNorm (coord y) = 1 := by
  subst h1
  simp [euclNorm, coord]

theorem euclNorm_axis2 (y : Fin 9) (h : y = 2) : euclNorm (coord y) = 1 := by
  subst h
  simp [euclNorm, coord]

theorem euclNorm_axis3 (y : Fin 9) (h : y = 3) : euclNorm (coord y) = 1 := by
  subst h
  simp [euclNorm, coord]

theorem euclNorm_axis4 (y : Fin 9) (h : y = 4) : euclNorm (coord y) = 1 := by
  subst h
  simp [euclNorm, coord]

/-- Helper: `√(ρ²+ρ²) = 4/5`. -/
theorem sqrt_two_rho_sq : Real.sqrt (ρ ^ 2 + ρ ^ 2) = 4 / 5 := by
  have h : ρ ^ 2 + ρ ^ 2 = (16 / 25 : ℝ) := by
    rw [ρ_sq]; norm_num
  rw [h]
  have h2 : Real.sqrt (16 / 25 : ℝ) = Real.sqrt 16 / Real.sqrt 25 := by
    rw [Real.sqrt_div (by norm_num)]
  rw [h2]
  have h3 : Real.sqrt (16 : ℝ) = 4 := by
    have : (16 : ℝ) = 4 ^ 2 := by norm_num
    rw [this]
    exact Real.sqrt_sq (by norm_num)
  have h4 : Real.sqrt (25 : ℝ) = 5 := by
    have : (25 : ℝ) = 5 ^ 2 := by norm_num
    rw [this]
    exact Real.sqrt_sq (by norm_num)
  rw [h3, h4]

/-- Diagonal points have norm `4/5`. -/
theorem euclNorm_diag5 : euclNorm (coord 5) = 4 / 5 := by
  simp [euclNorm, coord]
  exact sqrt_two_rho_sq

theorem euclNorm_diag6 : euclNorm (coord 6) = 4 / 5 := by
  simp [euclNorm, coord]
  exact sqrt_two_rho_sq

theorem euclNorm_diag7 : euclNorm (coord 7) = 4 / 5 := by
  simp [euclNorm, coord]
  exact sqrt_two_rho_sq

theorem euclNorm_diag8 : euclNorm (coord 8) = 4 / 5 := by
  simp [euclNorm, coord]
  exact sqrt_two_rho_sq

/-- Sum of squares of coordinates of each alphabet point. -/
theorem coord_sq_sum (y : Fin 9) :
    (coord y).1 ^ 2 + (coord y).2 ^ 2
      = match y.val with
        | 0 => 0
        | 1 => 1
        | 2 => 1
        | 3 => 1
        | 4 => 1
        | 5 => 16 / 25
        | 6 => 16 / 25
        | 7 => 16 / 25
        | _ => 16 / 25 := by
  match y with
  | ⟨0, _⟩ => simp [coord]
  | ⟨1, _⟩ => simp [coord]
  | ⟨2, _⟩ => simp [coord]
  | ⟨3, _⟩ => simp [coord]
  | ⟨4, _⟩ => simp [coord]
  | ⟨5, _⟩ => simp [coord, ρ_sq]; norm_num
  | ⟨6, _⟩ => simp [coord, neg_sq, ρ_sq]; norm_num
  | ⟨7, _⟩ => simp [coord, neg_sq, ρ_sq]; norm_num
  | ⟨8, _⟩ => simp [coord, neg_sq, ρ_sq]; norm_num

/-- Every alphabet point has Euclidean norm at most 1. -/
theorem euclNorm_coord_le_one (y : Fin 9) : euclNorm (coord y) ≤ 1 := by
  unfold euclNorm
  have hs : (coord y).1 ^ 2 + (coord y).2 ^ 2 ≤ 1 := by
    rw [coord_sq_sum]
    match y with
    | ⟨0, _⟩ => norm_num
    | ⟨1, _⟩ => norm_num
    | ⟨2, _⟩ => norm_num
    | ⟨3, _⟩ => norm_num
    | ⟨4, _⟩ => norm_num
    | ⟨5, _⟩ => norm_num
    | ⟨6, _⟩ => norm_num
    | ⟨7, _⟩ => norm_num
    | ⟨8, _⟩ => norm_num
  exact Real.sqrt_le_one.mpr hs


/-! ## Total variation on `Fin 9` -/

/-- Total variation of two mass functions on `Fin 9`. -/
noncomputable def tvFin (p q : Fin 9 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y, |p y - q y|

/-- Mean of a mass function (as a vector in `ℝ²`). -/
noncomputable def meanFin (p : Fin 9 → ℝ) : ℝ × ℝ :=
  ∑ y, p y • coord y

theorem meanFin_apply (p : Fin 9 → ℝ) :
    meanFin p = ∑ y, p y • coord y := rfl

/-- `∑_{y≠t} p y = ∑ y, if y = t then 0 else p y`. -/
theorem sum_diff_eq_ite (p : Fin 9 → ℝ) (t : Fin 9) :
    (∑ y ∈ Finset.univ \ {t}, p y) = ∑ y, (if y = t then (0:ℝ) else p y) := by
  have heq : Finset.univ \ ({t} : Finset (Fin 9))
      = Finset.univ.filter (fun y => y ≠ t) := by
    ext y
    simp
  rw [heq, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro y _
  by_cases hy : y = t
  · rw [if_pos hy]
    have hnn : ¬ (y ≠ t) := fun h => h hy
    rw [if_neg hnn]
  · rw [if_neg hy, if_pos hy]

/-- TV of `p` against a point mass at `t` is `1 - p t`. -/
theorem tvFin_delta (p : Fin 9 → ℝ) (t : Fin 9)
    (hnonneg : ∀ y, 0 ≤ p y) (hsum : ∑ y, p y = 1) (ht : p t ≤ 1) :
    tvFin p (fun y => if y = t then (1:ℝ) else 0) = 1 - p t := by
  unfold tvFin
  have hsplit : ∑ y, |p y - (if y = t then (1:ℝ) else 0)|
      = |p t - 1| + ∑ y, (if y = t then (0:ℝ) else p y) := by
    rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ)
      (f := fun y => |p y - (if y = t then (1:ℝ) else 0)|)
      (i := t) (h := Finset.mem_univ t)]
    have ht' : |p t - (if t = t then (1:ℝ) else 0)| = |p t - 1| := by
      simp
    rw [ht']
    have hrest : ∑ y ∈ Finset.univ \ {t}, |p y - (if y = t then (1:ℝ) else 0)|
        = ∑ y, (if y = t then (0:ℝ) else p y) := by
      have heq : ∑ y ∈ Finset.univ \ {t}, |p y - (if y = t then (1:ℝ) else 0)|
          = ∑ y ∈ Finset.univ \ {t}, p y := by
        refine Finset.sum_congr rfl ?_
        intro y hy
        have hy' : y ≠ t := by
          have hmem : y ∈ Finset.univ ∧ y ∉ ({t} : Finset (Fin 9)) :=
            Finset.mem_sdiff.mp hy
          intro heq
          subst heq
          exact hmem.2 (Finset.mem_singleton.mpr rfl)
        rw [if_neg hy', sub_zero, abs_of_nonneg (hnonneg y)]
      rw [heq, sum_diff_eq_ite]
    rw [hrest]
  have habs : |p t - 1| = 1 - p t := by
    rw [abs_of_nonpos]
    · ring
    · linarith
  rw [hsplit, habs]
  have hrest2 : ∑ y, (if y = t then (0:ℝ) else p y) = 1 - p t := by
    have h1 : ∑ y, p y = p t + ∑ y, (if y = t then (0:ℝ) else p y) := by
      rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ)
        (f := p) (i := t) (h := Finset.mem_univ t), sum_diff_eq_ite]
    linarith
  rw [hrest2]
  ring


/-! ## `compPt` is a probability -/

theorem compPt_nonneg (t : ℝ) (k : Fin 8) (y : Fin 9) : 0 ≤ compPt t k y := by
  unfold compPt
  exact le_of_lt (pt_pos _ _)

theorem compPt_sum (t : ℝ) (k : Fin 8) : ∑ y, compPt t k y = 1 := by
  unfold compPt
  exact pt_sum _

theorem compPt_le_one (t : ℝ) (k : Fin 8) (y : Fin 9) : compPt t k y ≤ 1 := by
  have hsum := compPt_sum t k
  have hle : compPt t k y ≤ ∑ z, compPt t k z := by
    rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ)
      (f := compPt t k) (i := y) (h := Finset.mem_univ y)]
    have h2 : 0 ≤ ∑ x ∈ Finset.univ \ {y}, compPt t k x :=
      Finset.sum_nonneg (fun x _ => compPt_nonneg t k x)
    linarith
  linarith

/-! ## TV of a component against its target -/

theorem compPt_tv_target (t : ℝ) (k : Fin 8) (ht : 0 ≤ t) :
    tvFin (compPt t k) (fun y => if y = compTarget k then (1:ℝ) else 0)
      = 1 - compPt t k (compTarget k) := by
  exact tvFin_delta (compPt t k) (compTarget k)
    (compPt_nonneg t k) (compPt_sum t k) (compPt_le_one t k (compTarget k))

/-- A.2 in component form: TV of component `k` to its target mass. -/
theorem compPt_tv_le (t : ℝ) (k : Fin 8) (ht : 0 ≤ t) :
    tvFin (compPt t k) (fun y => if y = compTarget k then (1:ℝ) else 0)
      ≤ 8 * Real.exp (-t * γ) := by
  rw [compPt_tv_target _ _ ht]
  unfold compPt
  fin_cases k <;>
    first
    | (simp only [compTarget, compNormal, dif_pos, dif_neg, Nat.lt_of_sub_eq_zero] <;>
       first | exact axis_A2 _ t ht | exact diag_A2 _ t ht)
    | (have ha := axis_A2 0 t ht
       simp only [compTarget, compNormal]
       simpa using ha)
    | (have ha := axis_A2 1 t ht
       simp only [compTarget, compNormal]
       simpa using ha)
    | (have ha := axis_A2 2 t ht
       simp only [compTarget, compNormal]
       simpa using ha)
    | (have ha := axis_A2 3 t ht
       simp only [compTarget, compNormal]
       simpa using ha)
    | (have hd := diag_A2 0 t ht
       simp only [compTarget, compNormal]
       simpa using hd)
    | (have hd := diag_A2 1 t ht
       simp only [compTarget, compNormal]
       simpa using hd)
    | (have hd := diag_A2 2 t ht
       simp only [compTarget, compNormal]
       simpa using hd)
    | (have hd := diag_A2 3 t ht
       simp only [compTarget, compNormal]
       simpa using hd)


/-! ## Convexity of TV and `TV(Q_t, U₈) ≤ β` -/

theorem tvFin_triangle (p q r : Fin 9 → ℝ) :
    tvFin p r ≤ tvFin p q + tvFin q r := by
  unfold tvFin
  have h : ∀ y, |p y - r y| ≤ |p y - q y| + |q y - r y| := by
    intro y
    have h2 : p y - q y + (q y - r y) = p y - r y := by ring
    rw [← h2]
    exact abs_add_le _ _
  have h2 : ∑ y, |p y - r y| ≤ ∑ y, (|p y - q y| + |q y - r y|) :=
    Finset.sum_le_sum (fun y _ => h y)
  have h3 : ∑ y, (|p y - q y| + |q y - r y|)
      = ∑ y, |p y - q y| + ∑ y, |q y - r y| :=
    Finset.sum_add_distrib
  rw [h3] at h2
  have : (1/2:ℝ) * ∑ y, |p y - r y|
      ≤ (1/2:ℝ) * (∑ y, |p y - q y| + ∑ y, |q y - r y|) :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  have h4 : (1/2:ℝ) * (∑ y, |p y - q y| + ∑ y, |q y - r y|)
      = (1/2:ℝ) * ∑ y, |p y - q y| + (1/2:ℝ) * ∑ y, |q y - r y| := by
    ring
  rw [h4] at this
  exact this

/-- `U₈` is 0 at the origin and `1/8` elsewhere. -/
theorem U8_of_zero : U8 0 = 0 := rfl

theorem U8_of_ne_zero (y : Fin 9) (hy : y ≠ 0) : U8 y = 1 / 8 :=
  U8_eq_inv y hy

/-- TV of a mixture against a mixture is at most the average TV. -/
theorem tvFin_mix_le (ps qs : Fin 8 → (Fin 9 → ℝ)) :
    tvFin (fun y => (1 / 8 : ℝ) * ∑ k, ps k y)
      (fun y => (1 / 8 : ℝ) * ∑ k, qs k y)
      ≤ (1 / 8 : ℝ) * ∑ k, tvFin (ps k) (qs k) := by
  unfold tvFin
  have hpt : ∀ y, |(1 / 8 : ℝ) * ∑ k, ps k y - (1 / 8 : ℝ) * ∑ k, qs k y|
      ≤ (1 / 8 : ℝ) * ∑ k, |ps k y - qs k y| := by
    intro y
    have h1 : (1 / 8 : ℝ) * ∑ k, ps k y - (1 / 8 : ℝ) * ∑ k, qs k y
        = (1 / 8 : ℝ) * (∑ k, ps k y - ∑ k, qs k y) := by ring
    rw [h1, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 1/8 by norm_num)]
    have h2 : |∑ k, ps k y - ∑ k, qs k y| ≤ ∑ k, |ps k y - qs k y| := by
      have h3 : ∑ k, ps k y - ∑ k, qs k y = ∑ k, (ps k y - qs k y) :=
        (Finset.sum_sub_distrib (f := fun k => ps k y) (g := fun k => qs k y)).symm
      rw [h3]
      exact Finset.abs_sum_le_sum_abs _ _
    exact mul_le_mul_of_nonneg_left h2 (show (0:ℝ) ≤ 1/8 by norm_num)
  have hsum : ∑ y, |(1 / 8 : ℝ) * ∑ k, ps k y - (1 / 8 : ℝ) * ∑ k, qs k y|
      ≤ ∑ y, ((1 / 8 : ℝ) * ∑ k, |ps k y - qs k y|) :=
    Finset.sum_le_sum (fun y _ => hpt y)
  have hR : ∑ y, ((1 / 8 : ℝ) * ∑ k, |ps k y - qs k y|)
      = (1 / 8 : ℝ) * ∑ k, ∑ y, |ps k y - qs k y| := by
    have h1 : ∑ y, ((1 / 8 : ℝ) * ∑ k, |ps k y - qs k y|)
        = (1 / 8 : ℝ) * ∑ y, ∑ k, |ps k y - qs k y| :=
      (Finset.mul_sum (s := Finset.univ)
        (f := fun y => ∑ k, |ps k y - qs k y|) (a := (1/8:ℝ))).symm
    rw [h1]
    rw [Finset.sum_comm]
  have hmul : (1/2:ℝ) * ∑ y, |(1 / 8 : ℝ) * ∑ k, ps k y - (1 / 8 : ℝ) * ∑ k, qs k y|
      ≤ (1/2:ℝ) * ((1 / 8 : ℝ) * ∑ k, ∑ y, |ps k y - qs k y|) :=
    mul_le_mul_of_nonneg_left (le_trans hsum (le_of_eq hR)) (show (0:ℝ) ≤ 1/2 by norm_num)
  have hR2 : (1/2:ℝ) * ((1 / 8 : ℝ) * ∑ k, ∑ y, |ps k y - qs k y|)
      = (1 / 8 : ℝ) * ∑ k, ((1/2:ℝ) * ∑ y, |ps k y - qs k y|) := by
    have h : (1/2:ℝ) * ((1 / 8 : ℝ) * ∑ k, ∑ y, |ps k y - qs k y|)
        = ((1/2:ℝ) * (1/8:ℝ)) * ∑ k, ∑ y, |ps k y - qs k y| := by
      ring
    rw [h]
    have h2 : ((1/2:ℝ) * (1/8:ℝ)) = ((1/8:ℝ) * (1/2:ℝ)) := by norm_num
    rw [h2]
    have h3 : ((1/8:ℝ) * (1/2:ℝ)) * ∑ k, ∑ y, |ps k y - qs k y|
        = (1/8:ℝ) * ((1/2:ℝ) * ∑ k, ∑ y, |ps k y - qs k y|) := by ring
    rw [h3]
    rw [Finset.mul_sum]
  rw [hR2] at hmul
  exact hmul


/-! ## Mean of a component -/


/-! ## Euclidean norm via `EuclideanSpace ℝ (Fin 2)` -/

/-- Embed `ℝ × ℝ` as `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def toES (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  ![p.1, p.2]

theorem norm_toES (p : ℝ × ℝ) :
    ‖toES p‖ = euclNorm p := by
  unfold euclNorm toES
  rw [EuclideanSpace.norm_eq]
  have h : (∑ i : Fin 2, ‖![p.1, p.2] i‖ ^ 2) = p.1 ^ 2 + p.2 ^ 2 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp
  rw [h]

/-- Triangle inequality for `euclNorm`. -/
theorem euclNorm_add_le (p q : ℝ × ℝ) :
    euclNorm (p.1 + q.1, p.2 + q.2) ≤ euclNorm p + euclNorm q := by
  have h1 : toES (p.1 + q.1, p.2 + q.2) = toES p + toES q := by
    ext i
    fin_cases i <;> simp [toES]
  have h := norm_add_le (toES p) (toES q)
  rw [← h1] at h
  rw [norm_toES, norm_toES, norm_toES] at h
  exact h

/-- Distance between any two alphabet points is at most 2. -/
theorem euclDist_coord_le_two (y z : Fin 9) :
    euclNorm ((coord y).1 - (coord z).1, (coord y).2 - (coord z).2) ≤ 2 := by
  have h1 : euclNorm (coord y) ≤ 1 := euclNorm_coord_le_one y
  have h2 : euclNorm (coord z) ≤ 1 := euclNorm_coord_le_one z
  have htri : euclNorm ((coord y).1 - (coord z).1, (coord y).2 - (coord z).2)
      ≤ euclNorm (coord y) + euclNorm (coord z) := by
    have h := euclNorm_add_le (coord y) (-(coord z).1, -(coord z).2)
    have hneg : euclNorm (-(coord z).1, -(coord z).2) = euclNorm (coord z) := by
      unfold euclNorm
      simp [neg_sq]
    rw [hneg] at h
    have h' : euclNorm ((coord y).1 + -(coord z).1, (coord y).2 + -(coord z).2)
        = euclNorm ((coord y).1 - (coord z).1, (coord y).2 - (coord z).2) := by
      congr 1 <;> simp [sub_eq_add_neg]
    rw [← h']
    exact h
  linarith

/-- Mean of `compPt t k` as a vector. -/
noncomputable def compMean (t : ℝ) (k : Fin 8) : ℝ × ℝ :=
  meanFin (compPt t k)

theorem compMean_eq (t : ℝ) (k : Fin 8) :
    compMean t k = ∑ y, compPt t k y • coord y := rfl



/-! ## `U₈` as the average of eight target point masses -/

/-- Point mass at `compTarget k`. -/
noncomputable def deltaFin (k : Fin 8) (y : Fin 9) : ℝ :=
  if y = compTarget k then (1:ℝ) else 0

theorem deltaFin_self (k : Fin 8) : deltaFin k (compTarget k) = 1 := by
  unfold deltaFin
  rw [if_pos rfl]

theorem deltaFin_ne (k : Fin 8) (y : Fin 9) (h : y ≠ compTarget k) :
    deltaFin k y = 0 := by
  unfold deltaFin
  rw [if_neg h]

/-- `U₈` equals the average of the eight target point masses. -/
theorem compTarget_eq (k : Fin 8) :
    compTarget k = (match k.val with
      | 0 => (1 : Fin 9) | 1 => 2 | 2 => 3 | 3 => 4
      | 4 => 5 | 5 => 6 | 6 => 7 | _ => 8) := by
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl
  | ⟨7, _⟩ => rfl

theorem deltaFin_zero_all (k : Fin 8) : deltaFin k (0 : Fin 9) = 0 := by
  unfold deltaFin
  rw [compTarget_eq]
  match k with
  | ⟨0, _⟩ => simp
  | ⟨1, _⟩ => simp
  | ⟨2, _⟩ => simp
  | ⟨3, _⟩ => simp
  | ⟨4, _⟩ => simp
  | ⟨5, _⟩ => simp
  | ⟨6, _⟩ => simp
  | ⟨7, _⟩ => simp

/-- Expand the eight-term delta sum. -/
theorem sum_deltaFin_succ (y : Fin 9) :
    (∑ k : Fin 8, deltaFin k y)
      = deltaFin 0 y + deltaFin 1 y + deltaFin 2 y + deltaFin 3 y
        + deltaFin 4 y + deltaFin 5 y + deltaFin 6 y + deltaFin 7 y := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  simp [add_assoc]

theorem fin_eq_of_val {n : ℕ} {h : n < 9} (m : Fin 9) (hm : n = m.val) :
    (⟨n, h⟩ : Fin 9) = m :=
  Fin.eq_of_val_eq hm

theorem sum_deltaFin_eq_one (y : Fin 9) (hy : y ≠ 0) :
    (∑ k : Fin 8, deltaFin k y) = 1 := by
  rw [sum_deltaFin_succ]
  simp only [deltaFin, compTarget_eq]
  match y with
  | ⟨0, _⟩ => exact absurd rfl hy
  | ⟨1, h⟩ =>
    have e0 : (⟨1, h⟩ : Fin 9) = (1 : Fin 9) := fin_eq_of_val 1 rfl
    have e1 : (⟨1, h⟩ : Fin 9) ≠ (2 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e2 : (⟨1, h⟩ : Fin 9) ≠ (3 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e3 : (⟨1, h⟩ : Fin 9) ≠ (4 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e4 : (⟨1, h⟩ : Fin 9) ≠ (5 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e5 : (⟨1, h⟩ : Fin 9) ≠ (6 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e6 : (⟨1, h⟩ : Fin 9) ≠ (7 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e7 : (⟨1, h⟩ : Fin 9) ≠ (8 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    rw [if_pos e0, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5,
      if_neg e6, if_neg e7]
    norm_num
  | ⟨2, h⟩ =>
    have e0 : (⟨2, h⟩ : Fin 9) ≠ (1 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e1 : (⟨2, h⟩ : Fin 9) = (2 : Fin 9) := fin_eq_of_val 2 rfl
    have e2 : (⟨2, h⟩ : Fin 9) ≠ (3 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e3 : (⟨2, h⟩ : Fin 9) ≠ (4 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e4 : (⟨2, h⟩ : Fin 9) ≠ (5 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e5 : (⟨2, h⟩ : Fin 9) ≠ (6 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e6 : (⟨2, h⟩ : Fin 9) ≠ (7 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e7 : (⟨2, h⟩ : Fin 9) ≠ (8 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    rw [if_neg e0, if_pos e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5,
      if_neg e6, if_neg e7]
    norm_num
  | ⟨3, h⟩ =>
    have e0 : (⟨3, h⟩ : Fin 9) ≠ (1 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e1 : (⟨3, h⟩ : Fin 9) ≠ (2 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e2 : (⟨3, h⟩ : Fin 9) = (3 : Fin 9) := fin_eq_of_val 3 rfl
    have e3 : (⟨3, h⟩ : Fin 9) ≠ (4 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e4 : (⟨3, h⟩ : Fin 9) ≠ (5 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e5 : (⟨3, h⟩ : Fin 9) ≠ (6 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e6 : (⟨3, h⟩ : Fin 9) ≠ (7 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e7 : (⟨3, h⟩ : Fin 9) ≠ (8 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    rw [if_neg e0, if_neg e1, if_pos e2, if_neg e3, if_neg e4, if_neg e5,
      if_neg e6, if_neg e7]
    norm_num
  | ⟨4, h⟩ =>
    have e0 : (⟨4, h⟩ : Fin 9) ≠ (1 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e1 : (⟨4, h⟩ : Fin 9) ≠ (2 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e2 : (⟨4, h⟩ : Fin 9) ≠ (3 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e3 : (⟨4, h⟩ : Fin 9) = (4 : Fin 9) := fin_eq_of_val 4 rfl
    have e4 : (⟨4, h⟩ : Fin 9) ≠ (5 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e5 : (⟨4, h⟩ : Fin 9) ≠ (6 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e6 : (⟨4, h⟩ : Fin 9) ≠ (7 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e7 : (⟨4, h⟩ : Fin 9) ≠ (8 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    rw [if_neg e0, if_neg e1, if_neg e2, if_pos e3, if_neg e4, if_neg e5,
      if_neg e6, if_neg e7]
    norm_num
  | ⟨5, h⟩ =>
    have e0 : (⟨5, h⟩ : Fin 9) ≠ (1 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e1 : (⟨5, h⟩ : Fin 9) ≠ (2 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e2 : (⟨5, h⟩ : Fin 9) ≠ (3 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e3 : (⟨5, h⟩ : Fin 9) ≠ (4 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e4 : (⟨5, h⟩ : Fin 9) = (5 : Fin 9) := fin_eq_of_val 5 rfl
    have e5 : (⟨5, h⟩ : Fin 9) ≠ (6 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e6 : (⟨5, h⟩ : Fin 9) ≠ (7 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e7 : (⟨5, h⟩ : Fin 9) ≠ (8 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    rw [if_neg e0, if_neg e1, if_neg e2, if_neg e3, if_pos e4, if_neg e5,
      if_neg e6, if_neg e7]
    norm_num
  | ⟨6, h⟩ =>
    have e0 : (⟨6, h⟩ : Fin 9) ≠ (1 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e1 : (⟨6, h⟩ : Fin 9) ≠ (2 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e2 : (⟨6, h⟩ : Fin 9) ≠ (3 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e3 : (⟨6, h⟩ : Fin 9) ≠ (4 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e4 : (⟨6, h⟩ : Fin 9) ≠ (5 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e5 : (⟨6, h⟩ : Fin 9) = (6 : Fin 9) := fin_eq_of_val 6 rfl
    have e6 : (⟨6, h⟩ : Fin 9) ≠ (7 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e7 : (⟨6, h⟩ : Fin 9) ≠ (8 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    rw [if_neg e0, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_pos e5,
      if_neg e6, if_neg e7]
    norm_num
  | ⟨7, h⟩ =>
    have e0 : (⟨7, h⟩ : Fin 9) ≠ (1 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e1 : (⟨7, h⟩ : Fin 9) ≠ (2 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e2 : (⟨7, h⟩ : Fin 9) ≠ (3 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e3 : (⟨7, h⟩ : Fin 9) ≠ (4 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e4 : (⟨7, h⟩ : Fin 9) ≠ (5 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e5 : (⟨7, h⟩ : Fin 9) ≠ (6 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e6 : (⟨7, h⟩ : Fin 9) = (7 : Fin 9) := fin_eq_of_val 7 rfl
    have e7 : (⟨7, h⟩ : Fin 9) ≠ (8 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    rw [if_neg e0, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5,
      if_pos e6, if_neg e7]
    norm_num
  | ⟨8, h⟩ =>
    have e0 : (⟨8, h⟩ : Fin 9) ≠ (1 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e1 : (⟨8, h⟩ : Fin 9) ≠ (2 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e2 : (⟨8, h⟩ : Fin 9) ≠ (3 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e3 : (⟨8, h⟩ : Fin 9) ≠ (4 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e4 : (⟨8, h⟩ : Fin 9) ≠ (5 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e5 : (⟨8, h⟩ : Fin 9) ≠ (6 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e6 : (⟨8, h⟩ : Fin 9) ≠ (7 : Fin 9) := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    have e7 : (⟨8, h⟩ : Fin 9) = (8 : Fin 9) := fin_eq_of_val 8 rfl
    rw [if_neg e0, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5,
      if_neg e6, if_pos e7]
    norm_num

theorem U8_eq_avg_delta (y : Fin 9) :
    U8 y = (1 / 8 : ℝ) * ∑ k : Fin 8, deltaFin k y := by
  by_cases hy : y = 0
  · subst hy
    rw [U8_eq_zero,
      show (∑ k : Fin 8, deltaFin k (0 : Fin 9)) = 0 by
        rw [Finset.sum_congr rfl (fun k _ => deltaFin_zero_all k)]
        simp]
    ring
  · rw [U8_eq_inv y hy, sum_deltaFin_eq_one y hy]
    ring


/-! ## `TV(Q_t, U₈) ≤ β` -/

/-- The eight target deltas as a family of mass functions. -/
noncomputable def deltaFam (k : Fin 8) : Fin 9 → ℝ := deltaFin k

theorem tvFin_deltaFam (t : ℝ) (k : Fin 8) (ht : 0 ≤ t) :
    tvFin (compPt t k) (deltaFam k)
      = 1 - compPt t k (compTarget k) := by
  unfold deltaFam
  exact compPt_tv_target t k ht

/-- **`TV(Q_t, U₈) ≤ 8 exp(-t γ)`.** -/
theorem Qt_U8_tv_le (t : ℝ) (ht : 0 ≤ t) :
    tvFin (Qt t) U8 ≤ 8 * Real.exp (-t * γ) := by
  have h1 : tvFin (Qt t) U8
      = tvFin (fun y => (1 / 8 : ℝ) * ∑ k, compPt t k y)
          (fun y => (1 / 8 : ℝ) * ∑ k, deltaFam k y) := by
    unfold tvFin
    have : U8 = (fun y => (1 / 8 : ℝ) * ∑ k, deltaFam k y) := by
      ext y
      rw [U8_eq_avg_delta]
      rfl
    rw [this]
    rfl
  rw [h1]
  have h2 := tvFin_mix_le (compPt t) deltaFam
  have h3 : (1 / 8 : ℝ) * ∑ k, tvFin (compPt t k) (deltaFam k)
      ≤ 8 * Real.exp (-t * γ) := by
    have h4 : ∀ k : Fin 8, tvFin (compPt t k) (deltaFam k)
        ≤ 8 * Real.exp (-t * γ) := by
      intro k
      unfold deltaFam
      exact compPt_tv_le t k ht
    have h5 : (∑ k, tvFin (compPt t k) (deltaFam k))
        ≤ ∑ k, 8 * Real.exp (-t * γ) :=
      Finset.sum_le_sum (fun k _ => h4 k)
    have h6 : (∑ k : Fin 8, 8 * Real.exp (-t * γ)) = 8 * 8 * Real.exp (-t * γ) := by
      have : (∑ k : Fin 8, 8 * Real.exp (-t * γ))
          = Fintype.card (Fin 8) • (8 * Real.exp (-t * γ)) := by
        rw [Finset.sum_const, Finset.card_univ]
      rw [this, Fintype.card_fin]
      simp [nsmul_eq_mul]
      ring
    rw [h6] at h5
    have h7 : (1/8:ℝ) * ∑ k, tvFin (compPt t k) (deltaFam k)
        ≤ (1/8:ℝ) * (8 * 8 * Real.exp (-t * γ)) :=
      mul_le_mul_of_nonneg_left h5 (by norm_num)
    have h8 : (1/8:ℝ) * (8 * 8 * Real.exp (-t * γ))
        = 8 * Real.exp (-t * γ) := by ring
    rw [h8] at h7
    exact h7
  exact le_trans h2 h3


/-! ## Mean in `EuclideanSpace ℝ (Fin 2)` -/

/-- Mean of a mass function as a point of `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def esMean (p : Fin 9 → ℝ) : EuclideanSpace ℝ (Fin 2) :=
  ∑ y, p y • toES (coord y)

/-- Target point as an element of `EuclideanSpace`. -/
noncomputable def esTarget (y : Fin 9) : EuclideanSpace ℝ (Fin 2) :=
  toES (coord y)

theorem esTarget_eq (y : Fin 9) : esTarget y = toES (coord y) := rfl

theorem norm_esTarget_eq (y : Fin 9) : ‖esTarget y‖ = euclNorm (coord y) :=
  norm_toES (coord y)

theorem norm_toES_coord_le_one (y : Fin 9) : ‖toES (coord y)‖ ≤ 1 := by
  rw [norm_toES]
  exact euclNorm_coord_le_one y

/-- Key identity: `mean − target = ∑_{y} p_y • (x_y − x_T)` when `∑ p = 1`. -/
theorem esMean_sub (p : Fin 9 → ℝ) (T : Fin 9) (hsum : ∑ y, p y = 1) :
    esMean p - esTarget T
      = ∑ y, p y • (toES (coord y) - toES (coord T)) := by
  unfold esMean esTarget
  have h : ∑ y, p y • toES (coord T) = toES (coord T) := by
    have hsmul : ∑ y, p y • toES (coord T) = (∑ y, p y) • toES (coord T) :=
      (Finset.sum_smul (s := Finset.univ) (f := p) (x := toES (coord T))).symm
    rw [hsmul, hsum, one_smul]
  have hsplit : ∑ y, p y • toES (coord y)
      = ∑ y, p y • (toES (coord y) - toES (coord T)) + toES (coord T) := by
    have : ∀ y, p y • toES (coord y)
        = p y • (toES (coord y) - toES (coord T)) + p y • toES (coord T) := by
      intro y
      rw [← smul_add, sub_add_cancel]
    calc ∑ y, p y • toES (coord y)
        = ∑ y, (p y • (toES (coord y) - toES (coord T)) + p y • toES (coord T)) :=
          Finset.sum_congr rfl (fun y _ => this y)
      _ = ∑ y, p y • (toES (coord y) - toES (coord T))
          + ∑ y, p y • toES (coord T) :=
          Finset.sum_add_distrib
      _ = ∑ y, p y • (toES (coord y) - toES (coord T)) + toES (coord T) := by
          rw [h]
  rw [hsplit]
  abel

/-- Norm of `toES (coord y) - toES (coord T)` is at most 2. -/
theorem norm_toES_coord_sub_le_two (y T : Fin 9) :
    ‖toES (coord y) - toES (coord T)‖ ≤ 2 := by
  have h := norm_sub_le (toES (coord y)) (toES (coord T))
  have h1 : ‖toES (coord y)‖ ≤ 1 := norm_toES_coord_le_one y
  have h2 : ‖toES (coord T)‖ ≤ 1 := norm_toES_coord_le_one T
  linarith

/-- Mean of a probability lies within `2(1-p(T))` of its target. -/
theorem esMean_dev (p : Fin 9 → ℝ) (T : Fin 9)
    (hnonneg : ∀ y, 0 ≤ p y) (hsum : ∑ y, p y = 1) :
    ‖esMean p - esTarget T‖ ≤ 2 * (1 - p T) := by
  rw [esMean_sub p T hsum]
  have hle : ‖∑ y, p y • (toES (coord y) - toES (coord T))‖
      ≤ ∑ y, ‖p y • (toES (coord y) - toES (coord T))‖ :=
    norm_sum_le _ _
  have hsmul : ∀ y, ‖p y • (toES (coord y) - toES (coord T))‖
      = p y * ‖toES (coord y) - toES (coord T)‖ := by
    intro y
    rw [norm_smul, Real.norm_of_nonneg (hnonneg y)]
  rw [Finset.sum_congr rfl (fun y _ => hsmul y)] at hle
  have hT : toES (coord T) - toES (coord T) = 0 := sub_self _
  have hsplit : (∑ y, p y * ‖toES (coord y) - toES (coord T)‖)
      = ∑ y, (if y = T then (0:ℝ) else p y * ‖toES (coord y) - toES (coord T)‖) := by
    refine Finset.sum_congr rfl ?_
    intro y _
    by_cases hy : y = T
    · subst hy
      simp [sub_self]
    · simp [hy]
  rw [hsplit] at hle
  have hbound : (∑ y, if y = T then (0:ℝ) else p y * ‖toES (coord y) - toES (coord T)‖)
      ≤ 2 * (1 - p T) := by
    have h10 : (∑ y, if y = T then (0:ℝ) else p y * ‖toES (coord y) - toES (coord T)‖)
        ≤ ∑ y, if y = T then (0:ℝ) else p y * 2 := by
      refine Finset.sum_le_sum ?_
      intro y _
      by_cases hy : y = T
      · rw [if_pos hy, if_pos hy]
      · rw [if_neg hy, if_neg hy]
        exact mul_le_mul_of_nonneg_left (norm_toES_coord_sub_le_two y T) (hnonneg y)
    have h11 : (∑ y, if y = T then (0:ℝ) else p y * 2) = 2 * (1 - p T) := by
      have hpt : ∀ y, (if y = T then (0:ℝ) else p y * 2)
          = 2 * (if y = T then (0:ℝ) else p y) := by
        intro y
        by_cases hy : y = T
        · rw [if_pos hy, if_pos hy]
          norm_num
        · rw [if_neg hy, if_neg hy]
          ring
      rw [Finset.sum_congr rfl (fun y _ => hpt y)]
      rw [← Finset.mul_sum]
      
      have hrest2 : (∑ y, if y = T then (0:ℝ) else p y) = 1 - p T := by
        have hsplit2 : ∑ y, p y = p T + ∑ y, (if y = T then (0:ℝ) else p y) := by
          rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ)
            (f := p) (i := T) (h := Finset.mem_univ T), sum_diff_eq_ite p T]
        linarith
      rw [hrest2]
    rw [h11] at h10
    have : (2:ℝ) * 1 = 2 := by ring
    -- h10 : ... ≤ 2 * (1 - p T) already after rw? h11 rewrites the sum to 2*(1-p T)
    exact h10
  exact le_trans hle hbound

/-- Component mean deviation at most `2 * 8 e^{-tγ}` under A.2. -/
theorem compMean_es_dev (t : ℝ) (k : Fin 8) (ht : 0 ≤ t) :
    ‖esMean (compPt t k) - esTarget (compTarget k)‖
      ≤ 2 * (8 * Real.exp (-t * γ)) := by
  have h := esMean_dev (compPt t k) (compTarget k)
    (compPt_nonneg t k) (compPt_sum t k)
  have hA2 : 1 - compPt t k (compTarget k) ≤ 8 * Real.exp (-t * γ) := by
    have := compPt_tv_le t k ht
    rw [compPt_tv_target t k ht] at this
    exact this
  have h2 : 2 * (1 - compPt t k (compTarget k)) ≤ 2 * (8 * Real.exp (-t * γ)) :=
    mul_le_mul_of_nonneg_left hA2 (by norm_num)
  exact le_trans h h2


/-! ## Exterior feasibility at `t = 200` -/

/-- `β_t = 8 exp(-t γ)`. -/
noncomputable def beta (t : ℝ) : ℝ := 8 * Real.exp (-t * γ)

theorem beta_eq (t : ℝ) : beta t = 8 * Real.exp (-t * γ) := rfl

/-- `8 exp(-200 γ) < 10^{-10}` using `γ > 13/100`. -/
theorem beta_200_lt : beta 200 < 10 ^ (-10 : ℤ) := by
  unfold beta
  have hγ : (13 / 100 : ℝ) < γ := γ_gt
  have h200 : (200:ℝ) * γ > 26 := by
    have : (200:ℝ) * (13 / 100) = 26 := by norm_num
    nlinarith
  have hexp : Real.exp (-(200:ℝ) * γ) < Real.exp (-26) := by
    rw [Real.exp_lt_exp]
    linarith
  have h8 : (8:ℝ) * Real.exp (-(200:ℝ) * γ) < 8 * Real.exp (-26) :=
    mul_lt_mul_of_pos_left hexp (by norm_num)
  have he2 : Real.exp 2 > (7:ℝ) := by
    have h1 := exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 : ((2.7182818283:ℝ) : ℝ) ^ 2 > 7 := by norm_num
    rw [h2]
    nlinarith
  have he26 : Real.exp 26 > (7:ℝ) ^ 13 := by
    have h26 : Real.exp 26 = Real.exp 2 ^ 13 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h26]
    exact pow_lt_pow_left₀ he2 (by norm_num) (by norm_num : (13:ℕ) ≠ 0)
  have h6 : (8:ℝ) * Real.exp (-26) < 10 ^ (-10 : ℤ) := by
    have hdiv : (8:ℝ) * Real.exp (-26) = 8 * (Real.exp 26)⁻¹ := by
      rw [Real.exp_neg]
    have h7' : (7:ℝ)^13 < Real.exp 26 := he26
    have hpos7 : 0 < (7:ℝ)^13 := by positivity
    have hpos26 : 0 < Real.exp 26 := Real.exp_pos _
    have h8 : (8:ℝ) * (Real.exp 26)⁻¹ < 8 * ((7:ℝ)^13)⁻¹ := by
      have hinv : (Real.exp 26)⁻¹ < ((7:ℝ)^13)⁻¹ := by
        have h := (one_div_lt_one_div hpos26 hpos7).mpr h7'
        simpa [div_eq_mul_inv] using h
      exact mul_lt_mul_of_pos_left hinv (by norm_num)
    have h9 : (8:ℝ) * ((7:ℝ)^13)⁻¹ < 10 ^ (-10:ℤ) := by
      have h7eq : ((7:ℝ)^13) = 96889010407 := Numerical.seven_pow_thirteen_eq
      rw [h7eq]
      norm_num [zpow_neg, zpow_ofNat]
    calc (8:ℝ) * Real.exp (-26)
        = 8 * (Real.exp 26)⁻¹ := hdiv
      _ < 8 * ((7:ℝ)^13)⁻¹ := h8
      _ < 10 ^ (-10:ℤ) := h9
  linarith

/-- Diagonal targets have Euclidean norm `4/5`. -/
theorem esTarget_diag5 : ‖esTarget (diagTarget 0)‖ = 4 / 5 := by
  unfold esTarget diagTarget
  rw [norm_toES]
  exact euclNorm_diag5

theorem esTarget_diag6 : ‖esTarget (diagTarget 1)‖ = 4 / 5 := by
  unfold esTarget diagTarget
  rw [norm_toES]
  exact euclNorm_diag6

theorem esTarget_diag7 : ‖esTarget (diagTarget 2)‖ = 4 / 5 := by
  unfold esTarget diagTarget
  rw [norm_toES]
  exact euclNorm_diag7

theorem esTarget_diag8 : ‖esTarget (diagTarget 3)‖ = 4 / 5 := by
  unfold esTarget diagTarget
  rw [norm_toES]
  exact euclNorm_diag8


/-! ## Exterior feasibility -/

/-- Each component target is one of the eight nonzero points with norm ≥ 4/5. -/
theorem compTarget_exists (k : Fin 8) :
    ∃ n : Fin 9, compTarget k = n ∧ (4 / 5 : ℝ) ≤ euclNorm (coord n) := by
  rw [compTarget_eq]
  match k with
  | ⟨0, _⟩ =>
    refine ⟨1, rfl, ?_⟩
    have := euclNorm_axis 1 rfl
    linarith
  | ⟨1, _⟩ =>
    refine ⟨2, rfl, ?_⟩
    have := euclNorm_axis2 2 rfl
    linarith
  | ⟨2, _⟩ =>
    refine ⟨3, rfl, ?_⟩
    have := euclNorm_axis3 3 rfl
    linarith
  | ⟨3, _⟩ =>
    refine ⟨4, rfl, ?_⟩
    have := euclNorm_axis4 4 rfl
    linarith
  | ⟨4, _⟩ =>
    refine ⟨5, rfl, ?_⟩
    exact le_of_eq euclNorm_diag5.symm
  | ⟨5, _⟩ =>
    refine ⟨6, rfl, ?_⟩
    exact le_of_eq euclNorm_diag6.symm
  | ⟨6, _⟩ =>
    refine ⟨7, rfl, ?_⟩
    exact le_of_eq euclNorm_diag7.symm
  | ⟨7, _⟩ =>
    refine ⟨8, rfl, ?_⟩
    exact le_of_eq euclNorm_diag8.symm

theorem target_norm_ge (k : Fin 8) :
    (4 / 5 : ℝ) ≤ euclNorm (coord (compTarget k)) := by
  obtain ⟨n, hn, h⟩ := compTarget_exists k
  rw [hn]
  exact h

/-- `‖mean‖ ≥ ‖target‖ − ‖mean − target‖`. -/
theorem esMean_norm_ge (p : Fin 9 → ℝ) (T : Fin 9) :
    euclNorm (coord T) - ‖esMean p - esTarget T‖ ≤ ‖esMean p‖ := by
  have h2 : esTarget T = esMean p - (esMean p - esTarget T) := by abel
  have h : ‖esMean p - (esMean p - esTarget T)‖
      ≤ ‖esMean p‖ + ‖esMean p - esTarget T‖ := by
    exact norm_sub_le (esMean p) (esMean p - esTarget T)
  rw [← h2] at h
  have h4 : ‖esTarget T‖ = euclNorm (coord T) := norm_toES (coord T)
  rw [h4] at h
  linarith

/-- At `t = 200`, every component mean has Euclidean norm `> r₀`. -/
theorem exterior_200 (k : Fin 8) : r₀ < ‖esMean (compPt 200 k)‖ := by
  have hdev := compMean_es_dev 200 k (by norm_num)
  have hdev' : ‖esMean (compPt 200 k) - esTarget (compTarget k)‖
      ≤ 2 * (8 * Real.exp (-200 * γ)) := hdev
  have hβ2 : beta 200 < 10 ^ (-10 : ℤ) := beta_200_lt
  have hβeq : (2 * (8 * Real.exp (-200 * γ)) : ℝ) = 2 * beta 200 := by
    unfold beta; ring
  have hβ3 : (2 * (8 * Real.exp (-200 * γ)) : ℝ) < 2 * 10 ^ (-10 : ℤ) := by
    rw [hβeq]
    exact mul_lt_mul_of_pos_left hβ2 (by norm_num)
  have hdev2 : ‖esMean (compPt 200 k) - esTarget (compTarget k)‖
      < 2 * 10 ^ (-10 : ℤ) := lt_of_le_of_lt hdev' hβ3
  rw [zpow_neg, zpow_ofNat] at hdev2
  have hge := esMean_norm_ge (compPt 200 k) (compTarget k)
  have hT : (4 / 5 : ℝ) ≤ euclNorm (coord (compTarget k)) := target_norm_ge k
  have hbound : (4 / 5 : ℝ) - 2 * (10 ^ 10)⁻¹
      ≤ euclNorm (coord (compTarget k))
        - ‖esMean (compPt 200 k) - esTarget (compTarget k)‖ := by
    have h1 : (0 : ℝ) < 2 * (10 ^ 10)⁻¹ := by
      have : (0:ℝ) < (10^10 : ℝ) := by positivity
      positivity
    have hdev_le : ‖esMean (compPt 200 k) - esTarget (compTarget k)‖
        ≤ 2 * (10 ^ 10)⁻¹ := le_of_lt hdev2
    linarith
  have h45 : (0.79 : ℝ) < 4 / 5 - 2 * (10 ^ 10)⁻¹ := by
    have h10 : (10 ^ 10 : ℝ)⁻¹ = (1:ℝ) / 10 ^ 10 := (one_div (10^10:ℝ)).symm
    rw [h10]
    norm_num
  have hbase : (0.79 : ℝ)
      < euclNorm (coord (compTarget k))
        - ‖esMean (compPt 200 k) - esTarget (compTarget k)‖ :=
    lt_of_lt_of_le h45 hbound
  have h5 : (0.79 : ℝ) < ‖esMean (compPt 200 k)‖ :=
    lt_of_lt_of_le hbase hge
  have h6 : r₀ < (0.79 : ℝ) := by
    rw [r₀_eq]
    norm_num
  linarith


/-! ## `Z ≥ 1` and origin mass ≤ ε -/

/-- Base mean is zero by nine-point symmetry. -/
theorem p0_mean_zero :
    (∑ y, p0 y * (coord y).1, ∑ y, p0 y * (coord y).2) = (0, 0) := by
  have hx : (∑ y, p0 y * (coord y).1) = 0 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp [p0, coord, w, ρ]
  have hy : (∑ y, p0 y * (coord y).2) = 0 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp [p0, coord, w, ρ]
  exact Prod.ext hx hy

/-- `exp a ≥ 1 + a` gives `Z(θ) ≥ 1` when the base mean is 0. -/
theorem Z_ge_one (θ : ℝ × ℝ) : 1 ≤ Z θ := by
  unfold Z un
  have hpoint : ∀ y, 1 + dot θ (coord y) ≤ Real.exp (dot θ (coord y)) := by
    intro y
    have := Real.add_one_le_exp (dot θ (coord y))
    linarith
  have h : ∀ y, p0 y * (1 + dot θ (coord y))
      ≤ Real.exp (dot θ (coord y)) * p0 y := by
    intro y
    have h1 : p0 y * (1 + dot θ (coord y))
        ≤ p0 y * Real.exp (dot θ (coord y)) :=
      mul_le_mul_of_nonneg_left (hpoint y) (p0_nonneg y)
    have h2 : p0 y * Real.exp (dot θ (coord y))
        = Real.exp (dot θ (coord y)) * p0 y := by ring
    rw [← h2]
    exact h1
  have h2 : ∑ y, p0 y * (1 + dot θ (coord y))
      ≤ ∑ y, Real.exp (dot θ (coord y)) * p0 y :=
    Finset.sum_le_sum (fun y _ => h y)
  have h3 : ∑ y, p0 y * (1 + dot θ (coord y)) = 1 := by
    have : ∀ y, p0 y * (1 + dot θ (coord y))
        = p0 y + p0 y * dot θ (coord y) := by
      intro y; ring
    rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_add_distrib]
    have h4 : ∑ y, p0 y * dot θ (coord y) = 0 := by
      have hform : ∀ y, p0 y * dot θ (coord y)
          = p0 y * (θ.1 * (coord y).1 + θ.2 * (coord y).2) := by
        intro y; rfl
      rw [Finset.sum_congr rfl (fun y _ => hform y)]
      have hsplit : ∑ y, p0 y * (θ.1 * (coord y).1 + θ.2 * (coord y).2)
          = θ.1 * ∑ y, p0 y * (coord y).1 + θ.2 * ∑ y, p0 y * (coord y).2 := by
        have : ∀ y, p0 y * (θ.1 * (coord y).1 + θ.2 * (coord y).2)
            = θ.1 * (p0 y * (coord y).1) + θ.2 * (p0 y * (coord y).2) := by
          intro y; ring
        rw [Finset.sum_congr rfl (fun y _ => this y),
          Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hsplit]
      have hx : ∑ y, p0 y * (coord y).1 = 0 := congrArg Prod.fst p0_mean_zero
      have hy : ∑ y, p0 y * (coord y).2 = 0 := congrArg Prod.snd p0_mean_zero
      rw [hx, hy]
      ring
    rw [h4, p0_sum, add_zero]
  linarith

/-- Tilted origin mass is at most `ε`. -/
theorem pt_origin_le (θ : ℝ × ℝ) : pt θ 0 ≤ ε := by
  have h : pt θ 0 = p0 0 / Z θ := by
    unfold pt un
    have h3 : dot θ (coord 0) = 0 := by
      unfold dot
      have : coord 0 = (0, 0) := rfl
      rw [this]
      ring
    rw [h3, Real.exp_zero, one_mul]
  rw [h]
  have hZ : 1 ≤ Z θ := Z_ge_one θ
  have hp : p0 0 = ε := rfl
  rw [hp]
  have hdiv : ε / Z θ ≤ ε / 1 := by
    exact div_le_div_of_nonneg_left (le_of_lt ε_pos) (by norm_num) hZ
  rw [div_one] at hdiv
  exact hdiv


/-! ## `Q_t` and `U₈` are probability mass functions -/

theorem Qt_nonneg (t : ℝ) (y : Fin 9) : 0 ≤ Qt t y := by
  unfold Qt
  refine mul_nonneg (by norm_num) ?_
  exact Finset.sum_nonneg (fun k _ => compPt_nonneg t k y)

theorem Qt_sum (t : ℝ) : ∑ y, Qt t y = 1 := by
  unfold Qt
  have h1 : ∑ y, (1 / 8 : ℝ) * ∑ k, compPt t k y
      = (1 / 8 : ℝ) * ∑ y, ∑ k, compPt t k y :=
    (Finset.mul_sum (s := Finset.univ)
      (f := fun y => ∑ k, compPt t k y) (a := (1/8:ℝ))).symm
  rw [h1, Finset.sum_comm]
  have h2 : ∑ k : Fin 8, ∑ y : Fin 9, compPt t k y = 8 := by
    have : ∀ k, ∑ y, compPt t k y = 1 := fun k => compPt_sum t k
    rw [Finset.sum_congr rfl (fun k _ => this k)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul]
  rw [h2]
  norm_num

theorem U8_sum : ∑ y, U8 y = 1 := by
  have h : ∑ y, U8 y
      = U8 0 + U8 1 + U8 2 + U8 3 + U8 4 + U8 5 + U8 6 + U8 7 + U8 8 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
    have h1 : (Fin.succ 0 : Fin 9) = 1 := rfl
    have h2 : (Fin.succ (0:Fin 7)).succ = 2 := rfl
    have h3 : (Fin.succ (0:Fin 6)).succ.succ = 3 := rfl
    have h4 : (Fin.succ (0:Fin 5)).succ.succ.succ = 4 := rfl
    have h5 : (Fin.succ (0:Fin 4)).succ.succ.succ.succ = 5 := rfl
    have h6 : (Fin.succ (0:Fin 3)).succ.succ.succ.succ.succ = 6 := rfl
    have h7 : (Fin.succ (0:Fin 2)).succ.succ.succ.succ.succ.succ = 7 := rfl
    have h8 : (Fin.succ (0:Fin 1)).succ.succ.succ.succ.succ.succ.succ = 8 := rfl
    rw [h8, h7, h6, h5, h4, h3, h2, h1]
    ring
  rw [h]
  have e0 : U8 0 = 0 := U8_eq_zero
  have e1 : U8 1 = 1 / 8 := U8_eq_inv 1 (by decide)
  have e2 : U8 2 = 1 / 8 := U8_eq_inv 2 (by decide)
  have e3 : U8 3 = 1 / 8 := U8_eq_inv 3 (by decide)
  have e4 : U8 4 = 1 / 8 := U8_eq_inv 4 (by decide)
  have e5 : U8 5 = 1 / 8 := U8_eq_inv 5 (by decide)
  have e6 : U8 6 = 1 / 8 := U8_eq_inv 6 (by decide)
  have e7 : U8 7 = 1 / 8 := U8_eq_inv 7 (by decide)
  have e8 : U8 8 = 1 / 8 := U8_eq_inv 8 (by decide)
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8]
  norm_num

theorem U8_nonneg (y : Fin 9) : 0 ≤ U8 y := by
  by_cases hy : y = 0
  · rw [hy, U8_eq_zero]
  · rw [U8_eq_inv y hy]
    norm_num

/-- `Q_t(0) ≤ ε` by averaging the component origin bounds. -/
theorem Qt_origin_le (t : ℝ) (ht : 0 ≤ t) : Qt t 0 ≤ ε := by
  unfold Qt
  have h : ∀ k : Fin 8, compPt t k 0 ≤ ε := by
    intro k
    unfold compPt
    exact pt_origin_le _
  have h2 : (∑ k : Fin 8, compPt t k 0) ≤ ∑ k : Fin 8, ε :=
    Finset.sum_le_sum (fun k _ => h k)
  have h3 : (∑ k : Fin 8, ε : ℝ) = 8 * ε := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul]
  rw [h3] at h2
  have h4 : (1 / 8 : ℝ) * ∑ k, compPt t k 0 ≤ (1 / 8 : ℝ) * (8 * ε) :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  have h5 : (1 / 8 : ℝ) * (8 * ε) = ε := by ring
  rw [h5] at h4
  exact h4

/-- `|Q_t(0) − ε| ≤ ε` since `0 ≤ Q_t(0) ≤ ε`. -/
theorem Qt_origin_abs_le (t : ℝ) (ht : 0 ≤ t) :
    |Qt t 0 - ε| ≤ ε := by
  have h1 : 0 ≤ Qt t 0 := Qt_nonneg t 0
  have h2 : Qt t 0 ≤ ε := Qt_origin_le t ht
  have : Qt t 0 - ε ≤ 0 := by linarith
  rw [abs_of_nonpos this]
  have : -(Qt t 0 - ε) = ε - Qt t 0 := by ring
  rw [this]
  linarith


/-! ## Single-point deviation from TV -/

/-- `∑_z d z = 0` implies `|d y| ≤ ∑_{z≠y} |d z|`. -/
theorem abs_le_sum_rest {d : Fin 9 → ℝ} (y : Fin 9) (hsum : ∑ z, d z = 0) :
    |d y| ≤ ∑ z, (if z = y then 0 else |d z|) := by
  have hsplit : ∑ z, d z = d y + ∑ z, (if z = y then 0 else d z) := by
    rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ)
      (f := d) (i := y) (h := Finset.mem_univ y), sum_diff_eq_ite d y]
  have hrest : ∑ z, (if z = y then 0 else d z) = - d y := by
    linarith
  have habs : |∑ z, (if z = y then 0 else d z)| ≤ ∑ z, |(if z = y then 0 else d z)| :=
    Finset.abs_sum_le_sum_abs _ _
  have hpt : ∀ z, |(if z = y then 0 else d z)| = (if z = y then 0 else |d z|) := by
    intro z
    by_cases hy : z = y
    · rw [if_pos hy, if_pos hy, abs_zero]
    · rw [if_neg hy, if_neg hy]
  rw [Finset.sum_congr rfl (fun z _ => hpt z)] at habs
  rw [hrest] at habs
  have : |- d y| = |d y| := abs_neg _
  rw [this] at habs
  exact habs

/-- For two probabilities on `Fin 9`, `|p y − q y| ≤ TV(p,q)`. -/
theorem abs_sub_le_tv (p q : Fin 9 → ℝ) (y : Fin 9)
    (hps : ∑ z, p z = 1) (hqs : ∑ z, q z = 1) :
    |p y - q y| ≤ tvFin p q := by
  unfold tvFin
  have hd : ∑ z, (p z - q z) = 0 := by
    rw [Finset.sum_sub_distrib, hps, hqs]
    ring
  have hrest : |p y - q y| ≤ ∑ z, (if z = y then 0 else |p z - q z|) :=
    abs_le_sum_rest y hd
  have hsplit : ∑ z, |p z - q z|
      = |p y - q y| + ∑ z, (if z = y then 0 else |p z - q z|) := by
    rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ)
      (f := fun z => |p z - q z|) (i := y) (h := Finset.mem_univ y),
      sum_diff_eq_ite (fun z => |p z - q z|) y]
  have hle : 2 * |p y - q y| ≤ ∑ z, |p z - q z| := by
    linarith
  have : |p y - q y| ≤ (1 / 2 : ℝ) * ∑ z, |p z - q z| := by
    have : (2:ℝ) * |p y - q y| ≤ ∑ z, |p z - q z| := hle
    linarith
  exact this

/-- Nonzero-point deviation `|Q_t(y) − 1/8| ≤ TV(Q_t,U₈) + Q_t(0)/8`-type bound.
Simplified: `|Q_t(y) − U₈(y)| ≤ TV(Q_t,U₈)`. -/
theorem Qt_U8_pointwise (t : ℝ) (y : Fin 9) :
    |Qt t y - U8 y| ≤ tvFin (Qt t) U8 :=
  abs_sub_le_tv (Qt t) U8 y (Qt_sum t) U8_sum


/-! ## Mass deviations of `Q_t` -/

/-- `|Q_t(y) − 1/8| ≤ TV(Q_t,U₈) + Q_t(0)` for nonzero `y`
(since U₈(y)=1/8 and we pay for the origin). Simplified tight form used
in the paper: `|Q_{200}(y) − w| ≤ β + ε/8`. -/
theorem Qt_point_dev (t : ℝ) (y : Fin 9) (hy : y ≠ 0) (ht : 0 ≤ t) :
    |Qt t y - (1 / 8 : ℝ)| ≤ tvFin (Qt t) U8 + Qt t 0 := by
  have h1 : |Qt t y - U8 y| ≤ tvFin (Qt t) U8 := Qt_U8_pointwise t y
  have h2 : U8 y = 1 / 8 := U8_eq_inv y hy
  rw [h2] at h1
  have h3 : |Qt t y - (1/8:ℝ)| ≤ tvFin (Qt t) U8 + Qt t 0 := by
    have h4 : tvFin (Qt t) U8 + Qt t 0 ≥ tvFin (Qt t) U8 := by
      have : 0 ≤ Qt t 0 := Qt_nonneg t 0
      linarith
    linarith
  exact h3

/-- Origin deviation `|Q_t(0) − ε| ≤ ε`. -/
theorem Qt_origin_dev (t : ℝ) (ht : 0 ≤ t) :
    |Qt t 0 - ε| ≤ ε :=
  Qt_origin_abs_le t ht

/-- `1/8 − w = ε/8`. -/
theorem inv8_sub_w : (1 / 8 : ℝ) - w = ε / 8 := by
  have : w = (1 - ε) / 8 := w_eq
  rw [this]
  ring

/-- `|Q_t(y) − w| ≤ TV(Q_t,U₈) + ε/8` for nonzero `y`. -/
theorem Qt_w_dev (t : ℝ) (y : Fin 9) (hy : y ≠ 0) :
    |Qt t y - w| ≤ tvFin (Qt t) U8 + ε / 8 := by
  have h1 : |Qt t y - U8 y| ≤ tvFin (Qt t) U8 := Qt_U8_pointwise t y
  have h2 : U8 y = 1 / 8 := U8_eq_inv y hy
  rw [h2] at h1
  have h3 : Qt t y - w = (Qt t y - (1/8:ℝ)) + ((1/8:ℝ) - w) := by ring
  rw [h3]
  have h4 : |(Qt t y - (1/8:ℝ)) + ((1/8:ℝ) - w)|
      ≤ |Qt t y - (1/8:ℝ)| + |(1/8:ℝ) - w| := abs_add_le _ _
  have h5 : |(1/8:ℝ) - w| = ε / 8 := by
    rw [inv8_sub_w]
    exact abs_of_nonneg (div_nonneg (le_of_lt ε_pos) (by norm_num))
  rw [h5] at h4
  linarith

/-- **A.4 chi-square pieces.** Origin contributes at most `ε`;
each nonzero point at most `(β+ε/8)²/w`. -/
theorem chiSq_upper_pieces (t : ℝ) (ht : 0 ≤ t)
    (hβ : tvFin (Qt t) U8 ≤ beta t) :
    (Qt t 0 - ε) ^ 2 / p0 0
      + ∑ y : Fin 9, (if y = 0 then (0:ℝ) else (Qt t y - w) ^ 2 / p0 y)
      ≤ ε + 8 * ((beta t + ε / 8) ^ 2 / w) := by
  have h0 : (Qt t 0 - ε) ^ 2 / p0 0 ≤ ε := by
    have hp : p0 0 = ε := rfl
    rw [hp]
    have habs : |Qt t 0 - ε| ≤ ε := Qt_origin_abs_le t ht
    have habs2 : |Qt t 0 - ε| ≤ |ε| :=
      habs.trans (le_of_eq (abs_of_pos ε_pos).symm)
    have hsq : (Qt t 0 - ε) ^ 2 ≤ ε ^ 2 := sq_le_sq.mpr habs2
    have hdiv : (Qt t 0 - ε) ^ 2 / ε ≤ ε ^ 2 / ε := by
      apply div_le_div_of_nonneg_right
      · exact hsq
      · exact le_of_lt ε_pos
    have hε : ε ^ 2 / ε = ε := by
      rw [sq, mul_div_cancel_left₀ _ (ne_of_gt ε_pos)]
    rw [hε] at hdiv
    exact hdiv
  have hnz : (∑ y : Fin 9, (if y = 0 then (0:ℝ) else (Qt t y - w) ^ 2 / p0 y))
      ≤ ∑ y : Fin 9, (if y = 0 then (0:ℝ) else (beta t + ε / 8) ^ 2 / w) := by
    have hpt : ∀ y : Fin 9, (if y = 0 then (0:ℝ) else (Qt t y - w) ^ 2 / p0 y)
        ≤ if y = 0 then (0:ℝ) else (beta t + ε / 8) ^ 2 / w := by
      intro y
      by_cases hy : y = 0
      · rw [if_pos hy, if_pos hy]
      · rw [if_neg hy, if_neg hy]
        have hdev : |Qt t y - w| ≤ tvFin (Qt t) U8 + ε / 8 :=
          Qt_w_dev t y hy
        have hdev2 : |Qt t y - w| ≤ beta t + ε / 8 := by
          have : tvFin (Qt t) U8 + ε / 8 ≤ beta t + ε / 8 := by
            have := hβ
            linarith
          linarith
        have hge : 0 ≤ beta t + ε / 8 := by
          have hε8 : (0:ℝ) ≤ ε / 8 :=
            div_nonneg (le_of_lt ε_pos) (by norm_num)
          have hβ3 : (0:ℝ) ≤ beta t := by
            unfold beta
            exact mul_nonneg (by norm_num) (le_of_lt (Real.exp_pos _))
          linarith
        have hsq : (Qt t y - w) ^ 2 ≤ (beta t + ε / 8) ^ 2 := by
          have habs2 : |Qt t y - w| ≤ |beta t + ε / 8| :=
            hdev2.trans (le_of_eq (abs_of_nonneg hge).symm)
          exact sq_le_sq.mpr habs2
        have hp : p0 y = w := by
          match y with
          | ⟨0, _⟩ => exact absurd rfl hy
          | ⟨n+1, _⟩ => rfl
        rw [hp]
        apply div_le_div_of_nonneg_right
        · exact hsq
        · exact le_of_lt w_pos
    have hle : (∑ y : Fin 9, (if y = 0 then (0:ℝ) else (Qt t y - w) ^ 2 / p0 y))
        ≤ ∑ y : Fin 9, (if y = 0 then (0:ℝ) else (beta t + ε / 8) ^ 2 / w) :=
      Finset.sum_le_sum (fun (y : Fin 9) _ => hpt y)
    exact hle
  have h8 : (∑ y : Fin 9, (if y = 0 then (0:ℝ) else (beta t + ε / 8) ^ 2 / w))
      = 8 * ((beta t + ε / 8) ^ 2 / w) := by
    have hfilter : (∑ y : Fin 9, (if y = 0 then (0:ℝ) else (beta t + ε / 8) ^ 2 / w))
        = ∑ y ∈ Finset.univ.filter (fun y : Fin 9 => y ≠ 0),
            ((beta t + ε / 8) ^ 2 / w) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro y _
      by_cases hy : y = 0
      · rw [if_pos hy]
        have hnn : ¬ (y ≠ 0) := fun h => h hy
        rw [if_neg hnn]
      · rw [if_neg hy, if_pos hy]
    rw [hfilter]
    have hcard : (Finset.univ.filter (fun y : Fin 9 => y ≠ 0)).card = 8 := by
      have heq : Finset.univ.filter (fun y : Fin 9 => y ≠ 0)
          = Finset.univ \ {(0:Fin 9)} := by
        ext y
        simp
      rw [heq, Finset.card_sdiff]
      have h2 : (({(0:Fin 9)} : Finset (Fin 9)) ∩ Finset.univ).card = 1 := by
        rw [Finset.inter_univ, Finset.card_singleton]
      rw [h2, Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_const, hcard]
    simp [nsmul_eq_mul]
  have : (∑ y : Fin 9, (if y = 0 then (0:ℝ) else (Qt t y - w) ^ 2 / p0 y))
      ≤ 8 * ((beta t + ε / 8) ^ 2 / w) := by
    linarith
  linarith


/-! ## A.4 closing bound -/

/-- At `t = 200`, `β + ε/8 < 11/10^{11}` as in the paper. -/
theorem beta200_eps_eight : beta 200 + ε / 8 < 11 / 10 ^ 11 := by
  have h1 : beta 200 < (1:ℝ) / 10 ^ 10 := by
    have h := beta_200_lt
    have hz : (10:ℝ) ^ (-10:ℤ) = (10 ^ 10 : ℝ)⁻¹ := by
      rw [zpow_neg, zpow_ofNat]
    rw [hz] at h
    have hconv : (10 ^ 10 : ℝ)⁻¹ = (1:ℝ) / 10 ^ 10 := (one_div _).symm
    rwa [hconv] at h
  have h2 : ε / 8 < (1:ℝ) / 10 ^ 14 := by
    have hε : ε = (1:ℝ) / 10 ^ 15 := ε_eq
    rw [hε]
    norm_num
  have h3 : (1:ℝ) / 10 ^ 10 + 1 / 10 ^ 14 < 11 / 10 ^ 11 := by
    norm_num
  have h4 : beta 200 + ε / 8 < (1:ℝ) / 10 ^ 10 + 1 / 10 ^ 14 := by
    linarith
  linarith

/-- Full A.4 numeric bound at `t = 200`. -/
theorem A4_numeric :
    ε + 8 * ((beta 200 + ε / 8) ^ 2 / w) < 1.001 * 10 ^ (-15 : ℤ) := by
  have h1 : beta 200 + ε / 8 < 11 / 10 ^ 11 := beta200_eps_eight
  have hge : 0 ≤ beta 200 + ε / 8 := by
    have hε8 : (0:ℝ) ≤ ε / 8 :=
      div_nonneg (le_of_lt ε_pos) (by norm_num)
    have hβ3 : (0:ℝ) ≤ beta 200 := by
      unfold beta
      exact mul_nonneg (by norm_num) (le_of_lt (Real.exp_pos _))
    linarith
  have hw : (1:ℝ) / 10 < w := by
    have hε : ε = (1:ℝ) / 10 ^ 15 := ε_eq
    rw [w_eq, hε]
    norm_num
  have hpos : (0:ℝ) < w := w_pos
  have hx2 : (beta 200 + ε / 8) ^ 2 < (11 / 10 ^ 11) ^ 2 :=
    pow_lt_pow_left₀ h1 hge (by norm_num : (2:ℕ) ≠ 0)
  have h4 : ((11:ℝ) / 10 ^ 11) ^ 2 = 121 / 10 ^ 22 := by norm_num
  have hx2' : (beta 200 + ε / 8) ^ 2 < (121:ℝ) / 10 ^ 22 := by
    rw [← h4]; exact hx2
  have hdiv1 : (beta 200 + ε / 8) ^ 2 / w < (121:ℝ) / 10 ^ 22 / w := by
    have hpos' : (0:ℝ) < w⁻¹ := inv_pos.mpr hpos
    have hmul := mul_lt_mul_of_pos_right hx2' hpos'
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact hmul
  have hdiv2 : (121:ℝ) / 10 ^ 22 / w < 121 / 10 ^ 22 / (1 / 10) := by
    have hc : (0:ℝ) < 121 / 10 ^ 22 := by norm_num
    have h10 : (0:ℝ) < (1 / 10 : ℝ) := by norm_num
    have hinv : w⁻¹ < ((1 / 10 : ℝ))⁻¹ := by
      have h := (one_div_lt_one_div hpos h10).mpr hw
      rwa [one_div, one_div] at h
    have hmul := mul_lt_mul_of_pos_left hinv hc
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact hmul
  have h8 : (121:ℝ) / 10 ^ 22 / (1 / 10) = 1210 / 10 ^ 22 := by norm_num
  have h9 : (1210:ℝ) / 10 ^ 22 = 121 / 10 ^ 21 := by norm_num
  have h10 : 8 * ((beta 200 + ε / 8) ^ 2 / w) < 8 * ((121:ℝ) / 10 ^ 21) := by
    have h3 : 8 * ((beta 200 + ε / 8) ^ 2 / w) < 8 * ((121:ℝ) / 10 ^ 22 / w) :=
      mul_lt_mul_of_pos_left hdiv1 (by norm_num : (0:ℝ) < 8)
    have h4' : 8 * ((121:ℝ) / 10 ^ 22 / w) < 8 * ((121:ℝ) / 10 ^ 22 / (1 / 10)) :=
      mul_lt_mul_of_pos_left hdiv2 (by norm_num : (0:ℝ) < 8)
    have h5' : (8:ℝ) * ((121:ℝ) / 10 ^ 22 / (1 / 10)) = 8 * (121 / 10 ^ 21) := by
      rw [h8, h9]
    linarith
  have h11 : (8:ℝ) * (121 / 10 ^ 21) = 968 / 10 ^ 21 := by norm_num
  have hε : ε = (1:ℝ) / 10 ^ 15 := ε_eq
  have h12 : ε + 8 * ((beta 200 + ε / 8) ^ 2 / w)
      < (1:ℝ) / 10 ^ 15 + 968 / 10 ^ 21 := by
    rw [hε] at h10 ⊢
    have h11' : (8:ℝ) * (121 / 10 ^ 21) = 968 / 10 ^ 21 := by norm_num
    rw [h11'] at h10
    linarith
  have h13 : (1:ℝ) / 10 ^ 15 + 968 / 10 ^ 21 < 1.001 / 10 ^ 15 := by
    norm_num
  have h14 : (1.001:ℝ) * 10 ^ (-15:ℤ) = 1.001 / 10 ^ 15 := by
    rw [zpow_neg, zpow_ofNat]
    norm_num
  rw [h14]
  linarith

end BoundaryReduction.NinePoint
