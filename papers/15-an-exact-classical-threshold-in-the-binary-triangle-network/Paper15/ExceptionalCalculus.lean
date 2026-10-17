import Paper15.Regularity
import Paper15.Stationary
import Paper15.Attainment
import Mathlib.Analysis.Calculus.LagrangeMultipliers

/-!
# Exceptional-table moment identities and coordinate stationarity

These identities connect the Section 4 polynomial calculations to the actual
finite independent-source model. The stationarity statement is expressed by
vanishing derivatives of the Lagrangian, before deriving equations (22)–(23).
-/

noncomputable section
namespace Paper15

@[simp] lemma deriv_mul_left (c r : ℝ) : deriv (HMul.hMul c) r = c := by
  simpa using ((hasDerivAt_id r).const_mul c).deriv

@[simp] lemma deriv_add_left (c r : ℝ) : deriv (HAdd.hAdd c) r = 1 := by
  simpa using ((hasDerivAt_id r).const_add c).deriv

/-- Equation (18) for the actual table (6) and arbitrary unequal source laws. -/
theorem detMoments_exceptional_lawOf (x y : Fin 3 → ℝ) :
    detMoments DetTriangle.exceptional (lawOf x y 0) (lawOf x y 1) (lawOf x y 2) =
      momentsOf x y := by
  change AggregateMoments.mk _ _ _ = AggregateMoments.mk _ _ _
  congr 1 <;>
    simp [detMoments, momentsOf, m1Of, m2Of, m3Of, eQty, tQty, sQty, vQty,
      uOf, lawOf, zOf, Fin.sum_univ_three, DetTriangle.exceptional,
      DetTriangle.exceptionalTable] <;> ring

lemma deriv_m1_x (x y : Fin 3 → ℝ) (i : Fin 3) :
    deriv (fun r => (momentsOf (Function.update x i r) y).M1) (x i) =
      (2:ℝ)/3 * eQtyPx x y i := by
  fin_cases i <;>
    simp (disch := fun_prop) [momentsOf, m1Of, m3Of, eQty, vQty, tQty, sQty, uOf,
      eQtyPx, vQtyPx, Function.update, Fin.ext_iff,
      deriv_fun_add, deriv_fun_sub, deriv_fun_mul, deriv_const_mul_field,
      deriv_mul_const_field, deriv_const_add, deriv_add_const] <;> ring <;> simp

lemma deriv_m1_y (x y : Fin 3 → ℝ) (i : Fin 3) :
    deriv (fun r => (momentsOf x (Function.update y i r)).M1) (y i) =
      (2:ℝ)/3 * eQtyPy x y i := by
  fin_cases i <;>
    simp (disch := fun_prop) [momentsOf, m1Of, m3Of, eQty, vQty, tQty, sQty, uOf,
      eQtyPy, vQtyPy, Function.update, Fin.ext_iff,
      deriv_fun_add, deriv_fun_sub, deriv_fun_mul, deriv_const_mul_field,
      deriv_mul_const_field, deriv_const_add, deriv_add_const] <;> ring <;> simp

lemma deriv_m3_x (x y : Fin 3 → ℝ) (i : Fin 3) :
    deriv (fun r => (momentsOf (Function.update x i r) y).M3) (x i) =
      2 * eQtyPx x y i - 4 * vQtyPx x y i := by
  fin_cases i <;>
    simp (disch := fun_prop) [momentsOf, m1Of, m3Of, eQty, vQty, tQty, sQty, uOf,
      eQtyPx, vQtyPx, Function.update, Fin.ext_iff,
      deriv_fun_add, deriv_fun_sub, deriv_fun_mul, deriv_const_mul_field,
      deriv_mul_const_field, deriv_const_add, deriv_add_const] <;> ring <;> simp

lemma deriv_m3_y (x y : Fin 3 → ℝ) (i : Fin 3) :
    deriv (fun r => (momentsOf x (Function.update y i r)).M3) (y i) =
      2 * eQtyPy x y i - 4 * vQtyPy x y i := by
  fin_cases i <;>
    simp (disch := fun_prop) [momentsOf, m1Of, m3Of, eQty, vQty, tQty, sQty, uOf,
      eQtyPy, vQtyPy, Function.update, Fin.ext_iff,
      deriv_fun_add, deriv_fun_sub, deriv_fun_mul, deriv_const_mul_field,
      deriv_mul_const_field, deriv_const_add, deriv_add_const] <;> ring <;> simp

/-- Lemma 6 with actual partial derivatives of the moment functions. -/
theorem lemma6_derivative_independent {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    ¬ ∃ α β : ℝ, (α ≠ 0 ∨ β ≠ 0) ∧
      (∀ i, α * deriv (fun r => (momentsOf (Function.update x i r) y).M1) (x i) +
        β * deriv (fun r => (momentsOf (Function.update x i r) y).M3) (x i) = 0) ∧
      (∀ i, α * deriv (fun r => (momentsOf x (Function.update y i r)).M1) (y i) +
        β * deriv (fun r => (momentsOf x (Function.update y i r)).M3) (y i) = 0) := by
  simpa only [deriv_m1_x, deriv_m1_y, deriv_m3_x, deriv_m3_y] using
    lemma6_grad_independent hx hy

/-- The actual Lagrangian from (20), as a polynomial in the six coordinates. -/
def exceptionalLagrangian (lam mu : ℝ) (x y : Fin 3 → ℝ) : ℝ :=
  (momentsOf x y).M2 - lam * (momentsOf x y).M1 - mu * (momentsOf x y).M3

lemma exceptionalLagrangian_eq (lam mu : ℝ) (x y : Fin 3 → ℝ) :
    exceptionalLagrangian lam mu x y =
      1 + lam + mu + lagC lam mu * eQty x y + lagB mu * tQty x y + lagA mu * sQty x y := by
  simp only [exceptionalLagrangian, momentsOf, m1Of, m2Of, m3Of, vQty, lagA, lagB, lagC]
  ring

lemma deriv_lagrangian_x (lam mu : ℝ) (x y : Fin 3 → ℝ) (i : Fin 3) :
    deriv (fun r => exceptionalLagrangian lam mu (Function.update x i r) y) (x i) =
      lagC lam mu * (y (i+1) + y (i+2)) + lagB mu * (y (i+1) * y (i+2)) +
        lagA mu * (x (i+1) * y (i+2) + y (i+1) * x (i+2)) := by
  fin_cases i <;>
    simp (disch := fun_prop) [exceptionalLagrangian_eq, eQty, tQty, sQty, uOf, Function.update, Fin.ext_iff,
      deriv_fun_add, deriv_fun_sub, deriv_fun_mul, deriv_const_mul_field,
      deriv_mul_const_field, deriv_const_add, deriv_add_const] <;> ring <;> simp

lemma deriv_lagrangian_y (lam mu : ℝ) (x y : Fin 3 → ℝ) (i : Fin 3) :
    deriv (fun r => exceptionalLagrangian lam mu x (Function.update y i r)) (y i) =
      lagC lam mu * (x (i+1) + y (i+1) + x (i+2) + y (i+2)) +
        lagB mu * (y (i+1) * y (i+2) + x (i+1) * y (i+2) + y (i+1) * x (i+2)) +
        lagA mu * (x (i+1) * x (i+2)) := by
  fin_cases i <;>
    simp (disch := fun_prop) [exceptionalLagrangian_eq, eQty, tQty, sQty, uOf, Function.update, Fin.ext_iff,
      deriv_fun_add, deriv_fun_sub, deriv_fun_mul, deriv_const_mul_field,
      deriv_mul_const_field, deriv_const_add, deriv_add_const] <;> ring <;> simp

/-- Constrained stationarity: the objective gradient belongs to the span of
the two constraint gradients, expressed using the six coordinate derivatives. -/
def IsExceptionalStationary (x y : Fin 3 → ℝ) : Prop :=
  ∃ lam mu : ℝ,
    (∀ i, deriv (fun r => exceptionalLagrangian lam mu (Function.update x i r) y) (x i) = 0) ∧
    (∀ i, deriv (fun r => exceptionalLagrangian lam mu x (Function.update y i r)) (y i) = 0)

/-- Lemma 7 for actual coordinate derivatives of the objective and constraints. -/
theorem lemma7_stationary {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hz : ∀ i, x i + y i < 1)
    (hstat : IsExceptionalStationary x y) :
    x 0 = x 1 ∧ x 1 = x 2 ∧ y 0 = y 1 ∧ y 1 = y 2 := by
  obtain ⟨lam, mu, hdx, hdy⟩ := hstat
  have h22 (j k : Fin 3) (hjk : j ≠ k) :
      lagC lam mu * (y j + y k) + lagB mu * (y j * y k) +
        lagA mu * (x j * y k + y j * x k) = 0 := by
    have h0 := hdx 0
    have h1 := hdx 1
    have h2 := hdx 2
    rw [deriv_lagrangian_x] at h0 h1 h2
    fin_cases j <;> fin_cases k <;> simp_all <;> nlinarith
  have h23 (j k : Fin 3) (hjk : j ≠ k) :
      lagC lam mu * (x j + y j + x k + y k) +
        lagB mu * (y j * y k + x j * y k + y j * x k) +
        lagA mu * (x j * x k) = 0 := by
    have h0 := hdy 0
    have h1 := hdy 1
    have h2 := hdy 2
    rw [deriv_lagrangian_y] at h0 h1 h2
    fin_cases j <;> fin_cases k <;> simp_all <;> nlinarith
  exact lemma7 hx hy hz (lagB_eq_lagA_add mu) h22 h23

end Paper15
