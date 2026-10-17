import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.Abel
import Mathlib.Data.ZMod.Basic

/-!
# Unit cancellation with left coefficients

Appendix A, equations (6)--(8).  The distinguished row and column are indexed by
`none`; `some` indexes all surviving coordinates.  All products are in the order
appropriate for free **left** modules: a source coefficient multiplies a matrix
entry on the left.  The coefficient ring need not be commutative.
-/

namespace Paper23.UnitCancellation

open scoped BigOperators

variable {R I J : Type*} [Ring R]

section FiniteSource

variable [Fintype J]

/-- Matrix application in the original coordinates, with the pivot column split out. -/
def boundary (M : Option I → Option J → R) (x : Option J → R) (i : Option I) : R :=
  x none * M i none + ∑ j, x (some j) * M i (some j)

/-- This is the usual finite matrix sum, with left coefficients. -/
theorem boundary_eq_sum (M : Option I → Option J → R) (x : Option J → R)
    (i : Option I) : boundary M x i = ∑ j, x j * M i j := by
  simp only [boundary, Fintype.sum_option]

/-- The Schur complement in equation (6), without any reordering of factors. -/
def reducedMatrix (M : Option I → Option J → R) (a : Rˣ) (i : I) (j : J) : R :=
  M (some i) (some j) - M none (some j) * (↑(a⁻¹) : R) * M (some i) none

/-- Application of the surviving matrix to a surviving source chain. -/
def reducedBoundary (M : Option I → Option J → R) (a : Rˣ) (x : J → R) (i : I) : R :=
  ∑ j, x j * reducedMatrix M a i j

/-- Zero extension of a reduced target chain. -/
def embedTarget (y : I → R) : Option I → R
  | none => 0
  | some i => y i

/-- Equation (7): restore the eliminated source coordinate. -/
def liftSource (M : Option I → Option J → R) (a : Rˣ) (x : J → R) : Option J → R
  | none => -(∑ j, x j * M none (some j)) * (↑(a⁻¹) : R)
  | some j => x j

/-- The restored source has zero boundary coefficient in the pivot row. -/
theorem liftSource_pivot (M : Option I → Option J → R) (a : Rˣ)
    (hpivot : M none none = ↑a) (x : J → R) :
    boundary M (liftSource M a x) none = 0 := by
  simp only [boundary, liftSource, hpivot, mul_assoc, Units.inv_mul, mul_one,
    neg_mul, neg_add_cancel]

/-- All other coefficients of the lifted boundary equal the Schur complement. -/
theorem liftSource_surviving (M : Option I → Option J → R) (a : Rˣ)
    (x : J → R) (i : I) :
    boundary M (liftSource M a x) (some i) = reducedBoundary M a x i := by
  simp only [boundary, liftSource, reducedBoundary, reducedMatrix, mul_sub,
    Finset.sum_sub_distrib, neg_mul]
  rw [Finset.sum_mul, Finset.sum_mul]
  simp only [mul_assoc]
  abel

/-- Equation (7) recovers an original source whose full boundary is exactly the
zero extension of the reduced boundary.  In particular no target coordinate
change is needed. -/
theorem boundary_liftSource (M : Option I → Option J → R) (a : Rˣ)
    (hpivot : M none none = ↑a) (x : J → R) :
    boundary M (liftSource M a x) = embedTarget (reducedBoundary M a x) := by
  funext i
  cases i with
  | none => exact liftSource_pivot M a hpivot x
  | some i => exact liftSource_surviving M a x i

/-- A bounding equation in the reduced matrix lifts to the original matrix. -/
theorem lift_bounding_chain (M : Option I → Option J → R) (a : Rˣ)
    (hpivot : M none none = ↑a) (x : J → R) (y : I → R)
    (h : reducedBoundary M a x = y) :
    boundary M (liftSource M a x) = embedTarget y := by
  rw [boundary_liftSource M a hpivot x, h]

end FiniteSource

@[simp] theorem embedTarget_add (y z : I → R) :
    embedTarget (y + z) = embedTarget y + embedTarget z := by
  funext i
  cases i <;> simp [embedTarget]

@[simp] theorem embedTarget_nsmul (n : ℕ) (y : I → R) :
    embedTarget (n • y) = n • embedTarget y := by
  funext i
  cases i <;> simp [embedTarget]

@[simp] theorem embedTarget_zsmul (n : ℤ) (y : I → R) :
    embedTarget (n • y) = n • embedTarget y := by
  funext i
  cases i <;> simp [embedTarget]

/-- In particular the sixfold bounding equation is preserved by a cancellation. -/
theorem lift_multiple_bounding_chain [Fintype J]
    (M : Option I → Option J → R) (a : Rˣ) (hpivot : M none none = ↑a)
    (x : J → R) (z : I → R) (n : ℕ)
    (h : reducedBoundary M a x = n • z) :
    boundary M (liftSource M a x) = n • embedTarget z := by
  rw [boundary_liftSource M a hpivot x, h, embedTarget_nsmul]

/-- Taking the boundary of the changed surviving source basis vector gives
exactly the Schur-complement column, extended by zero in the eliminated row.
This is equation (6) before assembling arbitrary source chains. -/
theorem changed_column (M : Option I → Option J → R) (a : Rˣ)
    (hpivot : M none none = ↑a) (j : J) :
    (fun i => M i (some j) - M none (some j) * (↑(a⁻¹) : R) * M i none) =
      embedTarget (fun i => reducedMatrix M a i j) := by
  funext i
  cases i with
  | none => simp [embedTarget, hpivot, mul_assoc]
  | some i => rfl

/-- Eliminate a target's pivot coordinate by subtracting its multiple of the
pivot column.  This is only an additive map; its codomain may later be mapped
additively to `ZMod 6`. -/
def targetProjection (M : Option I → Option J → R) (a : Rˣ) :
    (Option I → R) →+ (I → R) where
  toFun y i := y (some i) - y none * (↑(a⁻¹) : R) * M (some i) none
  map_zero' := by
    funext i
    simp
  map_add' y z := by
    funext i
    simp only [Pi.add_apply, add_mul]
    abel

@[simp] theorem targetProjection_embed (M : Option I → Option J → R) (a : Rˣ)
    (y : I → R) : targetProjection M a (embedTarget y) = y := by
  funext i
  simp [targetProjection, embedTarget]

/-- On a full boundary, pivot-column terms cancel and the projection gives the
reduced boundary of the surviving source coefficients. -/
theorem targetProjection_boundary [Fintype J] (M : Option I → Option J → R) (a : Rˣ)
    (hpivot : M none none = ↑a) (x : Option J → R) :
    targetProjection M a (boundary M x) = reducedBoundary M a (fun j => x (some j)) := by
  funext i
  simp only [targetProjection, AddMonoidHom.coe_mk, ZeroHom.coe_mk, boundary,
    reducedBoundary, reducedMatrix, hpivot, mul_sub, Finset.sum_sub_distrib,
    add_mul]
  rw [Finset.sum_mul, Finset.sum_mul]
  simp only [mul_assoc, Units.mul_inv, mul_one]
  abel

variable {A : Type*} [AddCommGroup A]

/-- Lift an arbitrary additive cochain.  No `R`-linearity is assumed. -/
def liftCochain (M : Option I → Option J → R) (a : Rˣ) (φ : (I → R) →+ A) :
    (Option I → R) →+ A := φ.comp (targetProjection M a)

/-- Lifting a cochain leaves its value on the zero-extended target unchanged. -/
@[simp] theorem liftCochain_embed (M : Option I → Option J → R) (a : Rˣ)
    (φ : (I → R) →+ A) (y : I → R) :
    liftCochain M a φ (embedTarget y) = φ y := by
  simp [liftCochain]

/-- The lifted cochain annihilates every original boundary whenever the reduced
cochain annihilates every reduced boundary. -/
theorem liftCochain_annihilates [Fintype J] (M : Option I → Option J → R) (a : Rˣ)
    (hpivot : M none none = ↑a) (φ : (I → R) →+ A)
    (hφ : ∀ x : J → R, φ (reducedBoundary M a x) = 0) (x : Option J → R) :
    liftCochain M a φ (boundary M x) = 0 := by
  change φ (targetProjection M a (boundary M x)) = 0
  rw [targetProjection_boundary M a hpivot x]
  exact hφ _

/-- Equation (8), valid for every coefficient `u` in the ring, hence in
particular for every permutation in the integral group-ring basis. -/
theorem liftCochain_pivot_formula (M : Option I → Option J → R) (a : Rˣ)
    (φ : (I → R) →+ A) (u : R) :
    liftCochain M a φ (fun k => match k with | none => u | some _ => 0) =
      -φ (fun i => u * (↑(a⁻¹) : R) * M (some i) none) := by
  change φ (fun i => 0 - u * (↑(a⁻¹) : R) * M (some i) none) = _
  simpa only [zero_sub, Pi.neg_apply] using
    φ.map_neg (fun i => u * (↑(a⁻¹) : R) * M (some i) none)

/-- The explicit finite-sum form of equation (8), with each surviving row
written as a single-coordinate target vector. -/
theorem liftCochain_pivot_sum [Fintype I] [DecidableEq I]
    (M : Option I → Option J → R) (a : Rˣ)
    (φ : (I → R) →+ A) (u : R) :
    liftCochain M a φ (fun k => match k with | none => u | some _ => 0) =
      -∑ i, φ (Pi.single i (u * (↑(a⁻¹) : R) * M (some i) none)) := by
  rw [liftCochain_pivot_formula]
  rw [← map_sum, Finset.univ_sum_single]

/-- The extension already annihilates all left multiples of the pivot column,
even before any assumption on the reduced columns. -/
theorem liftCochain_pivot_column (M : Option I → Option J → R) (a : Rˣ)
    (hpivot : M none none = ↑a) (φ : (I → R) →+ A) (u : R) :
    liftCochain M a φ (fun i => u * M i none) = 0 := by
  change φ (targetProjection M a (fun i => u * M i none)) = 0
  have hzero : targetProjection M a (fun i => u * M i none) = 0 := by
    funext i
    simp [targetProjection, hpivot, mul_assoc]
  rw [hzero, map_zero]

end Paper23.UnitCancellation


/-!
## Residual rank-one certificate

The two Bézout identities checked in Appendix A are precisely the hypotheses
of the final theorem below.  Their finite integer witnesses are mathematical
inputs here: this theorem does not assume that a script's return value proves
those identities.
-/

namespace Paper23.ResidualCertificate

open scoped BigOperators

variable {I J : Type*}

/-- Integral matrix application, using the same left-coefficient convention. -/
def boundary [Fintype J] (M : I → J → ℤ) (x : J → ℤ) (i : I) : ℤ :=
  ∑ j, x j * M i j

/-- The image of a rank-one matrix is computed without division. -/
theorem rankOne_boundary [Fintype J] (z : I → ℤ) (d x : J → ℤ) :
    boundary (fun i j => d j * z i) x = fun i => (∑ j, x j * d j) * z i := by
  funext i
  simp only [boundary, ← mul_assoc, Finset.sum_mul]

/-- The integral functional produced by the primitive-vector Bézout witness. -/
def integralFunctional [Fintype I] (w : I → ℤ) : (I → ℤ) →+ ℤ where
  toFun y := ∑ i, w i * y i
  map_zero' := by simp
  map_add' y y' := by simp [mul_add, Finset.sum_add_distrib]

@[simp] theorem integralFunctional_apply [Fintype I] (w y : I → ℤ) :
    integralFunctional w y = ∑ i, w i * y i := rfl

/-- Integer scalar multiplication passes through the integral functional. -/
theorem integralFunctional_mul [Fintype I] (w y : I → ℤ) (n : ℤ) :
    integralFunctional w (fun i => n * y i) = n * integralFunctional w y := by
  change (∑ i, w i * (n * y i)) = n * ∑ i, w i * y i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_left_comm (w i) n (y i)

/-- Reduction modulo six of the Bézout integral functional. -/
def modSixFunctional [Fintype I] (w : I → ℤ) : (I → ℤ) →+ ZMod 6 :=
  (Int.castAddHom (ZMod 6)).comp (integralFunctional w)

@[simp] theorem modSixFunctional_apply [Fintype I] (w y : I → ℤ) :
    modSixFunctional w y = (integralFunctional w y : ZMod 6) := rfl

/-- If the residual column coefficients are all divisible by six, the
modulo-six functional annihilates the entire residual image. -/
theorem modSixFunctional_annihilates [Fintype I] [Fintype J]
    (w z : I → ℤ) (d : J → ℤ) (hdiv : ∀ j, (6 : ℤ) ∣ d j) (x : J → ℤ) :
    modSixFunctional w (boundary (fun i j => d j * z i) x) = 0 := by
  rw [rankOne_boundary, modSixFunctional_apply, integralFunctional_mul]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 6).2
  apply dvd_mul_of_dvd_left
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (hdiv j) (x j)

/-- The primitive-vector Bézout identity gives the detecting value one. -/
theorem modSixFunctional_detects [Fintype I] (w z : I → ℤ)
    (hbezout : ∑ i, w i * z i = 1) : modSixFunctional w z = 1 := by
  rw [modSixFunctional_apply, integralFunctional_apply, hbezout, Int.cast_one]

/-- The residual source Bézout identity gives a chain bounding six times the
primitive residual vector. -/
theorem residual_bounding_chain [Fintype J] (z : I → ℤ) (d s : J → ℤ)
    (hbezout : ∑ j, s j * d j = 6) :
    boundary (fun i j => d j * z i) s = fun i => 6 * z i := by
  rw [rankOne_boundary, hbezout]

/-- Appendix A's final rank-one step: two explicit Bézout witnesses and the
column divisibilities yield the bounding equation and the detecting cocycle. -/
theorem rankOne_certificate [Fintype I] [Fintype J]
    (z w : I → ℤ) (d s : J → ℤ)
    (hprimitive : ∑ i, w i * z i = 1)
    (hcolumns : ∀ j, (6 : ℤ) ∣ d j)
    (hbound : ∑ j, s j * d j = 6) :
    boundary (fun i j => d j * z i) s = (fun i => 6 * z i) ∧
      (∀ x : J → ℤ, modSixFunctional w (boundary (fun i j => d j * z i) x) = 0) ∧
      modSixFunctional w z = 1 := by
  exact ⟨residual_bounding_chain z d s hbound,
    modSixFunctional_annihilates w z d hcolumns, modSixFunctional_detects w z hprimitive⟩

end Paper23.ResidualCertificate
