import Paper18.Fusion.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Pivotal and spherical structures on fusion data

A pivotal structure equips each simple `X` with a pivotal dimension `d_X ∈ ℂ`
and a slope `γ_X = d_X / d_{X*}`.  A spherical structure has `γ_X = 1` for all
simples.  Balancing (twist) data `θ` satisfies `θ_{X*} = θ_X γ_X^{-1}`.
-/

noncomputable section

open Classical

universe u

open scoped BigOperators

namespace Paper18

/-- Pivotal dimension data on a fusion basis. -/
structure PivotalData {ι : Type u} [Fintype ι] (B : FusionBasis ι) where
  /-- Pivotal dimension `d_X` of a simple object. -/
  jdim : ι → ℂ
  /-- Pivotal dimensions are nonzero on simples. -/
  jdim_ne_zero : ∀ x, jdim x ≠ 0
  /-- The unit has pivotal dimension one. -/
  jdim_one : jdim B.one = 1
  /-- Multiplicativity along tensor:
  `d_X d_Y = ∑_Z N x y z · d_Z`. -/
  jdim_tensor : ∀ x y : ι,
      jdim x * jdim y = ∑ z, (B.N x y z : ℂ) * jdim z

namespace PivotalData

variable {ι : Type u} [Fintype ι] {B : FusionBasis ι} (J : PivotalData B)

/-- Slope scalar `γ_X = d_X / d_{X*}`. -/
def gamma (x : ι) : ℂ := J.jdim x / J.jdim (B.dual x)

/-- Quantum dimension `n_X = d_X d_{X*}`. -/
def ndim (x : ι) : ℂ := J.jdim x * J.jdim (B.dual x)

@[simp]
lemma gamma_one : J.gamma B.one = 1 := by
  simp [gamma, J.jdim_one, B.dual_one]

@[simp]
lemma ndim_one : J.ndim B.one = 1 := by
  simp [ndim, J.jdim_one, B.dual_one]

lemma gamma_dual (x : ι) : J.gamma (B.dual x) = (J.gamma x)⁻¹ := by
  have hx : J.jdim x ≠ 0 := J.jdim_ne_zero x
  have hd : J.jdim (B.dual x) ≠ 0 := J.jdim_ne_zero (B.dual x)
  simp only [gamma, B.dual_involutive]
  field_simp [hx, hd]

lemma ndim_dual (x : ι) : J.ndim (B.dual x) = J.ndim x := by
  simp [ndim, B.dual_involutive, mul_comm]

lemma jdim_eq_gamma_mul_jdim_dual (x : ι) :
    J.jdim x = J.gamma x * J.jdim (B.dual x) := by
  have hd : J.jdim (B.dual x) ≠ 0 := J.jdim_ne_zero (B.dual x)
  simp only [gamma]
  field_simp [hd]

/-- A pivotal structure is *spherical* when all slopes equal one. -/
def Spherical : Prop := ∀ x : ι, J.gamma x = 1

lemma spherical_iff_jdim_dual :
    J.Spherical ↔ ∀ x : ι, J.jdim x = J.jdim (B.dual x) := by
  constructor
  · intro h x
    have hx := h x
    simp only [gamma] at hx
    have hd : J.jdim (B.dual x) ≠ 0 := J.jdim_ne_zero (B.dual x)
    exact (div_eq_one_iff_eq hd).mp hx
  · intro h x
    simp only [gamma, h x, div_self (J.jdim_ne_zero _)]

lemma ndim_eq_sq_of_spherical (h : J.Spherical) (x : ι) :
    J.ndim x = J.jdim x ^ 2 := by
  have hx := (J.spherical_iff_jdim_dual.mp h) x
  simp [ndim, hx, pow_two]

lemma jdim_dual_of_spherical (h : J.Spherical) (x : ι) :
    J.jdim (B.dual x) = J.jdim x :=
  (J.spherical_iff_jdim_dual.mp h) x |>.symm

lemma gamma_eq_one_of_spherical (h : J.Spherical) (x : ι) : J.gamma x = 1 := h x

end PivotalData

/-! ## Balancing / twist data -/

/-- Balancing (twist) data compatible with a pivotal structure. -/
structure BalancingData {ι : Type u} [Fintype ι] {B : FusionBasis ι}
    (J : PivotalData B) where
  /-- Twist scalar `θ_X`. -/
  theta : ι → ℂ
  /-- Twists are nonzero. -/
  theta_ne_zero : ∀ x, theta x ≠ 0
  /-- The unit is untwisted. -/
  theta_one : theta B.one = 1
  /-- Twists of duals: `θ_{X*} = θ_X · γ_X^{-1}`. -/
  theta_dual : ∀ x : ι, theta (B.dual x) = theta x * (J.gamma x)⁻¹

namespace BalancingData

variable {ι : Type u} [Fintype ι] {B : FusionBasis ι} {J : PivotalData B}
  (θ : BalancingData J)

lemma theta_one_eq : θ.theta B.one = 1 := θ.theta_one

/-- Combined scalar `θ_X n_X` used in Gauss sums. -/
def gaussWeight (x : ι) : ℂ := θ.theta x * J.ndim x

lemma theta_ndim_dual (x : ι) :
    θ.theta (B.dual x) * J.ndim (B.dual x) =
      θ.theta x * J.ndim x * (J.gamma x)⁻¹ := by
  rw [θ.theta_dual, J.ndim_dual]
  ring

/-- Twist of the unit squared is one. -/
@[simp]
lemma theta_one_sq : θ.theta B.one ^ 2 = 1 := by
  rw [θ.theta_one]
  simp

end BalancingData

lemma spherical_gamma_eq_one {ι : Type u} [Fintype ι] {B : FusionBasis ι}
    {J : PivotalData B} (h : J.Spherical) (x : ι) : J.gamma x = 1 := h x

end Paper18
