import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Combinatorial fusion-category data

Finite multiplicity data with positive Frobenius–Perron dimensions,
a distinguished unit and duality.  The paper's arguments about integrality,
pivotal slopes, Müger centers and modular extensions are formalized against
this data.
-/

noncomputable section

open Classical

universe u

open scoped BigOperators

namespace Paper18

/-- Combinatorial multiplicity data of simple objects with
positive Frobenius–Perron dimensions, a distinguished unit and duality. -/
structure FusionBasis (ι : Type u) [Fintype ι] where
  /-- Frobenius–Perron dimension of a simple object. -/
  fpdim : ι → ℝ
  /-- Isomorphism class of the tensor unit. -/
  one : ι
  /-- Duality involution on simple objects. -/
  dual : ι → ι
  /-- Fusion coefficients `N x y z = dim Hom(z, x ⊗ y)`. -/
  N : ι → ι → ι → ℕ
  /-- FP dimensions are strictly positive. -/
  fpdim_pos : ∀ x, 0 < fpdim x
  /-- The unit has FP dimension one. -/
  fpdim_one : fpdim one = 1
  /-- Duality preserves FP dimension. -/
  fpdim_dual : ∀ x, fpdim (dual x) = fpdim x
  /-- Duality is an involution. -/
  dual_involutive : ∀ x, dual (dual x) = x
  /-- The unit is self-dual. -/
  dual_one : dual one = one
  /-- `N one x y` detects `x = y`. -/
  N_one_left : ∀ x y, N one x y = if x = y then 1 else 0
  /-- `N x one y` detects `x = y`. -/
  N_one_right : ∀ x y, N x one y = if x = y then 1 else 0
  /-- Left Frobenius reciprocity. -/
  N_dual : ∀ x y z, N x y z = N (dual x) z y
  /-- Right Frobenius reciprocity. -/
  N_right : ∀ x y z, N x y z = N z (dual y) x
  /-- FP dimension is multiplicative on the based fusion product. -/
  fpdim_mul : ∀ x y, ∑ z, (N x y z : ℝ) * fpdim z = fpdim x * fpdim y

namespace FusionBasis

variable {ι : Type u} [Fintype ι] (B : FusionBasis ι)

attribute [simp] fpdim_one fpdim_dual dual_involutive dual_one

/-- Total Frobenius–Perron dimension `∑ fpdim x ^ 2`. -/
def totalFPdim : ℝ := ∑ x, B.fpdim x ^ 2

/-- A fusion category is *integral* when every simple has integer FP dimension. -/
def Integral : Prop := ∀ x : ι, ∃ n : ℤ, B.fpdim x = n

/-- A fusion category is *weakly integral* when its total FP dimension is an integer. -/
def WeaklyIntegral : Prop := ∃ N : ℤ, B.totalFPdim = N

/-- Simple `x` is invertible when `fpdim x = 1`. -/
def IsInvertible (x : ι) : Prop := B.fpdim x = 1

/-- The set of invertible simple objects. -/
def invertibles : Set ι := {x | B.IsInvertible x}

lemma integral_of_fpdim_nat (h : ∀ x : ι, ∃ n : ℕ, B.fpdim x = n) : B.Integral := by
  intro x
  obtain ⟨n, hn⟩ := h x
  refine ⟨(n : ℤ), ?_⟩
  simp [hn]

lemma fpdim_eq_coe_nat_of_integral (h : B.Integral) (x : ι) :
    ∃ n : ℕ, B.fpdim x = n := by
  obtain ⟨n, hn⟩ := h x
  have hpos : (0:ℤ) < n := by
    have := B.fpdim_pos x
    rw [hn] at this
    exact_mod_cast this
  refine ⟨n.natAbs, ?_⟩
  have hnn : n = (n.natAbs : ℤ) := (Int.natAbs_of_nonneg (le_of_lt hpos)).symm
  rw [hn, hnn]
  simp

lemma integral_iff_fpdim_nat :
    B.Integral ↔ ∀ x : ι, ∃ n : ℕ, B.fpdim x = n :=
  ⟨fun h => B.fpdim_eq_coe_nat_of_integral h, B.integral_of_fpdim_nat⟩

lemma isDual_invertible {x : ι} (hx : B.IsInvertible x) : B.IsInvertible (B.dual x) := by
  dsimp [IsInvertible] at *
  rwa [B.fpdim_dual]

lemma N_one_left_apply (x y : ι) :
    B.N B.one x y = if x = y then 1 else 0 := B.N_one_left x y

lemma N_one_right_apply (x y : ι) :
    B.N x B.one y = if x = y then 1 else 0 := B.N_one_right x y

lemma N_one_self : B.N B.one B.one B.one = 1 := by
  rw [B.N_one_left]
  simp

lemma dual_injective : Function.Injective B.dual := by
  intro x y h
  have h1 := congrArg B.dual h
  simpa [B.dual_involutive] using h1

lemma dual_surjective : Function.Surjective B.dual := by
  intro x
  exact ⟨B.dual x, B.dual_involutive x⟩

lemma dual_bijective : Function.Bijective B.dual :=
  ⟨B.dual_injective, B.dual_surjective⟩

/-- Dimension of `Hom(z, x ⊗ y)` as a real number. -/
def homDim (x y z : ι) : ℝ := (B.N x y z : ℝ)

@[simp]
lemma homDim_one_left (x z : ι) :
    B.homDim B.one x z = if x = z then (1:ℝ) else 0 := by
  classical
  simp [homDim, B.N_one_left]

@[simp]
lemma homDim_one_right (x z : ι) :
    B.homDim x B.one z = if x = z then (1:ℝ) else 0 := by
  classical
  simp [homDim, B.N_one_right]

end FusionBasis

end Paper18
