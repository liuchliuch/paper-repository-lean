import ELV.Basic
import ELV.CostIdentities
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Oracle data and the admissible witness program (paper 05 §2, §4.1)
-/

noncomputable section

namespace ELV

namespace Model

abbrev Mspace (n : ℕ) := EuclideanSpace ℂ (Fin (2 * n))

/-- Known input `s = e_0`. -/
def knownInput (n : ℕ) [NeZero n] : Mspace n :=
  (EuclideanSpace.basisFun (Fin (2 * n)) ℂ) 0

lemma knownInput_norm (n : ℕ) [NeZero n] : ‖knownInput n‖ = 1 := by
  unfold knownInput
  exact Orthonormal.norm_eq_one
    (EuclideanSpace.basisFun (Fin (2 * n)) ℂ).orthonormal 0

/-- Oracle: norm-preserving linear map on `M`. -/
structure Oracle (n : ℕ) where
  U : Mspace n →ₗ[ℂ] Mspace n
  norm_preserving : ∀ v, ‖U v‖ = ‖v‖

namespace Oracle

variable {n : ℕ} (O : Oracle n)

/-- Generated state `φ_O = O s` (2.1). -/
def phi [NeZero n] : Mspace n := O.U (knownInput n)

/-- Answer probability `p_O = ‖Π₁ φ_O‖²` (2.1): squared norm of the
    answer-`1` block (indices `i.val ≥ n`). -/
def p [NeZero n] : ℝ :=
  ∑ i : Fin (2 * n), if n ≤ i.val then ‖O.phi i‖ ^ 2 else 0

lemma phi_norm [NeZero n] : ‖O.phi‖ = 1 := by
  unfold phi
  rw [O.norm_preserving]
  exact knownInput_norm n

lemma p_nonneg [NeZero n] : 0 ≤ O.p := by
  unfold p
  exact Finset.sum_nonneg fun i _ => by
    by_cases h : n ≤ i.val
    · simp [h]
    · simp [h]

lemma p_le_one [NeZero n] : O.p ≤ 1 := by
  unfold p
  have hle : (∑ i : Fin (2 * n), if n ≤ i.val then ‖O.phi i‖ ^ 2 else 0)
      ≤ ∑ i : Fin (2 * n), ‖O.phi i‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => by
      by_cases h : n ≤ i.val
      · simp [h]
      · simp [h]
  have hsum : ‖O.phi‖ ^ 2 = ∑ i, ‖O.phi i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
  nlinarith [O.phi_norm]

/-- Promised family (2.2). -/
def Promised (δ : ℝ) [NeZero n] : Prop :=
  O.p ≤ 1 / 2 - δ ∨ O.p ≥ 1 / 2 + δ

/-- Answer label `r_O` (2.2). -/
def r [NeZero n] : Fin 2 := if O.p ≤ 1 / 2 then 0 else 1

end Oracle

/-! ## Proposition 4.1 witness program -/

/-- Public Gram difference `F_xy = 1_{r_x ≠ r_y}`. -/
def publicF {X : Type*} (r : X → Fin 2) (x y : X) : ℂ :=
  if r x = r y then (0 : ℂ) else 1

/-- Proposition 4.1 constraint (4.2). -/
def Prop41Constraint {X ι : Type*} [Fintype ι]
    (φ : X → EuclideanSpace ℂ (Fin 2))
    (r : X → Fin 2)
    (f g : X → EuclideanSpace ℂ ι) : Prop :=
  ∀ x y : X,
    publicF r x y =
      (1 - @inner ℂ _ _ (φ x) (φ y)) *
        (@inner ℂ _ _ (f x) (f y) - @inner ℂ _ _ (g x) (g y))

/-- Witness cost (4.1): `sup_x (‖f_x‖² + ‖g_x‖²)` over the finite index. -/
def witnessCost {X ι : Type*} [Fintype X] [Fintype ι] [Nonempty X]
    (f g : X → EuclideanSpace ℂ ι) : ℝ :=
  ⨆ x : X, (‖f x‖ ^ 2 + ‖g x‖ ^ 2 : ℝ)

/-- Admissible optimization value (Proposition 4.1). -/
def admOptimum {X : Type*} [Fintype X] [Nonempty X]
    (φ : X → EuclideanSpace ℂ (Fin 2)) (r : X → Fin 2) : ℝ :=
  sInf { c : ℝ | ∃ (ι : Type) (_ : Fintype ι) (f g : X → EuclideanSpace ℂ ι),
    Prop41Constraint φ r f g ∧ c = witnessCost f g }

end Model

end ELV
