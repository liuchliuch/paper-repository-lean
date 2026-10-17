import Paper14.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
/-!
# Algebraic properties of the BCZ map

Paper anchors: Ex8 (`B^{-1}`), S2.p3 (linear branches of determinant one, preserves `m`).

This file proves the elementary floor inequalities behind `B`, that `B` maps `Ω` into `Ω`,
the two-sided algebraic inverse identities on `Ω`, positivity of `τ` on `Ω`, and
determinant one of each linear branch `(a,b) ↦ (b, k*b - a)`.
-/
open MeasureTheory Filter Topology Set Matrix
namespace Paper14

/-! ## Floor bounds for the BCZ branch -/

/-- Floor lower piece: `k * b ≤ 1 + a` for `k = ⌊(1+a)/b⌋`, `b > 0`. -/
theorem floor_branch_le (a b : ℝ) (hb : 0 < b) :
    ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b ≤ 1 + a := by
  have h := Int.floor_le ((1 + a) / b)
  nlinarith [div_mul_cancel₀ (1 + a) (ne_of_gt hb)]

/-- Floor upper piece: `1 - b < k * b - a` for `k = ⌊(1+a)/b⌋`, `b > 0`. -/
theorem lt_floor_branch_sub (a b : ℝ) (hb : 0 < b) :
    1 - b < ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a := by
  have h := Int.lt_floor_add_one ((1 + a) / b)
  nlinarith [div_mul_cancel₀ (1 + a) (ne_of_gt hb)]

/-- Standard consequence: `k*b - a ≤ 1` and `k*b - a < 1 + b`. -/
theorem floor_branch_sub_bounds (a b : ℝ) (hb : 0 < b) :
    ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a ≤ 1 ∧
      ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a < 1 + b := by
  refine ⟨?_, ?_⟩
  · have := floor_branch_le a b hb
    linarith
  · have := floor_branch_le a b hb
    linarith

/-- `⌊(1-a)/b⌋ = 0` when `b > 0`, `a ≤ 1`, `1 < a + b`. -/
theorem floor_one_sub_div_eq_zero {a b : ℝ} (hb : 0 < b) (ha : a ≤ 1) (hs : 1 < a + b) :
    ⌊(1 - a) / b⌋ = 0 := by
  rw [Int.floor_eq_zero_iff]
  refine ⟨div_nonneg ?_ (le_of_lt hb), (div_lt_one hb).2 ?_⟩
  · linarith
  · linarith

/-- `⌊(1-b)/a⌋ = 0` when `a > 0`, `b ≤ 1`, `1 < a + b`. -/
theorem floor_one_sub_div_eq_zero' {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) (hs : 1 < a + b) :
    ⌊(1 - b) / a⌋ = 0 := by
  rw [Int.floor_eq_zero_iff]
  refine ⟨div_nonneg ?_ (le_of_lt ha), (div_lt_one ha).2 ?_⟩
  · linarith
  · linarith

/-! ## Coordinate unfolds for `B` and `Binv` -/

theorem B_fst (a b : ℝ) : (B (a, b)).1 = b := rfl

theorem B_snd (a b : ℝ) :
    (B (a, b)).2 = ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a := rfl

theorem B_apply (a b : ℝ) :
    B (a, b) = (b, ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a) := rfl

theorem B'_apply (a b : ℝ) :
    B' a b = (b, ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a) := rfl

theorem Binv_apply (a b : ℝ) :
    Binv (a, b) = (((⌊(1 + b) / a⌋ : ℤ) : ℝ) * a - b, a) := rfl

theorem Binv_fst (a b : ℝ) :
    (Binv (a, b)).1 = ((⌊(1 + b) / a⌋ : ℤ) : ℝ) * a - b := rfl

theorem Binv_snd (a b : ℝ) : (Binv (a, b)).2 = a := rfl

/-! ## `B` maps `Ω` into `Ω` -/

/-- The BCZ map sends `Ω` to `Ω`. -/
theorem B_mem_Omega {a b : ℝ} (h : (a, b) ∈ Omega) : B (a, b) ∈ Omega := by
  rcases mem_Omega.1 h with ⟨ha0, ha1, hb0, hb1, hsum⟩
  have hb : 0 < b := hb0
  have hlow := lt_floor_branch_sub a b hb
  have hup := (floor_branch_sub_bounds a b hb).1
  rw [B_apply, mem_Omega]
  exact ⟨hb0, hb1, by linarith, by linarith, by linarith⟩

theorem Binv_mem_Omega {a b : ℝ} (h : (a, b) ∈ Omega) : Binv (a, b) ∈ Omega := by
  rcases mem_Omega.1 h with ⟨ha0, ha1, hb0, hb1, hsum⟩
  have ha : 0 < a := ha0
  have hlow := lt_floor_branch_sub b a ha
  have hup := (floor_branch_sub_bounds b a ha).1
  rw [Binv_apply, mem_Omega]
  exact ⟨by linarith, by linarith, ha0, ha1, by linarith⟩

/-! ## Algebraic inverse identities on `Ω` -/

/-- `Binv ∘ B = id` on `Ω`. -/
theorem Binv_B (a b : ℝ) (h : (a, b) ∈ Omega) : Binv (B (a, b)) = (a, b) := by
  rcases mem_Omega.1 h with ⟨ha0, ha1, hb0, hb1, hsum⟩
  have hb : 0 < b := hb0
  have hB : B (a, b) = (b, ((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a) := rfl
  have hdiv :
      (1 + (((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a)) / b
        = ((⌊(1 + a) / b⌋ : ℤ) : ℝ) + (1 - a) / b := by
    field_simp [ne_of_gt hb]
    ring
  have hfloor : ⌊(1 + (((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a)) / b⌋ = (⌊(1 + a) / b⌋ : ℤ) := by
    rw [hdiv, Int.floor_intCast_add]
    have hz : ⌊(1 - a) / b⌋ = 0 := floor_one_sub_div_eq_zero hb0 ha1 hsum
    rw [hz]
    ring
  rw [hB]
  show (((⌊(1 + (((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a)) / b⌋ : ℤ) : ℝ) * b
        - (((⌊(1 + a) / b⌋ : ℤ) : ℝ) * b - a), b) = (a, b)
  rw [hfloor]
  refine Prod.ext ?_ rfl
  ring

/-- `B ∘ Binv = id` on `Ω`. -/
theorem B_Binv (a b : ℝ) (h : (a, b) ∈ Omega) : B (Binv (a, b)) = (a, b) := by
  rcases mem_Omega.1 h with ⟨ha0, ha1, hb0, hb1, hsum⟩
  have ha : 0 < a := ha0
  have hdiv :
      (1 + (((⌊(1 + b) / a⌋ : ℤ) : ℝ) * a - b)) / a
        = ((⌊(1 + b) / a⌋ : ℤ) : ℝ) + (1 - b) / a := by
    field_simp [ne_of_gt ha]
    ring
  have hfloor : ⌊(1 + (((⌊(1 + b) / a⌋ : ℤ) : ℝ) * a - b)) / a⌋ = (⌊(1 + b) / a⌋ : ℤ) := by
    rw [hdiv, Int.floor_intCast_add]
    have hz : ⌊(1 - b) / a⌋ = 0 := floor_one_sub_div_eq_zero' ha0 hb1 hsum
    rw [hz]
    ring
  rw [Binv_apply]
  show (a, ((⌊(1 + (((⌊(1 + b) / a⌋ : ℤ) : ℝ) * a - b)) / a⌋ : ℤ) : ℝ) * a
        - (((⌊(1 + b) / a⌋ : ℤ) : ℝ) * a - b)) = (a, b)
  rw [hfloor]
  refine Prod.ext rfl ?_
  ring

/-! ## Statement forms (paper Ex8) -/

/-- Paper Ex8: `B ∘ Binv = id` on `Ω` (mod the floor branch). -/
def BInverseLeftStatement : Prop :=
  ∀ a b : ℝ, (a, b) ∈ Omega → B (Binv (a, b)) = (a, b)

/-- Paper Ex8: `Binv ∘ B = id` on `Ω`. -/
def BInverseRightStatement : Prop :=
  ∀ a b : ℝ, (a, b) ∈ Omega → Binv (B (a, b)) = (a, b)

theorem BInverseLeft : BInverseLeftStatement := fun a b h => B_Binv a b h

theorem BInverseRight : BInverseRightStatement := fun a b h => Binv_B a b h

/-! ## `τ` is positive on `Ω` -/

theorem tau_pos {x : ℝ × ℝ} (hx : x ∈ Omega) : 0 < tau x := by
  rcases mem_Omega.1 hx with ⟨ha0, _, hb0, _, _⟩
  rw [tau_apply]
  exact one_div_pos.2 (mul_pos ha0 hb0)

theorem tau_pos_of (a b : ℝ) (h : (a, b) ∈ Omega) : 0 < tau (a, b) :=
  tau_pos h

theorem one_div_mul_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < 1 / (a * b) :=
  one_div_pos.2 (mul_pos ha hb)

/-! ## Linear branches have determinant one -/

/-- Linear branch of `B` on a fixed floor level `k`. -/
def branchMap (k : ℤ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.2, (k : ℝ) * x.2 - x.1)

theorem branchMap_apply (k : ℤ) (a b : ℝ) :
    branchMap k (a, b) = (b, (k : ℝ) * b - a) := rfl

/-- Matrix of the branch `(a,b) ↦ (b, k*b - a)`, i.e. `[[0,1],[-1,k]]`. -/
def branchMat (k : ℤ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, (k : ℝ)]

/-- Each linear branch has determinant one. -/
theorem branchMat_det_one (k : ℤ) : (branchMat k).det = 1 := by
  unfold branchMat
  rw [Matrix.det_fin_two_of]
  ring

theorem branchMat_det_eq (k : ℤ) : Matrix.det !![0, 1; -1, (k : ℝ)] = 1 := by
  rw [Matrix.det_fin_two_of]
  ring

/-- Determinant one of the abstract linear branch. -/
def BDetOneStatement : Prop := ∀ k : ℤ, Matrix.det !![0, 1; -1, (k : ℝ)] = 1

theorem BDetOne : BDetOneStatement := branchMat_det_eq

end Paper14
