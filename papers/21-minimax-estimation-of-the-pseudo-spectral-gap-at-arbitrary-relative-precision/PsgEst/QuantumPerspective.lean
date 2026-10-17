import PsgEst.TraceExponential
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Quadratic perspectives and positive Sylvester operators

The function `(v,T) ↦ vᵀ T⁻¹ v` is jointly convex on positive definite real
matrices. The proof is the exact completing-square variational inequality.
The Hilbert--Schmidt operator below is represented on the actual pair index
`ι × ι`, with left and right multiplication in their usual orientation.
-/

open Matrix BigOperators Real
open scoped Kronecker

namespace PsgEst

section QuadraticPerspective

variable {κ α : Type*} [Fintype κ] [DecidableEq κ] [Fintype α]

/-- The actual matrix quadratic-over-linear function. -/
noncomputable def quadraticPerspective (v : κ → ℝ) (T : Matrix κ κ ℝ) : ℝ :=
  v ⬝ᵥ (T⁻¹ *ᵥ v)

private theorem perspective_inverse_cancel {T : Matrix κ κ ℝ} (hT : T.PosDef)
    (v : κ → ℝ) : T *ᵥ (T⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T
    ((Matrix.isUnit_iff_isUnit_det T).mp hT.isUnit), Matrix.one_mulVec]

omit [DecidableEq κ] in
private theorem perspective_dot_symmetric {T : Matrix κ κ ℝ} (hT : T.IsHermitian)
    (u w : κ → ℝ) : u ⬝ᵥ (T *ᵥ w) = w ⬝ᵥ (T *ᵥ u) := by
  have ht : T.transpose = T := by
    ext i j
    simpa only [Matrix.transpose_apply, star_trivial] using hT.apply i j
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ht, dotProduct_comm]

/-- Completing the positive quadratic square gives the variational upper bound. -/
theorem quadraticPerspective_variational {T : Matrix κ κ ℝ} (hT : T.PosDef)
    (v y : κ → ℝ) :
    2 * (v ⬝ᵥ y) - y ⬝ᵥ (T *ᵥ y) ≤ quadraticPerspective v T := by
  let z := T⁻¹ *ᵥ v
  have hz : T *ᵥ z = v := perspective_inverse_cancel hT v
  have hzy : z ⬝ᵥ (T *ᵥ y) = v ⬝ᵥ y := by
    rw [perspective_dot_symmetric hT.isHermitian, hz, dotProduct_comm]
  have hzz : z ⬝ᵥ (T *ᵥ z) = quadraticPerspective v T := by
    rw [hz, dotProduct_comm]
    rfl
  have hnonneg := hT.posSemidef.2 (y - z)
  simp only [star_trivial, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub] at hnonneg
  rw [hzy, hzz, hz, dotProduct_comm y v] at hnonneg
  linarith

/-- Finite joint convexity of the genuine quadratic matrix perspective. -/
theorem quadraticPerspective_joint_convex (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (v : α → κ → ℝ) (T : α → Matrix κ κ ℝ)
    (hT : ∀ a, (T a).PosDef) :
    quadraticPerspective (∑ a, p a • v a) (∑ a, p a • T a) ≤
      ∑ a, p a * quadraticPerspective (v a) (T a) := by
  let B := ∑ a, p a • T a
  let w := ∑ a, p a • v a
  let y := B⁻¹ *ᵥ w
  have hB : B.PosDef := weighted_sum_posDef p hp hsum T hT
  have hBy : B *ᵥ y = w := perspective_inverse_cancel hB w
  have hw : w ⬝ᵥ y = ∑ a, p a * (v a ⬝ᵥ y) := by
    dsimp only [w]
    simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul]
  have hquad : y ⬝ᵥ (B *ᵥ y) = ∑ a, p a * (y ⬝ᵥ (T a *ᵥ y)) := by
    dsimp only [B]
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum,
      dotProduct_smul, smul_eq_mul]
  have hmean : ∑ a, p a * (2 * (v a ⬝ᵥ y) - y ⬝ᵥ (T a *ᵥ y)) =
      2 * (w ⬝ᵥ y) - y ⬝ᵥ (B *ᵥ y) := by
    rw [hw, hquad, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  change quadraticPerspective w B ≤ _
  calc
    quadraticPerspective w B =
        ∑ a, p a * (2 * (v a ⬝ᵥ y) - y ⬝ᵥ (T a *ᵥ y)) := by
      rw [hmean, hBy, dotProduct_comm y w]
      change w ⬝ᵥ y = _
      ring
    _ ≤ _ := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (quadraticPerspective_variational (hT a) (v a) y) (hp a)

end QuadraticPerspective

section HilbertSchmidt

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Left multiplication `Y ↦ AY`, represented on the pair index. -/
def hsLeft (A : Matrix ι ι ℝ) : Matrix (ι × ι) (ι × ι) ℝ :=
  A ⊗ₖ (1 : Matrix ι ι ℝ)

/-- Right multiplication `Y ↦ YX`, represented on the pair index. -/
def hsRight (X : Matrix ι ι ℝ) : Matrix (ι × ι) (ι × ι) ℝ :=
  (1 : Matrix ι ι ℝ) ⊗ₖ X.transpose

/-- The actual positive Sylvester operator used in the resolvent perspective. -/
def sylvesterMatrix (s : ℝ) (A X : Matrix ι ι ℝ) : Matrix (ι × ι) (ι × ι) ℝ :=
  s • hsLeft A + (1 - s) • hsRight X

lemma hsLeft_mulVec (A : Matrix ι ι ℝ) (y : (ι × ι) → ℝ) (i j : ι) :
    (hsLeft A *ᵥ y) (i, j) = (A *ᵥ fun k => y (k, j)) i := by
  simp [hsLeft, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, ite_mul]

lemma hsRight_mulVec (X : Matrix ι ι ℝ) (y : (ι × ι) → ℝ) (i j : ι) :
    (hsRight X *ᵥ y) (i, j) = (X.transpose *ᵥ fun l => y (i, l)) j := by
  simp [hsRight, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply, ite_mul]

/-- Pair-index vectorization acts by the usual matrix Sylvester expression. -/
theorem sylvesterMatrix_mulVec (s : ℝ) (A X Y : Matrix ι ι ℝ) :
    sylvesterMatrix s A X *ᵥ (fun ij => Y ij.1 ij.2) =
      fun ij => (s • (A * Y) + (1 - s) • (Y * X)) ij.1 ij.2 := by
  unfold sylvesterMatrix
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
  ext ⟨i, j⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply]
  rw [hsLeft_mulVec, hsRight_mulVec]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]

lemma hsLeft_quadratic (A : Matrix ι ι ℝ) (y : (ι × ι) → ℝ) :
    y ⬝ᵥ (hsLeft A *ᵥ y) = ∑ j, (fun i => y (i, j)) ⬝ᵥ (A *ᵥ fun i => y (i, j)) := by
  simp only [dotProduct, Fintype.sum_prod_type, hsLeft_mulVec]
  rw [Finset.sum_comm]

lemma hsRight_quadratic (X : Matrix ι ι ℝ) (y : (ι × ι) → ℝ) :
    y ⬝ᵥ (hsRight X *ᵥ y) =
      ∑ i, (fun j => y (i, j)) ⬝ᵥ (X.transpose *ᵥ fun j => y (i, j)) := by
  simp only [dotProduct, Fintype.sum_prod_type, hsRight_mulVec]

/-- Left multiplication by a positive definite matrix is positive definite in HS space. -/
theorem hsLeft_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef) : (hsLeft A).PosDef := by
  have hherm : (hsLeft A).IsHermitian := by
    change (A ⊗ₖ (1 : Matrix ι ι ℝ))ᴴ = A ⊗ₖ 1
    rw [Matrix.conjTranspose_kronecker, hA.isHermitian.eq, Matrix.conjTranspose_one]
  refine ⟨hherm, ?_⟩
  intro y hy
  simp only [star_trivial, hsLeft_quadratic]
  obtain ⟨⟨i, j⟩, hij⟩ : ∃ q, y q ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hy (funext hn)
  have hcol : (fun k => y (k, j)) ≠ 0 := by
    intro hz
    exact hij (congrFun hz i)
  have hpos : 0 < (fun k => y (k, j)) ⬝ᵥ (A *ᵥ fun k => y (k, j)) := by
    simpa only [star_trivial] using hA.2 _ hcol
  exact hpos.trans_le (Finset.single_le_sum
    (fun b _ => by simpa only [star_trivial] using hA.posSemidef.2 (fun k => y (k, b)))
    (Finset.mem_univ j))

/-- Right multiplication by a positive definite matrix is positive definite in HS space. -/
theorem hsRight_posDef {X : Matrix ι ι ℝ} (hX : X.PosDef) : (hsRight X).PosDef := by
  have hherm : (hsRight X).IsHermitian := by
    change ((1 : Matrix ι ι ℝ) ⊗ₖ X.transpose)ᴴ = 1 ⊗ₖ X.transpose
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hX.transpose.isHermitian.eq]
  refine ⟨hherm, ?_⟩
  intro y hy
  simp only [star_trivial, hsRight_quadratic]
  obtain ⟨⟨i, j⟩, hij⟩ : ∃ q, y q ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hy (funext hn)
  have hrow : (fun l => y (i, l)) ≠ 0 := by
    intro hz
    exact hij (congrFun hz j)
  have hpos : 0 < (fun l => y (i, l)) ⬝ᵥ (X.transpose *ᵥ fun l => y (i, l)) := by
    simpa only [star_trivial] using hX.transpose.2 _ hrow
  exact hpos.trans_le (Finset.single_le_sum
    (fun b _ => by simpa only [star_trivial] using hX.transpose.posSemidef.2 (fun l => y (b, l)))
    (Finset.mem_univ i))

/-- Every interpolation parameter in `[0,1]` gives an actual positive definite
Sylvester matrix when both input matrices are positive definite. -/
theorem sylvesterMatrix_posDef {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {A X : Matrix ι ι ℝ} (hA : A.PosDef) (hX : X.PosDef) :
    (sylvesterMatrix s A X).PosDef := by
  by_cases hs0 : s = 0
  · simpa only [sylvesterMatrix, hs0, zero_smul, sub_zero, one_smul, zero_add]
      using hsRight_posDef hX
  · have hsp : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    exact ((hsLeft_posDef hA).smul hsp).add_posSemidef
      ((hsRight_posDef hX).posSemidef.smul (sub_nonneg.mpr hs.2))

/-- The Sylvester matrix is jointly linear in its two matrix arguments. -/
theorem sylvesterMatrix_weighted_sum (s : ℝ) (p : α → ℝ)
    (A X : α → Matrix ι ι ℝ) :
    sylvesterMatrix s (∑ a, p a • A a) (∑ a, p a • X a) =
      ∑ a, p a • sylvesterMatrix s (A a) (X a) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [sylvesterMatrix, hsLeft, hsRight, Matrix.kronecker_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.transpose_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- A verified solution of the actual Sylvester matrix equation identifies the
inverse action, without a simultaneous-diagonalization assumption. -/
theorem sylvesterMatrix_inverse_mulVec {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {A X : Matrix ι ι ℝ} (hA : A.PosDef) (hX : X.PosDef)
    (V W : Matrix ι ι ℝ)
    (hsol : s • (A * W) + (1 - s) • (W * X) = V) :
    (sylvesterMatrix s A X)⁻¹ *ᵥ (fun ij => V ij.1 ij.2) =
      fun ij => W ij.1 ij.2 := by
  have haction := sylvesterMatrix_mulVec s A X W
  rw [hsol] at haction
  rw [← haction, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (sylvesterMatrix_posDef hs hA hX).isUnit),
    Matrix.one_mulVec]

/-- The resolvent quadratic kernel for matrix relative entropy is jointly convex
in its actual matrix arguments. -/
theorem sylvester_quadraticPerspective_joint_convex (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (A X : α → Matrix ι ι ℝ)
    (hA : ∀ a, (A a).PosDef) (hX : ∀ a, (X a).PosDef) :
    quadraticPerspective (fun ij => (∑ a, p a • X a) ij.1 ij.2)
      (sylvesterMatrix s (∑ a, p a • A a) (∑ a, p a • X a)) ≤
      ∑ a, p a * quadraticPerspective (fun ij => X a ij.1 ij.2)
        (sylvesterMatrix s (A a) (X a)) := by
  have hv : (fun ij : ι × ι => (∑ a, p a • X a) ij.1 ij.2) =
      ∑ a, p a • (fun ij : ι × ι => X a ij.1 ij.2) := by
    ext ⟨i, j⟩
    simp only [Matrix.sum_apply, Matrix.smul_apply, Finset.sum_apply, Pi.smul_apply]
  rw [hv, sylvesterMatrix_weighted_sum]
  exact quadraticPerspective_joint_convex p hp hsum _ _
    (fun a => sylvesterMatrix_posDef hs (hA a) (hX a))

end HilbertSchmidt

end PsgEst
