import PsgEst.GapsOfPowers
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The operator norm identity in equation (2)

The second sorted singular value of `L_t` is exactly the Euclidean operator
norm of `L_t - vvᵀ`, where `v_i = √π_i`. This identifies the scalar `bNorm`
with the norm used in the paper, including the one-state convention.
-/

open Matrix BigOperators Real

namespace PsgEst

variable {d : ℕ}

/-- Similarity transforms preserve subtraction. -/
theorem simil_sub (mu : Fin d → ℝ) (A B : Matrix (Fin d) (Fin d) ℝ) :
    simil mu (A - B) = simil mu A - simil mu B := by
  simp only [simil, Matrix.mul_sub, Matrix.sub_mul]

/-- The stationary rank-one operator becomes the Euclidean orthogonal projection. -/
theorem simil_piMat_eq_piProj (S : Stoch d) (st : Stationary S) :
    simil st.mu (piMat st.mu) = piProj st := by
  ext i j
  simp only [simil, Matrix.mul_diagonal, Matrix.diagonal_mul, piMat, piProj, stVec]
  have hj : st.mu j * st.mu j ^ (-(1 / 2 : ℝ)) = st.mu j ^ (1 / 2 : ℝ) := by
    calc
      _ = st.mu j ^ (1 : ℝ) * st.mu j ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = st.mu j ^ ((1 : ℝ) + -(1 / 2 : ℝ)) :=
        (Real.rpow_add (st.pos j) _ _).symm
      _ = _ := by norm_num
  rw [mul_assoc, hj]

/-- The actual centered transition operator `P^t - Π` has normalized matrix `L_t-vvᵀ`. -/
theorem simil_centered_eq_LkSub (S : Stoch d) (st : Stationary S) (t : ℕ) :
    simil st.mu (S.P ^ t - piMat st.mu) = LkSub S st t := by
  rw [simil_sub, simil_piMat_eq_piProj]
  rfl

/-- Operator norm on the stationary weighted Euclidean space, expressed by its
isometric diagonal change of coordinates. -/
noncomputable def weightedOperatorNorm [DecidableEq (Fin d)] (mu : Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (simil mu A)‖

private theorem real_euclidean_norm_sq (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq x

/-- Orthogonal projection off the stationary direction cannot increase length,
and the action of `L_t` there is bounded by its second singular value. -/
theorem LkSub_sq_bound [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S)
    (t : ℕ) (hd : 1 < d) (x : Fin d → ℝ) :
    ∑ i, (LkSub S st t *ᵥ x) i ^ 2 ≤
      sigma2 (Lk S st t) ^ 2 * ∑ i, x i ^ 2 := by
  classical
  let c : ℝ := ∑ i, stVec st i * x i
  let y : Fin d → ℝ := x - c • stVec st
  have hxy : ∑ i, x i * stVec st i = c := by
    dsimp [c]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hyorth : ∑ i, y i * stVec st i = 0 := by
    calc
      _ = (∑ i, x i * stVec st i) - c * ∑ i, stVec st i * stVec st i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp only [y, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      _ = 0 := by rw [hxy, stVec_sq_sum]; ring
  have hynorm : ∑ i, y i ^ 2 ≤ ∑ i, x i ^ 2 := by
    have he : ∑ i, y i ^ 2 = (∑ i, x i ^ 2) - c ^ 2 := by
      calc
        _ = (∑ i, x i ^ 2) - 2 * c * (∑ i, x i * stVec st i) +
            c ^ 2 * ∑ i, stVec st i * stVec st i := by
          simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          simp only [y, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        _ = _ := by rw [hxy, stVec_sq_sum]; ring
    linarith [sq_nonneg c]
  have hLy : Lk S st t *ᵥ y = LkSub S st t *ᵥ x := by
    dsimp only [y]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Lk_mulVec_stVec]
    funext i
    rw [LkSub_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    change (Lk S st t *ᵥ x) i - c * stVec st i =
      (Lk S st t *ᵥ x) i - stVec st i * c
    ring
  have hb := sigma2_bound_fixed (Lk S st t) (stVec st) hd (stVec_sq_sum st)
    (Lk_mulVec_stVec S st t) (Lk_transpose_mulVec_stVec S st t)
    (Lk_contraction S st t) y hyorth
  rw [hLy] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hynorm (sq_nonneg _))

/-- The second sorted singular value is the norm of the centered Markov operator. -/
theorem sigma2_eq_norm_LkSub [DecidableEq (Fin d)] (S : Stoch d)
    (st : Stationary S) (t : ℕ) :
    sigma2 (Lk S st t) = ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (LkSub S st t)‖ := by
  classical
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (LkSub S st t)
  have hsnonneg : 0 ≤ sigma2 (Lk S st t) :=
    (sigma2_mem_of_contraction _ (Lk_contraction S st t)).1
  by_cases hd : 1 < d
  · apply le_antisymm
    · obtain ⟨x, hx, hxv, hxL⟩ := (sigma2_rayleigh_fixed (Lk S st t) (stVec st) hd
        (stVec_sq_sum st) (Lk_mulVec_stVec S st t)
        (Lk_transpose_mulVec_stVec S st t) (Lk_contraction S st t)).2
      have hxv' : ∑ i, stVec st i * x i = 0 := by simpa only [mul_comm] using hxv
      have hMx : LkSub S st t *ᵥ x = Lk S st t *ᵥ x := by
        funext i
        rw [LkSub_mulVec]
        simp only [hxv', mul_zero, sub_zero]
      have hxin : ‖WithLp.toLp 2 x‖ = (1 : ℝ) := by
        have hh := real_euclidean_norm_sq (WithLp.toLp 2 x)
        change ‖WithLp.toLp 2 x‖ ^ 2 = ∑ i, x i ^ 2 at hh
        rw [hx] at hh
        nlinarith [norm_nonneg (WithLp.toLp 2 x)]
      have hxout : ‖T (WithLp.toLp 2 x)‖ = sigma2 (Lk S st t) := by
        apply (sq_eq_sq₀ (norm_nonneg _) hsnonneg).mp
        change ‖WithLp.toLp 2 (LkSub S st t *ᵥ x)‖ ^ 2 = _
        rw [real_euclidean_norm_sq, hMx]
        exact hxL
      have hh := T.le_opNorm (WithLp.toLp 2 x)
      rw [hxin, hxout, mul_one] at hh
      exact hh
    · apply T.opNorm_le_bound hsnonneg
      intro x
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hsnonneg (norm_nonneg _))).mp
      change ‖WithLp.toLp 2 (LkSub S st t *ᵥ WithLp.ofLp x)‖ ^ 2 ≤ _
      rw [mul_pow, real_euclidean_norm_sq, real_euclidean_norm_sq]
      exact LkSub_sq_bound S st t hd (WithLp.ofLp x)
  · have hdne : d ≠ 0 := by
      intro hz
      subst d
      have hh := st.sum_one
      simp at hh
    have hd1 : d = 1 := by omega
    subst d
    have hmu : st.mu = fun _ => (1 : ℝ) := by
      funext i
      fin_cases i
      simpa using st.sum_one
    have hPt (i j : Fin 1) : (S.pow t).P i j = 1 := by
      fin_cases i
      fin_cases j
      simpa using (S.pow t).row_stoch 0
    have hM : LkSub S st t = 0 := by
      ext i j
      fin_cases i
      fin_cases j
      simp [LkSub, Lk, simil, piProj, stVec, hmu]
      change (S.pow t).P 0 0 - 1 = 0
      rw [hPt, sub_self]
    simp [sigma2, hM]

/-- Equation (2): the square-root deficit used throughout the formalization is
precisely the Euclidean operator norm of the centered similarity transform. -/
theorem bNorm_eq_operatorNorm [DecidableEq (Fin d)] (S : Stoch d)
    (st : Stationary S) (t : ℕ) :
    bNorm S st t = ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (LkSub S st t)‖ := by
  rw [← sigma2_eq_norm_LkSub S st t]
  have hs := (sigma2_mem_of_contraction _ (Lk_contraction S st t)).1
  simp only [bNorm, gapB, aK, aOf, sub_sub_cancel,
    max_eq_right (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hs]

/-- Every centered similarity-transform entry is controlled by the paper's
contraction norm. This is useful for recovering strict positivity of powers. -/
theorem LkSub_entry_abs_le_bNorm [DecidableEq (Fin d)] (S : Stoch d)
    (st : Stationary S) (t : ℕ) (i j : Fin d) :
    |LkSub S st t i j| ≤ bNorm S st t := by
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (LkSub S st t)
  have he : (T (EuclideanSpace.single j (1 : ℝ))) i = LkSub S st t i j := by
    change (LkSub S st t *ᵥ Pi.single j 1) i = _
    simp only [Matrix.mulVec_single_one]
    rfl
  have hh := (PiLp.norm_apply_le (T (EuclideanSpace.single j (1 : ℝ))) i).trans
    (T.le_opNorm (EuclideanSpace.single j 1))
  rw [he, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs] at hh
  rw [bNorm_eq_operatorNorm]
  exact hh

/-- Equation (2) with the paper's actual operator `P^t - Π`, rather than only its
normalized matrix. `Stoch.pow` uses exactly the powers in the definition of `Lk`. -/
theorem bNorm_eq_weightedOperatorNorm [DecidableEq (Fin d)] (S : Stoch d)
    (st : Stationary S) (t : ℕ) :
    bNorm S st t = weightedOperatorNorm st.mu ((S.pow t).P - piMat st.mu) := by
  have hcenter : simil st.mu ((S.pow t).P - piMat st.mu) = LkSub S st t :=
    simil_centered_eq_LkSub S st t
  unfold weightedOperatorNorm
  rw [hcenter]
  exact bNorm_eq_operatorNorm S st t

end PsgEst
