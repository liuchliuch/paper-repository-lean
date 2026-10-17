import PsgEst.BipartiteSpectrum

/-!
# Separate normalization for an arbitrary nonnegative real matrix

Section 2's deterministic claim applies to every nonnegative real matrix with
positive row and column sums, without a transition-count or trajectory hypothesis.
The vectors of square roots of the two degree vectors are a singular pair of
singular value one; the normalized matrix is a Euclidean contraction.
-/

open Matrix BigOperators Real

namespace PsgEst.NormalizedMatrix

variable {d : ℕ}

/-- The row degree of an arbitrary real matrix. -/
def rowSum (C : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) : ℝ := ∑ j, C i j

/-- The column degree of an arbitrary real matrix. -/
def colSum (C : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : ℝ := ∑ i, C i j

/-- Separate incoming and outgoing normalization, with no empirical restriction. -/
noncomputable def normalized (C : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  diagonal (fun i => rowSum C i ^ (-(1 / 2 : ℝ))) * C *
    diagonal (fun j => colSum C j ^ (-(1 / 2 : ℝ)))

lemma inverse_half_sq (x : ℝ) (hx : 0 < x) :
    (x ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / x := by
  rw [pow_two, rpow_neg_half_sq x hx, Real.rpow_neg_one, one_div]

lemma normalized_mulVec (C : Matrix (Fin d) (Fin d) ℝ)
    (u : Fin d → ℝ) (i : Fin d) :
    (normalized C *ᵥ u) i = rowSum C i ^ (-(1 / 2 : ℝ)) *
      ∑ j, C i j * (colSum C j ^ (-(1 / 2 : ℝ)) * u j) := by
  have hmul : normalized C *ᵥ u =
      diagonal (fun i => rowSum C i ^ (-(1 / 2 : ℝ))) *ᵥ
        (C *ᵥ (diagonal (fun j => colSum C j ^ (-(1 / 2 : ℝ))) *ᵥ u)) := by
    unfold normalized
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hmul]
  simp only [Matrix.mulVec_diagonal]
  have hmv : ∀ (M : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) (i : Fin d),
      (M *ᵥ w) i = ∑ j, M i j * w j := fun _ _ _ => rfl
  rw [hmv]
  simp only [Matrix.mulVec_diagonal, Finset.mul_sum]

/-- Weighted Cauchy--Schwarz controls each normalized row. -/
theorem row_bound (C : Matrix (Fin d) (Fin d) ℝ)
    (hC : ∀ i j, 0 ≤ C i j)
    (hr : ∀ i, 0 < rowSum C i) (hc : ∀ j, 0 < colSum C j)
    (u : Fin d → ℝ) (i : Fin d) :
    (normalized C *ᵥ u) i ^ 2 ≤ ∑ j, C i j * u j ^ 2 / colSum C j := by
  have hweighted := weighted_cauchy (a := fun j => C i j)
    (v := fun j => colSum C j ^ (-(1 / 2 : ℝ)) * u j) (hC i)
  change (∑ j, C i j * (colSum C j ^ (-(1 / 2 : ℝ)) * u j)) ^ 2 ≤
    rowSum C i * ∑ j, C i j * (colSum C j ^ (-(1 / 2 : ℝ)) * u j) ^ 2 at hweighted
  have hterm (j : Fin d) : (colSum C j ^ (-(1 / 2 : ℝ)) * u j) ^ 2 =
      u j ^ 2 / colSum C j := by
    rw [mul_pow, inverse_half_sq _ (hc j)]
    ring
  rw [normalized_mulVec, mul_pow, inverse_half_sq _ (hr i)]
  calc (1 / rowSum C i) *
      (∑ j, C i j * (colSum C j ^ (-(1 / 2 : ℝ)) * u j)) ^ 2 ≤
      (1 / rowSum C i) * (rowSum C i *
        ∑ j, C i j * (colSum C j ^ (-(1 / 2 : ℝ)) * u j) ^ 2) :=
      mul_le_mul_of_nonneg_left hweighted (div_nonneg (by norm_num) (hr i).le)
    _ = ∑ j, C i j * u j ^ 2 / colSum C j := by
      rw [← mul_assoc, one_div_mul_cancel (ne_of_gt (hr i)), one_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [hterm]
      ring

/-- The separately normalized operator of any nonnegative real matrix is a
Euclidean contraction. -/
theorem contraction (C : Matrix (Fin d) (Fin d) ℝ)
    (hC : ∀ i j, 0 ≤ C i j)
    (hr : ∀ i, 0 < rowSum C i) (hc : ∀ j, 0 < colSum C j)
    (u : Fin d → ℝ) :
    (∑ i, (normalized C *ᵥ u) i ^ 2) ≤ ∑ i, u i ^ 2 := by
  calc (∑ i, (normalized C *ᵥ u) i ^ 2) ≤
      ∑ i, ∑ j, C i j * u j ^ 2 / colSum C j :=
      Finset.sum_le_sum (fun i _ => row_bound C hC hr hc u i)
    _ = ∑ j, u j ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_div, ← Finset.sum_mul]
      change colSum C j * u j ^ 2 / colSum C j = u j ^ 2
      field_simp [ne_of_gt (hc j)]

/-- The incoming square-root degree vector is mapped to the outgoing vector. -/
theorem mul_sqrt_col (C : Matrix (Fin d) (Fin d) ℝ)
    (hr : ∀ i, 0 < rowSum C i) (hc : ∀ j, 0 < colSum C j) :
    normalized C *ᵥ (fun j => colSum C j ^ ((1 : ℝ) / 2)) =
      (fun i => rowSum C i ^ ((1 : ℝ) / 2)) := by
  ext i
  rw [normalized_mulVec]
  have hinner : ∀ j, colSum C j ^ (-(1 / 2 : ℝ)) * colSum C j ^ ((1 : ℝ) / 2) = 1 :=
    fun j => rpow_neg_half_cancel _ (hc j)
  simp_rw [hinner, mul_one]
  exact rpow_neg_half_mul _ (hr i)

@[simp] lemma rowSum_transpose (C : Matrix (Fin d) (Fin d) ℝ) :
    rowSum Cᵀ = colSum C := rfl

@[simp] lemma colSum_transpose (C : Matrix (Fin d) (Fin d) ℝ) :
    colSum Cᵀ = rowSum C := rfl

lemma normalized_transpose (C : Matrix (Fin d) (Fin d) ℝ) :
    normalized Cᵀ = (normalized C)ᵀ := by
  simp only [normalized, Matrix.transpose_mul, Matrix.diagonal_transpose,
    rowSum_transpose, colSum_transpose, Matrix.mul_assoc]

/-- The transpose maps the outgoing square-root vector back to the incoming one. -/
theorem transpose_mul_sqrt_row (C : Matrix (Fin d) (Fin d) ℝ)
    (hr : ∀ i, 0 < rowSum C i) (hc : ∀ j, 0 < colSum C j) :
    (normalized C)ᵀ *ᵥ (fun i => rowSum C i ^ ((1 : ℝ) / 2)) =
      (fun j => colSum C j ^ ((1 : ℝ) / 2)) := by
  rw [← normalized_transpose]
  exact mul_sqrt_col Cᵀ hc hr

/-- The two square-root degree vectors have equal squared Euclidean norms. -/
theorem sqrt_degree_sum_sq (C : Matrix (Fin d) (Fin d) ℝ)
    (hr : ∀ i, 0 < rowSum C i) (hc : ∀ j, 0 < colSum C j) :
    (∑ j, (colSum C j ^ ((1 : ℝ) / 2)) ^ 2) =
      ∑ i, (rowSum C i ^ ((1 : ℝ) / 2)) ^ 2 := by
  have hrow : ∀ i, (rowSum C i ^ ((1 : ℝ) / 2)) ^ 2 = rowSum C i := by
    intro i
    rw [pow_two, rpow_half_sq _ (hr i)]
  have hcol : ∀ j, (colSum C j ^ ((1 : ℝ) / 2)) ^ 2 = colSum C j := by
    intro j
    rw [pow_two, rpow_half_sq _ (hc j)]
  simp_rw [hrow, hcol]
  exact Finset.sum_comm

/-- Equality of the actual Euclidean-space norms, in addition to the sum formula. -/
theorem sqrt_degree_norm (C : Matrix (Fin d) (Fin d) ℝ)
    (hr : ∀ i, 0 < rowSum C i) (hc : ∀ j, 0 < colSum C j) :
    ‖(WithLp.toLp 2 (fun j => colSum C j ^ ((1 : ℝ) / 2)) : EuclideanSpace ℝ (Fin d))‖ =
      ‖(WithLp.toLp 2 (fun i => rowSum C i ^ ((1 : ℝ) / 2)) : EuclideanSpace ℝ (Fin d))‖ := by
  have hs := sqrt_degree_sum_sq C hr hc
  have hn :
      ‖(WithLp.toLp 2 (fun j => colSum C j ^ ((1 : ℝ) / 2)) : EuclideanSpace ℝ (Fin d))‖ ^ 2 =
      ‖(WithLp.toLp 2 (fun i => rowSum C i ^ ((1 : ℝ) / 2)) : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
    simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using hs
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun j => colSum C j ^ ((1 : ℝ) / 2)) : EuclideanSpace ℝ (Fin d)),
    norm_nonneg (WithLp.toLp 2 (fun i => rowSum C i ^ ((1 : ℝ) / 2)) : EuclideanSpace ℝ (Fin d))]

/-- For a nonempty index type, the actual largest sorted Gram eigenvalue is one.
This is the squared top singular value, rather than a surrogate deficit. -/
theorem gram_top_one (hd : 0 < d) (C : Matrix (Fin d) (Fin d) ℝ)
    (hC : ∀ i j, 0 ≤ C i j)
    (hr : ∀ i, 0 < rowSum C i) (hc : ∀ j, 0 < colSum C j) :
    gramEig₀ (normalized C) ⟨0, by simpa using hd⟩ = 1 := by
  apply gram_top_one_of_singular_pair hd (normalized C) (contraction C hC hr hc)
    (fun i => rowSum C i ^ ((1 : ℝ) / 2)) (fun j => colSum C j ^ ((1 : ℝ) / 2))
  · intro hv
    have hh := congrFun hv ⟨0, hd⟩
    have hp : 0 < colSum C ⟨0, hd⟩ ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (hc _) _
    exact (ne_of_gt hp) hh
  · exact mul_sqrt_col C hr hc
  · exact transpose_mul_sqrt_row C hr hc

end PsgEst.NormalizedMatrix
