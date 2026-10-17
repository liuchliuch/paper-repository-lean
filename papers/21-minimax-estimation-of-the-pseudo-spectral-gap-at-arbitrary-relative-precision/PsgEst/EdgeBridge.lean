import PsgEst.EdgeProcess

open Matrix BigOperators Real Finset
open scoped InnerProductSpace
namespace PsgEst

/-- Cauchy--Schwarz converts the actual Euclidean operator norm to a quadratic
form bound. No symmetry assumption is needed for this direction. -/
theorem matrixEuclideanNorm_quadratic_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    |x ⬝ᵥ (M *ᵥ x)| ≤ matrixEuclideanNorm M * (x ⬝ᵥ x) := by
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 x
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M
  have hq : |x ⬝ᵥ (M *ᵥ x)| = |inner ℝ v (T v)| := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
    rfl
  calc _ = |inner ℝ v (T v)| := hq
    _ ≤ ‖v‖ * ‖T v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖T‖ * ‖v‖) := mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg _)
    _ = matrixEuclideanNorm M * (x ⬝ᵥ x) := by
      change ‖v‖ * (‖T‖ * ‖v‖) = ‖T‖ * (x ⬝ᵥ x)
      have he : ‖v‖^2 = x⬝ᵥx := euclidean_norm_sq_dot v
      rw [← he]
      ring

/-- Reindexing the bipartite coordinates preserves the quadratic form. -/
theorem edgeFin_quadratic {d : ℕ} (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ)
    (x : Fin d ⊕ Fin d → ℝ) :
    (x ∘ finSumFinEquiv.symm) ⬝ᵥ (edgeFinEquiv d M *ᵥ (x ∘ finSumFinEquiv.symm)) =
      x ⬝ᵥ (M *ᵥ x) := by
  change (x ∘ finSumFinEquiv.symm) ⬝ᵥ
    (M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm *ᵥ (x ∘ finSumFinEquiv.symm)) = _
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_assoc, Equiv.symm_symm, Equiv.symm_comp_self, Function.comp_id]
  exact comp_equiv_dotProduct_comp_equiv x (M*ᵥx) finSumFinEquiv.symm

/-- The norm used by Freedman controls the original bipartite quadratic form. -/
theorem edgeFin_norm_quadratic_le {d : ℕ}
    (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (x : Fin d ⊕ Fin d → ℝ) :
    |x ⬝ᵥ (M*ᵥx)| ≤ matrixEuclideanNorm (edgeFinEquiv d M) * (x⬝ᵥx) := by
  have h := matrixEuclideanNorm_quadratic_le (edgeFinEquiv d M) (x ∘ finSumFinEquiv.symm)
  rw [edgeFin_quadratic, comp_equiv_dotProduct_comp_equiv] at h
  exact h

lemma edgeProcess_rowMean {d : ℕ} (Q : Stoch d) (st : Stationary Q) (τ : ℝ) (i : Fin d) :
    edgeRowMean Q (edgeProcessK Q st τ) i =
      edgeFinEquiv d (edgeProcessA Q st τ * edgeF Q st i * edgeProcessA Q st τ) := by
  rw [← regularizedEdge_rowMean]
  simp only [edgeRowMean, edgeProcessK, map_sum, map_smul]

/-- Exact, multiplicity-preserving sum of the constructed martingale
increments. It is the centered empirical edge Laplacian, conjugated by `A`,
in the coordinate system of matrix Freedman. -/
theorem edgeProcess_sum_eq {d m : ℕ} (Q : Stoch d) (st : Stationary Q) (τ : ℝ)
    (Y : Fin (m+1) → Fin d) (hm : 0 < m) :
    (∑ t : Fin m, edgeProcessZ Q st τ t Y) = edgeFinEquiv d
      (edgeProcessA Q st τ * ((m:ℝ) • empiricalHbar st.mu Y -
        ∑ i, (outDeg Y i:ℝ) • edgeF Q st i) * edgeProcessA Q st τ) := by
  have hbar : (m:ℝ) • empiricalHbar st.mu Y =
      ∑ t : Fin m, edgeOuter st.mu (Y t.castSucc) (Y t.succ) := by
    rw [empiricalHbar_eq_path_average, smul_smul,
      mul_inv_cancel₀ (show (m:ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hm.ne'), one_smul]
  change (∑ t : Fin m, (edgeProcessK Q st τ (Y t.castSucc) (Y t.succ) -
      edgeRowMean Q (edgeProcessK Q st τ) (Y t.castSucc))) = _
  rw [sum_sub_distrib, ← sum_outDeg_smul, hbar]
  simp only [edgeProcess_rowMean, edgeProcessK, regularizedEdge, map_sub, map_sum, map_smul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

end PsgEst
