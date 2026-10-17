import PsgEst.EdgeConditional
import PsgEst.EdgeMatrix
import PsgEst.LaplacianCounts

open Matrix BigOperators Real Finset
open scoped InnerProductSpace
namespace PsgEst

/-- Conditional unregularized edge mean `F_i`. -/
noncomputable def edgeF {d : ℕ} (Q : Stoch d) (st : Stationary Q) (i : Fin d) :=
  edgeRowMean Q (edgeOuter st.mu) i

/-- Population edge Laplacian, with the actual stationary edge weights. -/
noncomputable def stationaryEdgeH {d : ℕ} (Q : Stoch d) (st : Stationary Q) :=
  ∑ i, st.mu i • edgeF Q st i

/-- Regularized positive edge observation `A v_ij v_ijᵀ A`. -/
noncomputable def regularizedEdge {d : ℕ} (stmu : Fin d → ℝ)
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (i j : Fin d) :=
  A * edgeOuter stmu i j * A

lemma edgeF_posSemidef {d : ℕ} (Q : Stoch d) (st : Stationary Q) (i : Fin d) :
    (edgeF Q st i).PosSemidef := by
  exact posSemidef_sum _ (fun j => (edgeOuter_posSemidef st.mu i j).smul (Q.nonneg i j))

lemma stationaryEdgeH_posSemidef {d : ℕ} (Q : Stoch d) (st : Stationary Q) :
    (stationaryEdgeH Q st).PosSemidef :=
  posSemidef_sum _ (fun i => (edgeF_posSemidef Q st i).smul (st.nonneg i))

lemma regularizedEdge_posSemidef {d : ℕ} (mu : Fin d → ℝ)
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (hA : A.IsHermitian) (i j : Fin d) :
    (regularizedEdge mu A i j).PosSemidef := by
  simpa only [hA.eq] using (edgeOuter_posSemidef mu i j).conjTranspose_mul_mul_same A

lemma regularizedEdge_rowMean {d : ℕ} (Q : Stoch d) (st : Stationary Q)
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (i : Fin d) :
    edgeRowMean Q (regularizedEdge st.mu A) i = A * edgeF Q st i * A := by
  simp only [edgeRowMean, edgeF, regularizedEdge, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]

lemma regularizedEdge_stationaryMean {d : ℕ} (Q : Stoch d) (st : Stationary Q)
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) :
    (∑ i, st.mu i • edgeRowMean Q (regularizedEdge st.mu A) i) = A * stationaryEdgeH Q st * A := by
  simp only [stationaryEdgeH, regularizedEdge_rowMean, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]

/-- Squared length of the exact stationary-normalized edge vector. -/
lemma edgeVector_sq_length {d : ℕ} (mu : Fin d → ℝ) (hmu : ∀ i, 0 < mu i) (i j : Fin d) :
    edgeVector mu i j ⬝ᵥ edgeVector mu i j = (mu i)⁻¹ + (mu j)⁻¹ := by
  simp only [edgeVector, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  simp only [Pi.single_apply, mul_ite, ite_mul, mul_zero, zero_mul, mul_one, one_mul,
    neg_mul_neg, sum_ite_eq', mem_univ, if_true]
  rw [← mul_inv, ← mul_inv, Real.mul_self_sqrt (hmu i).le, Real.mul_self_sqrt (hmu j).le]

lemma edgeVector_sq_length_le {d : ℕ} (mu : Fin d → ℝ) (hmu : ∀ i, 0 < mu i)
    (p : ℝ) (hp : 0 < p) (hpmin : ∀ i, p ≤ mu i) (i j : Fin d) :
    edgeVector mu i j ⬝ᵥ edgeVector mu i j ≤ 2/p := by
  rw [edgeVector_sq_length mu hmu]
  have hi := one_div_le_one_div_of_le hp (hpmin i)
  have hj := one_div_le_one_div_of_le hp (hpmin j)
  simp only [one_div] at hi hj
  simp only [div_eq_mul_inv]
  linarith

/-- Conjugation of a rank-one edge matrix transforms its vector. -/
lemma regularizedEdge_eq_outer {d : ℕ} (mu : Fin d → ℝ)
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (hA : A.IsHermitian) (i j : Fin d) :
    regularizedEdge mu A i j = vecMulVec (A *ᵥ edgeVector mu i j) (A *ᵥ edgeVector mu i j) := by
  unfold regularizedEdge edgeOuter
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  have ht : Aᵀ = A := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  rw [← ht, Matrix.vecMul_transpose, ht]

/-- The sharp edge-length bound after regularization. -/
lemma regularized_edge_length_le {d : ℕ} (mu : Fin d → ℝ) (hmu : ∀ i, 0 < mu i)
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (p τ : ℝ)
    (hp : 0 < p) (hτ : 0 < τ) (hpmin : ∀ i, p ≤ mu i)
    (henergy : ∀ x, τ*((A*ᵥx)⬝ᵥ(A*ᵥx)) ≤ x⬝ᵥx) (i j : Fin d) :
    (A*ᵥedgeVector mu i j)⬝ᵥ(A*ᵥedgeVector mu i j) ≤ 2/(p*τ) := by
  have h := (henergy (edgeVector mu i j)).trans (edgeVector_sq_length_le mu hmu p hp hpmin i j)
  apply (le_div_iff₀ (mul_pos hp hτ)).mpr
  have hp' := mul_le_mul_of_nonneg_left h hp.le
  have heq : p*(2/p) = 2 := by field_simp
  rw [heq] at hp'
  nlinarith

/-- Both the edge observation and its square have their required PSD bounds. -/
theorem regularizedEdge_bounds {d : ℕ} (mu : Fin d → ℝ) (hmu : ∀ i, 0 < mu i)
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) (hA : A.IsHermitian) (p τ : ℝ)
    (hp : 0 < p) (hτ : 0 < τ) (hpmin : ∀ i, p ≤ mu i)
    (henergy : ∀ x, τ*((A*ᵥx)⬝ᵥ(A*ᵥx)) ≤ x⬝ᵥx) (i j : Fin d) :
    ((2/(p*τ)) • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) - regularizedEdge mu A i j).PosSemidef ∧
    ((2/(p*τ)) • regularizedEdge mu A i j - regularizedEdge mu A i j * regularizedEdge mu A i j).PosSemidef := by
  let v := A*ᵥedgeVector mu i j
  have hc : v⬝ᵥv ≤ 2/(p*τ) := regularized_edge_length_le mu hmu A p τ hp hτ hpmin henergy i j
  have hW := regularizedEdge_posSemidef mu A hA i j
  have houter : regularizedEdge mu A i j = vecMulVec v v := regularizedEdge_eq_outer mu A hA i j
  constructor
  · refine ⟨(Matrix.PosSemidef.one.smul (show 0 ≤ 2/(p*τ) by positivity)).isHermitian.sub hW.isHermitian, ?_⟩
    intro x
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    rw [houter, Matrix.vecMulVec_mulVec, dotProduct_smul]
    simp only [op_smul_eq_mul]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ v x
    have hxx : 0 ≤ x⬝ᵥx := by unfold dotProduct; exact sum_nonneg (fun a _ => mul_self_nonneg _)
    have hmul := mul_le_mul_of_nonneg_right hc hxx
    rw [dotProduct_comm x v]
    simp only [dotProduct, pow_two] at *
    nlinarith only [hcs, hmul]
  · have hidentity : regularizedEdge mu A i j * regularizedEdge mu A i j = (v⬝ᵥv) • regularizedEdge mu A i j := by
      rw [houter, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
    rw [hidentity, ← sub_smul]
    exact hW.smul (sub_nonneg.mpr hc)

end PsgEst
