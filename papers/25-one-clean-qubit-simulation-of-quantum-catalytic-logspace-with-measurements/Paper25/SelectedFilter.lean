import Paper25.TraceApproximation
import Paper25.FilterMatrix
import Paper25.StatePreparation
import Paper25.WalkFilter

/-!
# Actual history selectors inside the dilation filter

The selected ideal block is computed from the proved dilation-filter identity
(17). Its trace is the actual history-selector trace. Operator-norm error on
the full filtered dilation automatically bounds the selected block error.
-/

noncomputable section
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
open Matrix

namespace Paper25
namespace SelectedFilter

section Isometries
variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]

/-- Computational-basis embedding with a specified coordinate map. -/
def basisColumn (f : κ → ι) : Matrix ι κ ℂ :=
  fun p i => if p = f i then 1 else 0

lemma basisColumn_isometry (f : κ → ι) (hf : Function.Injective f) :
    (basisColumn f).conjTranspose * basisColumn f = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [basisColumn, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite,
      Matrix.one_apply, hf.eq_iff]
  · simp [basisColumn, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite,
      Matrix.one_apply, hf.eq_iff, hij, Ne.symm hij]

lemma basisColumn_cross (f : κ → ι) (g : ν → ι) (M : Matrix ι ι ℂ) :
    (basisColumn f).conjTranspose * M * basisColumn g = M.submatrix f g := by
  ext i j
  simp [basisColumn, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite]

/-- The physical block between separately prepared input and output columns. -/
def selectedBlock (F : Matrix ι κ ℂ) (M : Matrix ι ι ℂ) (E : Matrix ι κ ℂ) :
    Matrix κ κ ℂ := F.conjTranspose * M * E

lemma selectedBlock_sub (F E : Matrix ι κ ℂ) (M N : Matrix ι ι ℂ) :
    selectedBlock F (M - N) E = selectedBlock F M E - selectedBlock F N E := by
  simp only [selectedBlock, Matrix.mul_sub, Matrix.sub_mul]

lemma isometry_norm_le_one (E : Matrix ι κ ℂ) (hE : E.conjTranspose * E = 1) :
    ‖E‖ ≤ 1 := by
  exact Paper25.isometry_opNorm_le_one E hE

/-- A two-sided block between normalized preparation columns has no larger
operator norm than its parent matrix. -/
theorem selectedBlock_norm_le (F E : Matrix ι κ ℂ)
    (hF : F.conjTranspose * F = 1) (hE : E.conjTranspose * E = 1)
    (M : Matrix ι ι ℂ) : ‖selectedBlock F M E‖ ≤ ‖M‖ := by
  have hf := isometry_norm_le_one F hF
  have he := isometry_norm_le_one E hE
  unfold selectedBlock
  calc
    _ ≤ (‖F.conjTranspose‖ * ‖M‖) * ‖E‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg E))
    _ = (‖F‖ * ‖M‖) * ‖E‖ := by rw [Matrix.l2_opNorm_conjTranspose]
    _ ≤ (1 * ‖M‖) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hf (norm_nonneg M)) he
        (norm_nonneg E) (by positivity)
    _ = ‖M‖ := by ring

end Isometries

section Dilation
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Coordinate transport of a physical column, without changing its image. -/
def finColumn (E : Matrix ι κ ℂ) : Matrix (Fin (Fintype.card ι)) κ ℂ :=
  E.submatrix (Fintype.equivFin ι).symm id

lemma finColumn_gram (E F : Matrix ι κ ℂ) :
    (finColumn E).conjTranspose * finColumn F = E.conjTranspose * F := by
  simp only [finColumn, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id]

/-- Input selector h=0, in the coordinate system used by the dilation. -/
def dilationInput (E : Matrix ι κ ℂ) :
    Matrix (Fin (Fintype.card ι) ⊕ Fin (Fintype.card ι)) κ ℂ :=
  basisColumn Sum.inl * finColumn E

/-- Output selector h=1, in the coordinate system used by the dilation. -/
def dilationOutput (F : Matrix ι κ ℂ) :
    Matrix (Fin (Fintype.card ι) ⊕ Fin (Fintype.card ι)) κ ℂ :=
  basisColumn Sum.inr * finColumn F

lemma dilationInput_gram (E : Matrix ι κ ℂ) :
    (dilationInput E).conjTranspose * dilationInput E = E.conjTranspose * E := by
  unfold dilationInput
  rw [Matrix.conjTranspose_mul]
  have h := basisColumn_isometry (Sum.inl : Fin (Fintype.card ι) →
    Fin (Fintype.card ι) ⊕ Fin (Fintype.card ι)) Sum.inl_injective
  calc
    _ = (finColumn E).conjTranspose *
        ((basisColumn Sum.inl).conjTranspose * basisColumn Sum.inl) * finColumn E := by
      simp only [Matrix.mul_assoc]
      congr 1
      exact (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [h, Matrix.mul_one, finColumn_gram]

lemma dilationOutput_gram (F : Matrix ι κ ℂ) :
    (dilationOutput F).conjTranspose * dilationOutput F = F.conjTranspose * F := by
  unfold dilationOutput
  rw [Matrix.conjTranspose_mul]
  have h := basisColumn_isometry (Sum.inr : Fin (Fintype.card ι) →
    Fin (Fintype.card ι) ⊕ Fin (Fintype.card ι)) Sum.inr_injective
  calc
    _ = (finColumn F).conjTranspose *
        ((basisColumn Sum.inr).conjTranspose * basisColumn Sum.inr) * finColumn F := by
      simp only [Matrix.mul_assoc]
      congr 1
      exact (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [h, Matrix.mul_one, finColumn_gram]

/-- The actual spectral filter of the scaled history dilation. -/
def idealFilter (A : Matrix ι ι ℂ) (lam : ℝ) :
    Matrix (Fin (Fintype.card ι) ⊕ Fin (Fintype.card ι))
      (Fin (Fintype.card ι) ⊕ Fin (Fintype.card ι)) ℂ :=
  filterMat (((1 / 3 : ℝ) : ℂ) • dilation (Matrix.reindex (Fintype.equivFin ι)
    (Fintype.equivFin ι) A)) (scaled_dilation_isHermitian _) (lam / 3)

/-- Equation (17), including both physical selection columns and finite
coordinate changes. No ideal-block trace identity is assumed. -/
theorem selected_idealFilter (A : Matrix ι ι ℂ) (F E : Matrix ι κ ℂ)
    (lam : ℝ) (hlam : 0 < lam) :
    selectedBlock (dilationOutput F) (idealFilter A lam) (dilationInput E) =
      (lam : ℂ) • selectedBlock F (matrixRegInv A lam) E := by
  let e := Fintype.equivFin ι
  have hreg : bLam (Matrix.reindex e e A) lam =
      (matrixRegInv A lam).submatrix e.symm e.symm := by
    rw [bLam_eq_regInv]
    exact (reindex_matrixRegInv e A lam).symm
  unfold selectedBlock dilationOutput dilationInput
  rw [Matrix.conjTranspose_mul]
  calc
    _ = (finColumn F).conjTranspose *
        ((basisColumn Sum.inr).conjTranspose * idealFilter A lam * basisColumn Sum.inl) *
          finColumn E := by simp only [Matrix.mul_assoc]
    _ = (finColumn F).conjTranspose * ((lam : ℂ) • bLam (Matrix.reindex e e A) lam) *
          finColumn E := by
      rw [basisColumn_cross]
      congr 2
      exact filter_dilation_spectral_block (Matrix.reindex e e A) lam hlam
    _ = (lam : ℂ) • ((finColumn F).conjTranspose * bLam (Matrix.reindex e e A) lam *
          finColumn E) := by simp only [Matrix.mul_smul, Matrix.smul_mul]
    _ = _ := by
      rw [hreg]
      change (lam : ℂ) • (F.conjTranspose.submatrix id e.symm *
        (matrixRegInv A lam).submatrix e.symm e.symm * E.submatrix e.symm id) = _
      rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]

end Dilation

section History

/-- The actual normalized input/output column on clock and Liouville data. -/
def historyColumn {J m n : ℕ} (t : Fin J) (ω : Fin m → ℂ) :
    Matrix (Fin J × (Fin m × Fin n)) (Fin n) ℂ :=
  clockColumn t (kronColId ω)

lemma historyColumn_isometry {J m n : ℕ} (t : Fin J) (ω : Fin m → ℂ)
    (hω : cinner ω ω = 1) :
    (historyColumn (n := n) t ω).conjTranspose * historyColumn (n := n) t ω = 1 := by
  rw [historyColumn, clockColumn_gram, kronColId_conjTranspose_mul, hω, one_smul]

/-- The trace of the actual ideal selected block is λ times the history
selector trace. This is derived from equation (17) and the rectangular trace
cycle, without an ideal-trace hypothesis. -/
theorem history_idealFilter_trace {J m n : ℕ}
    (A : Matrix (Fin J × (Fin m × Fin n)) (Fin J × (Fin m × Fin n)) ℂ)
    (u v : Fin J) (ω z : Fin m → ℂ) (lam : ℝ) (hlam : 0 < lam) :
    Matrix.trace (selectedBlock (dilationOutput (historyColumn v z))
      (idealFilter A lam) (dilationInput (historyColumn u ω))) =
        (lam : ℂ) * Matrix.trace
          (historySelector u v (kronRankOneId (n := n) ω z) * matrixRegInv A lam) := by
  rw [selected_idealFilter A _ _ lam hlam, Matrix.trace_smul]
  congr 1
  unfold selectedBlock
  rw [Matrix.trace_mul_cycle]
  congr 1
  rw [historyColumn, historyColumn, clockColumn_mul_adjoint, ← kronRankOneId_eq_mul]

/-- A full-space filter approximation gives the actual selected history
block approximation, by the proved preparation-column isometries. -/
theorem history_selected_filter_error {J m n : ℕ}
    (A : Matrix (Fin J × (Fin m × Fin n)) (Fin J × (Fin m × Fin n)) ℂ)
    (u v : Fin J) (ω z : Fin m → ℂ)
    (hω : cinner ω ω = 1) (hz : cinner z z = 1)
    (lam eps : ℝ)
    (G : Matrix (Fin (Fintype.card (Fin J × (Fin m × Fin n))) ⊕
      Fin (Fintype.card (Fin J × (Fin m × Fin n))))
      (Fin (Fintype.card (Fin J × (Fin m × Fin n))) ⊕
      Fin (Fintype.card (Fin J × (Fin m × Fin n)))) ℂ)
    (hG : ‖G - idealFilter A lam‖ ≤ eps) :
    ‖selectedBlock (dilationOutput (historyColumn v z)) G
        (dilationInput (historyColumn u ω)) -
      selectedBlock (dilationOutput (historyColumn v z)) (idealFilter A lam)
        (dilationInput (historyColumn u ω))‖ ≤ eps := by
  rw [← selectedBlock_sub]
  apply (selectedBlock_norm_le _ _ ?_ ?_ _).trans hG
  · rw [dilationOutput_gram]
    exact historyColumn_isometry v z hz
  · rw [dilationInput_gram]
    exact historyColumn_isometry u ω hω

/-- Equation (19) with both structural selected-block premises eliminated.
The remaining approximation input is a full-space filter approximation,
which is the output of the coherent phase-estimation construction. -/
theorem eq19_from_full_filter {T J K D : ℕ}
    (S : ℕ → Matrix (Fin (K ^ 2) × Fin (D ^ 2))
      (Fin (K ^ 2) × Fin (D ^ 2)) ℂ)
    (hJ : T + 1 ≤ J) (hD : 0 < D)
    (hchannels : CPTPFrobBound S T (K * D))
    (ω η z : Fin (K ^ 2) → ℂ)
    (hω : cinner ω ω = 1) (hz : cinner z z = 1)
    (hrestore : ExactRestoration (chainProd S 0 T) ω η)
    (lam : ℝ) (hlam : 0 < lam) (eps : ℝ)
    (G : Matrix (Fin (Fintype.card (Fin J × (Fin (K ^ 2) × Fin (D ^ 2)))) ⊕
      Fin (Fintype.card (Fin J × (Fin (K ^ 2) × Fin (D ^ 2)))))
      (Fin (Fintype.card (Fin J × (Fin (K ^ 2) × Fin (D ^ 2)))) ⊕
      Fin (Fintype.card (Fin J × (Fin (K ^ 2) × Fin (D ^ 2))))) ℂ)
    (hG : ‖G - idealFilter (1 - historyShift T J S) lam‖ ≤ eps) :
    |normalizedReTrace (selectedBlock
        (dilationOutput (historyColumn (⟨T, by omega⟩ : Fin J) z)) G
        (dilationInput (historyColumn (⟨0, by omega⟩ : Fin J) ω))) -
      lam * (cinner z η).re| ≤
      (lam ^ 2 / 2) * (J : ℝ) ^ 2 * (K : ℝ) ^ 2 + eps := by
  apply eq19_selected_filter_trace S hJ hD hchannels ω η z hω hz hrestore lam hlam
  · exact history_selected_filter_error _ _ _ ω z hω hz lam eps G hG
  · exact history_idealFilter_trace _ _ _ ω z lam hlam

/-- The source's actual signed acceptance bias, using the explicit clean
input and normalized observable vector, follows from the full filter error. -/
theorem eq19_source_signed_bias {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {T J D : ℕ}
    (S : ℕ → Matrix (Fin ((Fintype.card (SourceBias.Work α)) ^ 2) × Fin (D ^ 2))
      (Fin ((Fintype.card (SourceBias.Work α)) ^ 2) × Fin (D ^ 2)) ℂ)
    (hJ : T + 1 ≤ J) (hD : 0 < D)
    (hchannels : CPTPFrobBound S T (Fintype.card (SourceBias.Work α) * D))
    (w0 : SourceBias.Work α) (η : Matrix (SourceBias.Work α) (SourceBias.Work α) ℂ)
    (hη : η.IsHermitian) (ht : η.trace = 1)
    (hrestore : ExactRestoration (chainProd S 0 T) (SourceBias.historyOmega w0)
      (SourceBias.historyEta η))
    (lam : ℝ) (hlam : 0 < lam) (eps : ℝ)
    (G : Matrix (Fin (Fintype.card (Fin J ×
      (Fin ((Fintype.card (SourceBias.Work α)) ^ 2) × Fin (D ^ 2)))) ⊕
      Fin (Fintype.card (Fin J ×
      (Fin ((Fintype.card (SourceBias.Work α)) ^ 2) × Fin (D ^ 2)))))
      (Fin (Fintype.card (Fin J ×
      (Fin ((Fintype.card (SourceBias.Work α)) ^ 2) × Fin (D ^ 2)))) ⊕
      Fin (Fintype.card (Fin J ×
      (Fin ((Fintype.card (SourceBias.Work α)) ^ 2) × Fin (D ^ 2))))) ℂ)
    (hG : ‖G - idealFilter (1 - historyShift T J S) lam‖ ≤ eps) :
    |normalizedReTrace (selectedBlock
        (dilationOutput (historyColumn (⟨T, by omega⟩ : Fin J) SourceBias.historyZ)) G
        (dilationInput (historyColumn (⟨0, by omega⟩ : Fin J) (SourceBias.historyOmega w0)))) -
      lam * (2 * SourceBias.accept η - 1) / Real.sqrt (Fintype.card (SourceBias.Work α))| ≤
      (lam ^ 2 / 2) * (J : ℝ) ^ 2 * (Fintype.card (SourceBias.Work α) : ℝ) ^ 2 + eps := by
  have h := eq19_from_full_filter S hJ hD hchannels (SourceBias.historyOmega w0)
    (SourceBias.historyEta η) SourceBias.historyZ (SourceBias.historyOmega_normalized w0)
    SourceBias.historyZ_normalized hrestore lam hlam eps G hG
  rw [SourceBias.history_z_eta_bias η hη ht, Complex.div_ofReal_re,
    Complex.ofReal_re] at h
  simpa only [mul_div_assoc] using h

end History

section PhysicalPreparation
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

/-- The actual zero-ancilla basis column, retaining the catalyst data. -/
def zeroColumn (q : σ) : Matrix (σ × κ) κ ℂ :=
  basisColumn (fun j => (q, j))

/-- Preparing a small-register unitary column and leaving the catalyst alone. -/
def preparedColumn (F : Matrix σ σ ℂ) (q : σ) : Matrix (σ × κ) κ ℂ :=
  Matrix.kronecker F (1 : Matrix κ κ ℂ) * zeroColumn q

lemma preparedColumn_apply (F : Matrix σ σ ℂ) (q : σ) (p : σ × κ) (j : κ) :
    preparedColumn F q p j = F p.1 q * (if p.2 = j then 1 else 0) := by
  simp [preparedColumn, zeroColumn, basisColumn, Matrix.mul_apply,
    Matrix.kronecker_apply, Fintype.sum_prod_type, Matrix.one_apply]

/-- The all-zero block of `F† Uf` is exactly the transition between the
prepared output column `F|0⟩` and the actual zero input column. -/
theorem prepared_readout_block (F : Matrix σ σ ℂ) (U : Matrix (σ × κ) (σ × κ) ℂ)
    (q : σ) :
    ((Matrix.kronecker F (1 : Matrix κ κ ℂ)).conjTranspose * U).submatrix
      (fun j => (q, j)) (fun j => (q, j)) =
      selectedBlock (preparedColumn F q) U (zeroColumn q) := by
  unfold selectedBlock preparedColumn zeroColumn
  rw [Matrix.conjTranspose_mul]
  have h : (basisColumn (fun j => (q, j))).conjTranspose *
      ((Matrix.kronecker F (1 : Matrix κ κ ℂ)).conjTranspose * U) *
        basisColumn (fun j => (q, j)) = _ :=
    basisColumn_cross (fun j => (q, j)) (fun j => (q, j)) _
  rw [← h]
  simp only [Matrix.mul_assoc]

/-- The physical F in the paper prepares the exact signed work vector and
retains each specified clock, h-selector, and zero auxiliary coordinate. -/
theorem actual_F_prepared_column (ell s r n : ℕ) (t : StatePreparation.Bits ell)
    (p : StatePreparation.Small ell s r × Fin n) (j : Fin n) :
    preparedColumn (StatePreparation.F ell s r t) (StatePreparation.smallZero ell s r) p j =
      ((if p.1.1 = 1 then 1 else 0) * (if p.1.2.1 = t then 1 else 0) *
        (SourceBias.zVector (α := StatePreparation.Bits s)) p.1.2.2.1 *
          (if p.1.2.2.2 = StatePreparation.zeroBits r then 1 else 0)) *
        (if p.2 = j then 1 else 0) := by
  rw [preparedColumn_apply, StatePreparation.F_column]

end PhysicalPreparation

end SelectedFilter
end Paper25
