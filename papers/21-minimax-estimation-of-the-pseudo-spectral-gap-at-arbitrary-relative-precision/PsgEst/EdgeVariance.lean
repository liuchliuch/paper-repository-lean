import PsgEst.EdgeConditional
import PsgEst.EdgeMatrix

open Matrix BigOperators Real Finset
namespace PsgEst

attribute [local instance] Classical.propDecidable

lemma edgeRowMean_posSemidef {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Stoch d) (K : Fin d → Fin d → Matrix ι ι ℝ)
    (hK : ∀ i j, (K i j).PosSemidef) (i : Fin d) : (edgeRowMean Q K i).PosSemidef :=
  posSemidef_sum _ (fun j => (hK i j).smul (Q.nonneg i j))

lemma edgeRowMean_upper {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Stoch d) (K : Fin d → Fin d → Matrix ι ι ℝ) (R : ℝ)
    (hK : ∀ i j, (R • (1 : Matrix ι ι ℝ) - K i j).PosSemidef) (i : Fin d) :
    (R • (1 : Matrix ι ι ℝ) - edgeRowMean Q K i).PosSemidef := by
  have heq : R • (1 : Matrix ι ι ℝ) - edgeRowMean Q K i =
      ∑ j, Q.P i j • (R • (1 : Matrix ι ι ℝ) - K i j) := by
    simp only [smul_sub, sum_sub_distrib, ← sum_smul, Q.row_stoch, one_smul, edgeRowMean]
  rw [heq]
  exact posSemidef_sum _ (fun j => (hK i j).smul (Q.nonneg i j))

/-- The conditional second moment of the centered transition matrix. -/
noncomputable def edgeRowVariance {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Stoch d) (K : Fin d → Fin d → Matrix ι ι ℝ) (i : Fin d) : Matrix ι ι ℝ :=
  ∑ j, Q.P i j • (centeredEdge Q K i j * centeredEdge Q K i j)

/-- The exact conditional covariance identity `E[Z²]=E[W²]-M²`. -/
theorem edgeRowVariance_identity {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Stoch d) (K : Fin d → Fin d → Matrix ι ι ℝ) (i : Fin d) :
    edgeRowVariance Q K i = (∑ j, Q.P i j • (K i j * K i j)) -
      edgeRowMean Q K i * edgeRowMean Q K i := by
  let M := edgeRowMean Q K i
  have hr : (∑ j, Q.P i j • (K i j * M)) = M*M := by
    calc _ = (∑ j, Q.P i j • K i j)*M := by simp only [Matrix.sum_mul, Matrix.smul_mul]
      _ = _ := rfl
  have hl : (∑ j, Q.P i j • (M * K i j)) = M*M := by
    calc _ = M*(∑ j, Q.P i j • K i j) := by simp only [Matrix.mul_sum, Matrix.mul_smul]
      _ = _ := rfl
  have hc : (∑ j, Q.P i j • (M*M)) = M*M := by rw [← sum_smul, Q.row_stoch, one_smul]
  change (∑ j, Q.P i j • ((K i j - M)*(K i j - M))) = _
  simp only [sub_mul, mul_sub, smul_sub, sum_sub_distrib]
  rw [hr, hl, hc]
  change _ = _ - M*M
  abel

lemma edgeRowVariance_posSemidef {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Stoch d) (K : Fin d → Fin d → Matrix ι ι ℝ)
    (hK : ∀ i j, (K i j).IsHermitian) (i : Fin d) : (edgeRowVariance Q K i).PosSemidef :=
  posSemidef_sum _ (fun j => (hermitian_square_posSemidef _
    (centeredEdge_isHermitian Q K hK i j)).smul (Q.nonneg i j))

/-- Matrix variance is bounded by `R M` from the actual rank-one square bound. -/
theorem edgeRowVariance_upper {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Stoch d) (K : Fin d → Fin d → Matrix ι ι ℝ) (R : ℝ)
    (hK : ∀ i j, (K i j).IsHermitian)
    (hsq : ∀ i j, (R • K i j - K i j * K i j).PosSemidef) (i : Fin d) :
    (R • edgeRowMean Q K i - edgeRowVariance Q K i).PosSemidef := by
  have hp := posSemidef_sum _ (fun j => (hsq i j).smul (Q.nonneg i j))
  have hm := hermitian_square_posSemidef _ (edgeRowMean_isHermitian Q K hK i)
  have heq : R • edgeRowMean Q K i - edgeRowVariance Q K i =
      (∑ j, Q.P i j • (R • K i j - K i j * K i j)) +
        edgeRowMean Q K i * edgeRowMean Q K i := by
    rw [edgeRowVariance_identity]
    simp only [smul_sub, sum_sub_distrib, smul_comm (Q.P i _) R, ← smul_sum, edgeRowMean]
    abel
  rw [heq]
  exact hp.add hm

/-- On a prefix atom an arbitrary matrix edge observation has its actual
transition-row mean. The factor is zero on zero-mass atoms and one otherwise. -/
theorem pathMatrixCondExp_edge {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (K : Fin d → Fin d → Matrix (Fin D) (Fin D) ℝ) (t : Fin m)
    (Y : Fin (m+1) → Fin d) :
    pathMatrixCondExp Q mu t.val (fun W => K (W t.castSucc) (W t.succ)) Y =
      ((eventProb Q.P mu (samePrefix t.val Y))⁻¹ * eventProb Q.P mu (samePrefix t.val Y)) •
        edgeRowMean Q K (Y t.castSucc) := by
  classical
  have hc := edgeIncrement_atom_sum_zero Q mu K t Y
  have hm : ∑ W ∈ univ.filter (samePrefix t.val Y), pathProb Q.P mu W • edgeRowMean Q K (W t.castSucc) =
      eventProb Q.P mu (samePrefix t.val Y) • edgeRowMean Q K (Y t.castSucc) := by
    unfold eventProb pathMeasure
    rw [sum_smul]
    apply sum_congr rfl
    intro W hW
    have h := (mem_filter.mp hW).2 t.castSucc (by simp)
    rw [h]
  have hs : (∑ W ∈ univ.filter (samePrefix t.val Y),
      pathProb Q.P mu W • K (W t.castSucc) (W t.succ)) =
      eventProb Q.P mu (samePrefix t.val Y) • edgeRowMean Q K (Y t.castSucc) := by
    simpa only [edgeIncrement, centeredEdge, smul_sub, sum_sub_distrib, hm, sub_eq_zero] using hc
  unfold pathMatrixCondExp
  rw [hs, smul_smul]

/-- Conditional second moments are dominated by the transition-row variance,
including on null prefix atoms. -/
theorem edge_conditional_variance_upper {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (K : Fin d → Fin d → Matrix (Fin D) (Fin D) ℝ)
    (hK : ∀ i j, (K i j).IsHermitian) (t : Fin m) (Y : Fin (m+1) → Fin d) :
    (edgeRowVariance Q K (Y t.castSucc) -
      pathMatrixCondExp Q mu t.val (fun W => edgeIncrement Q K t W * edgeIncrement Q K t W) Y).PosSemidef ∧
    (pathMatrixCondExp Q mu t.val (fun W => edgeIncrement Q K t W * edgeIncrement Q K t W) Y).PosSemidef := by
  have heq := pathMatrixCondExp_edge Q mu (fun i j => centeredEdge Q K i j * centeredEdge Q K i j) t Y
  change pathMatrixCondExp Q mu t.val (fun W => edgeIncrement Q K t W * edgeIncrement Q K t W) Y =
    _ • edgeRowVariance Q K (Y t.castSucc) at heq
  rw [heq]
  have hp := edgeRowVariance_posSemidef Q K hK (Y t.castSucc)
  by_cases hz : eventProb Q.P mu (samePrefix t.val Y) = 0
  · simp only [hz, _root_.inv_zero, mul_zero, zero_smul, sub_zero]
    exact ⟨hp, Matrix.PosSemidef.zero⟩
  · rw [inv_mul_cancel₀ hz, one_smul, sub_self]
    exact ⟨Matrix.PosSemidef.zero, hp⟩

lemma sum_outDeg_smul {d m : ℕ} {ι : Type*} [Fintype ι]
    (M : Fin d → Matrix ι ι ℝ) (Y : Fin (m+1) → Fin d) :
    (∑ i, (outDeg Y i:ℝ) • M i) = ∑ t : Fin m, M (Y t.castSucc) := by
  classical
  simp_rw [outDeg_eq_stateSum Y, stateSum, observationIndex, Bool.false_eq_true,
    if_false, stateIndicator, sum_smul]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  simp [ite_smul, eq_comm]

lemma posSemidef_sub_trans {ι : Type*} [Fintype ι]
    {A B C : Matrix ι ι ℝ} (hAB : (B-A).PosSemidef) (hBC : (C-B).PosSemidef) :
    (C-A).PosSemidef := by
  have h := hBC.add hAB
  convert h using 1 <;> abel

noncomputable def edgePredictableVariation {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (K : Fin d → Fin d → Matrix (Fin D) (Fin D) ℝ)
    (Y : Fin (m+1) → Fin d) : Matrix (Fin D) (Fin D) ℝ :=
  ∑ t : Fin m, pathMatrixCondExp Q mu t.val
    (fun W => edgeIncrement Q K t W * edgeIncrement Q K t W) Y

/-- The first inequality in (17), derived from the true conditional second
moments of the centered edge process. -/
theorem edgePredictableVariation_le_counts {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (K : Fin d → Fin d → Matrix (Fin D) (Fin D) ℝ) (R : ℝ)
    (hK : ∀ i j, (K i j).IsHermitian)
    (hsq : ∀ i j, (R • K i j - K i j * K i j).PosSemidef)
    (Y : Fin (m+1) → Fin d) :
    (R • (∑ i, (outDeg Y i:ℝ) • edgeRowMean Q K i) - edgePredictableVariation Q mu K Y).PosSemidef ∧
    (edgePredictableVariation Q mu K Y).PosSemidef := by
  have hstep (t : Fin m) :
      (R • edgeRowMean Q K (Y t.castSucc) - pathMatrixCondExp Q mu t.val
        (fun W => edgeIncrement Q K t W * edgeIncrement Q K t W) Y).PosSemidef :=
    posSemidef_sub_trans (edge_conditional_variance_upper Q mu K hK t Y).1
      (edgeRowVariance_upper Q K R hK hsq (Y t.castSucc))
  constructor
  · rw [sum_outDeg_smul]
    unfold edgePredictableVariation
    rw [smul_sum, ← sum_sub_distrib]
    exact posSemidef_sum _ hstep
  · exact posSemidef_sum _ (fun t => (edge_conditional_variance_upper Q mu K hK t Y).2)

/-- The full predictable-variation bound (17), using the degree event and the
regularized population contraction. -/
theorem edgePredictableVariation_degree_bound {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (K : Fin d → Fin d → Matrix (Fin D) (Fin D) ℝ) (pi : Fin d → ℝ)
    (R η : ℝ) (hR : 0 ≤ R) (hη : 0 ≤ η)
    (hK : ∀ i j, (K i j).PosSemidef)
    (hsq : ∀ i j, (R • K i j - K i j * K i j).PosSemidef)
    (hpop : ((1 : Matrix (Fin D) (Fin D) ℝ) - ∑ i, pi i • edgeRowMean Q K i).PosSemidef)
    (Y : Fin (m+1) → Fin d) (hE : degreeEvent pi η Y) :
    ((R*(m:ℝ)*(1+η)) • (1 : Matrix (Fin D) (Fin D) ℝ) - edgePredictableVariation Q mu K Y).PosSemidef ∧
    (edgePredictableVariation Q mu K Y).PosSemidef := by
  have hc := edgePredictableVariation_le_counts Q mu K R (fun i j => (hK i j).isHermitian) hsq Y
  have hdeg (i : Fin d) : (outDeg Y i:ℝ) ≤ (m:ℝ)*(1+η)*pi i := by
    have h := (abs_le.mp (hE false i)).2
    rw [← outDeg_eq_stateSum Y i] at h
    nlinarith
  have hm (i : Fin d) := edgeRowMean_posSemidef Q K hK i
  have hb : ((R*(m:ℝ)*(1+η)) • (∑ i, pi i • edgeRowMean Q K i) -
      R • (∑ i, (outDeg Y i:ℝ) • edgeRowMean Q K i)).PosSemidef := by
    have h := posSemidef_sum _ (fun i => (hm i).smul
      (mul_nonneg hR (sub_nonneg.mpr (hdeg i))))
    convert h using 1
    ext a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      mul_sum]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  have hpop' := hpop.smul (show 0 ≤ R*(m:ℝ)*(1+η) by positivity)
  have hlast : ((R*(m:ℝ)*(1+η)) • (1 : Matrix (Fin D) (Fin D) ℝ) -
      (R*(m:ℝ)*(1+η)) • (∑ i, pi i • edgeRowMean Q K i)).PosSemidef := by
    simpa only [smul_sub] using hpop'
  exact ⟨posSemidef_sub_trans (posSemidef_sub_trans hc.1 hb) hlast, hc.2⟩

/-- The norm version of (17) required by the joint-event Freedman theorem. -/
theorem predictableVariationNorm_degree_bound {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (K : Fin d → Fin d → Matrix (Fin D) (Fin D) ℝ) (pi : Fin d → ℝ)
    (R η : ℝ) (hR : 0 ≤ R) (hη : 0 ≤ η)
    (hK : ∀ i j, (K i j).PosSemidef)
    (hsq : ∀ i j, (R • K i j - K i j * K i j).PosSemidef)
    (hpop : ((1 : Matrix (Fin D) (Fin D) ℝ) - ∑ i, pi i • edgeRowMean Q K i).PosSemidef)
    (Y : Fin (m+1) → Fin d) (hE : degreeEvent pi η Y) :
    predictableVariationNorm Q mu (edgeIncrement Q K) Y ≤ R*(m:ℝ)*(1+η) := by
  have h := edgePredictableVariation_degree_bound Q mu K pi R η hR hη hK hsq hpop Y hE
  exact matrixEuclideanNorm_le_of_psd_bounds _ _ (by positivity) h.2 h.1

end PsgEst
