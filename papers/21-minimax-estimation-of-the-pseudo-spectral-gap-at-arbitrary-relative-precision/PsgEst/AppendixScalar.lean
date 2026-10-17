import PsgEst.EdgeBridge

/-! The single-residue occupation estimate in Appendix A. The scalar process
is embedded into actual one-by-one Hermitian matrices so that the only
external input is the original `MatrixFreedmanInput`. -/

open Matrix BigOperators Real Finset
namespace PsgEst

attribute [local instance] Classical.propDecidable

/-- All observations in a residue, including its first observation. -/
noncomputable def appendixVisitCount {d m : ℕ} (i : Fin d)
    (Y : Fin (m+1) → Fin d) : ℝ := ∑ t, stateIndicator i (Y t)

/-- The actual scalar as a one-by-one matrix. -/
noncomputable def appendixScalarMatrix (c : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := c • 1

@[simp] theorem appendixScalarMatrix_apply (c : ℝ) (a b : Fin 1) :
    appendixScalarMatrix c a b = c := by
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst a; subst b
  simp [appendixScalarMatrix]

theorem appendixScalarMatrix_isHermitian (c : ℝ) : (appendixScalarMatrix c).IsHermitian := by
  ext a b
  simp [Matrix.conjTranspose]

theorem appendixScalarMatrix_posSemidef {c : ℝ} (hc : 0 ≤ c) :
    (appendixScalarMatrix c).PosSemidef := Matrix.PosSemidef.one.smul hc

@[simp] theorem appendixScalarMatrix_sub (c e : ℝ) :
    appendixScalarMatrix c - appendixScalarMatrix e = appendixScalarMatrix (c-e) := by
  simp only [appendixScalarMatrix, sub_smul]

@[simp] theorem appendixScalarMatrix_mul (c e : ℝ) :
    appendixScalarMatrix c * appendixScalarMatrix e = appendixScalarMatrix (c*e) := by
  simp only [appendixScalarMatrix, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    smul_smul, mul_comm]

/-- The one-dimensional matrix norm really controls the absolute scalar. -/
theorem appendixScalarMatrix_abs_le_norm (c : ℝ) :
    |c| ≤ euclideanMatrixNorm (appendixScalarMatrix c) := by
  have h := matrixEuclideanNorm_quadratic_le (appendixScalarMatrix c)
    (fun _ : Fin 1 => (1:ℝ))
  simpa [dotProduct, Matrix.mulVec, matrixEuclideanNorm, euclideanMatrixNorm] using h

/-- The uncentered next-state indicator. -/
noncomputable def appendixIndicatorK {d : ℕ} (i : Fin d) (_a b : Fin d) :
    Matrix (Fin 1) (Fin 1) ℝ := appendixScalarMatrix (stateIndicator i b)

/-- The actual indicator minus its transition-row mean at each transition. -/
noncomputable def appendixIndicatorZ {d m : ℕ} (Q : Stoch d) (i : Fin d) :=
  edgeIncrement (m := m) Q (appendixIndicatorK i)

lemma appendixIndicatorK_posSemidef {d : ℕ} (i a b : Fin d) :
    (appendixIndicatorK i a b).PosSemidef := by
  apply appendixScalarMatrix_posSemidef
  unfold stateIndicator
  split_ifs <;> norm_num

lemma appendixIndicatorK_upper {d : ℕ} (i a b : Fin d) :
    ((1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) - appendixIndicatorK i a b).PosSemidef := by
  change (appendixScalarMatrix 1 - appendixScalarMatrix (stateIndicator i b)).PosSemidef
  rw [appendixScalarMatrix_sub]
  apply appendixScalarMatrix_posSemidef
  unfold stateIndicator
  split_ifs <;> norm_num

lemma appendixIndicatorK_square {d : ℕ} (i a b : Fin d) :
    ((1 : ℝ) • appendixIndicatorK i a b - appendixIndicatorK i a b * appendixIndicatorK i a b).PosSemidef := by
  have he : appendixIndicatorK i a b * appendixIndicatorK i a b = appendixIndicatorK i a b := by
    unfold appendixIndicatorK
    rw [appendixScalarMatrix_mul]
    unfold stateIndicator
    split_ifs <;> norm_num
  rw [one_smul, he, sub_self]
  exact Matrix.PosSemidef.zero

lemma appendixIndicator_rowMean {d : ℕ} (Q : Stoch d) (i a : Fin d) :
    edgeRowMean Q (appendixIndicatorK i) a = appendixScalarMatrix (Q.P a i) := by
  ext u v
  simp [edgeRowMean, appendixIndicatorK, Matrix.sum_apply, Matrix.smul_apply,
    stateIndicator, mul_ite]

lemma appendixIndicator_increment {d m : ℕ} (Q : Stoch d) (i : Fin d)
    (t : Fin m) (Y : Fin (m+1) → Fin d) :
    appendixIndicatorZ Q i t Y =
      appendixScalarMatrix (stateIndicator i (Y t.succ) - Q.P (Y t.castSucc) i) := by
  unfold appendixIndicatorZ edgeIncrement centeredEdge
  rw [appendixIndicator_rowMean]
  exact appendixScalarMatrix_sub _ _

lemma appendixIndicator_increment_norm {d m : ℕ} (Q : Stoch d) (i : Fin d)
    (t : Fin m) (Y : Fin (m+1) → Fin d) :
    euclideanMatrixNorm (appendixIndicatorZ Q i t Y) ≤ 1 := by
  have hM := edgeRowMean_posSemidef Q (appendixIndicatorK i)
    (appendixIndicatorK_posSemidef i)
  have hMu := edgeRowMean_upper Q (appendixIndicatorK i) 1 (appendixIndicatorK_upper i)
  exact matrixEuclideanNorm_sub_le_of_psd_bounds _ _ 1 (by norm_num)
    (appendixIndicatorK_posSemidef i _ _) (hM _) (appendixIndicatorK_upper i _ _) (hMu _)

/-- Freedman's hypotheses are verified for the actual indicator differences. -/
theorem appendixIndicator_freedman {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ a, 0 ≤ mu a) (hsum : ∑ a, mu a = 1) (i : Fin d)
    (hinput : MatrixFreedmanInput Q mu) :
    FreedmanJointInput Q mu 1 1 (martingaleSumNorm (appendixIndicatorZ (m := m) Q i))
      (predictableVariationNorm Q mu (appendixIndicatorZ (m := m) Q i)) := by
  exact matrixFreedman_joint Q mu hinput 1 (appendixIndicatorZ Q i) hmu hsum
    (by norm_num)
    (edgeIncrement_isHermitian Q _ (fun a b => (appendixIndicatorK_posSemidef i a b).isHermitian))
    (edgeIncrement_adapted Q _) (edgeIncrement_centered Q mu _)
    (appendixIndicator_increment_norm Q i)

/-- The sum is the actual arrival count minus its actual conditional means. -/
theorem appendixIndicator_sum {d m : ℕ} (Q : Stoch d) (i : Fin d)
    (Y : Fin (m+1) → Fin d) :
    (∑ t : Fin m, appendixIndicatorZ Q i t Y) =
      appendixScalarMatrix (∑ t : Fin m,
        (stateIndicator i (Y t.succ) - Q.P (Y t.castSucc) i)) := by
  ext a b
  simp only [Matrix.sum_apply, appendixIndicator_increment, appendixScalarMatrix_apply]

/-- The first indicator is set aside exactly once. -/
theorem appendixVisitCount_decomposition {d m : ℕ} (Q : Stoch d) (i : Fin d)
    (Y : Fin (m+1) → Fin d) (p : ℝ) :
    appendixVisitCount i Y - (m+1 : ℕ)*p =
      (∑ t : Fin m, (stateIndicator i (Y t.succ) - Q.P (Y t.castSucc) i)) +
      (stateIndicator i (Y 0) - p) + ∑ t : Fin m, (Q.P (Y t.castSucc) i - p) := by
  rw [appendixVisitCount, Fin.sum_univ_succ, sum_sub_distrib, sum_sub_distrib]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- Entrywise relative closeness implies the absolute conditional-mean bound. -/
lemma appendix_entry_absolute {d : ℕ} (Q : Stoch d) (st : Stationary Q)
    (η : ℝ) (hentry : ∀ a b, |Q.P a b / st.mu b - 1| ≤ η/4) (a i : Fin d) :
    |Q.P a i - st.mu i| ≤ η/4 * st.mu i := by
  have he : (Q.P a i / st.mu i - 1) * st.mu i = Q.P a i - st.mu i := by
    field_simp [(st.pos i).ne']
  calc
    _ = |(Q.P a i / st.mu i - 1) * st.mu i| := congrArg abs he.symm
    _ = |Q.P a i / st.mu i - 1| * st.mu i := by rw [abs_mul, abs_of_pos (st.pos i)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hentry a i) (st.nonneg i)

/-- Predictable variation bound proved from the actual conditional second
moments, including zero-mass prefix atoms. -/
theorem appendixIndicator_variation {d m : ℕ} (Q : Stoch d) (st : Stationary Q)
    (mu : Fin d → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hentry : ∀ a b, |Q.P a b / st.mu b - 1| ≤ η/4)
    (i : Fin d) (Y : Fin (m+1) → Fin d) :
    predictableVariationNorm Q mu (appendixIndicatorZ Q i) Y ≤
      (1+η/4)*(m+1 : ℕ)*st.mu i := by
  let B := (1+η/4)*st.mu i
  have hB : 0 ≤ B := mul_nonneg (by linarith) (st.nonneg i)
  have hrow (a : Fin d) :
      (B • (1 : Matrix (Fin 1) (Fin 1) ℝ) - edgeRowMean Q (appendixIndicatorK i) a).PosSemidef := by
    rw [appendixIndicator_rowMean]
    change (appendixScalarMatrix B - appendixScalarMatrix (Q.P a i)).PosSemidef
    rw [appendixScalarMatrix_sub]
    apply appendixScalarMatrix_posSemidef
    have h := (abs_le.mp (appendix_entry_absolute Q st η hentry a i)).2
    dsimp [B]
    linarith
  have hcond (t : Fin m) :
      (B • (1 : Matrix (Fin 1) (Fin 1) ℝ) - pathMatrixCondExp Q mu t.val
        (fun W => appendixIndicatorZ Q i t W * appendixIndicatorZ Q i t W) Y).PosSemidef := by
    exact posSemidef_sub_trans (edge_conditional_variance_upper Q mu (appendixIndicatorK i)
      (fun a b => (appendixIndicatorK_posSemidef i a b).isHermitian) t Y).1
      (posSemidef_sub_trans
        (edgeRowVariance_upper Q (appendixIndicatorK i) 1
          (fun a b => (appendixIndicatorK_posSemidef i a b).isHermitian)
          (appendixIndicatorK_square i) (Y t.castSucc))
        (by simpa only [one_smul] using hrow (Y t.castSucc)))
  have hupper := posSemidef_sum _ hcond
  have hpsum := posSemidef_sum _ (fun t =>
    (edge_conditional_variance_upper Q mu (appendixIndicatorK i)
      (fun a b => (appendixIndicatorK_posSemidef i a b).isHermitian) t Y).2)
  have hupper' : (((m:ℝ)*B) • (1 : Matrix (Fin 1) (Fin 1) ℝ) -
      edgePredictableVariation Q mu (appendixIndicatorK i) Y).PosSemidef := by
    have hs : (∑ _ : Fin m, B • (1 : Matrix (Fin 1) (Fin 1) ℝ)) =
        ((m:ℝ)*B) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      rw [← sum_smul]
      simp
    simpa only [sum_sub_distrib, hs, edgePredictableVariation, appendixIndicatorZ] using hupper
  have hn : predictableVariationNorm Q mu (appendixIndicatorZ Q i) Y ≤ (m:ℝ)*B :=
    matrixEuclideanNorm_le_of_psd_bounds _ _ (mul_nonneg (Nat.cast_nonneg _) hB) hpsum hupper'
  have hmB : (m:ℝ)*B ≤ (1+η/4)*(m+1 : ℕ)*st.mu i := by
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp [B] at hB ⊢
    nlinarith
  exact hn.trans hmB

/-- The omitted first indicator and the conditional-mean errors together
consume at most three quarters of the target deviation. -/
theorem appendixIndicator_bias {d m : ℕ} (Q : Stoch d) (st : Stationary Q)
    (η : ℝ) (hη : 0 < η)
    (hentry : ∀ a b, |Q.P a b / st.mu b - 1| ≤ η/4) (i : Fin d)
    (hsize : 2/η ≤ (m+1 : ℕ)*st.mu i) (Y : Fin (m+1) → Fin d) :
    |(stateIndicator i (Y 0) - st.mu i) +
      ∑ t : Fin m, (Q.P (Y t.castSucc) i - st.mu i)| ≤
      3/4*η*(m+1 : ℕ)*st.mu i := by
  have hp1 := probability_coordinate_le_one st.mu st.nonneg st.sum_one i
  have hfirst : |stateIndicator i (Y 0) - st.mu i| ≤ 1 := by
    unfold stateIndicator
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith [st.nonneg i]
  have hsum : |∑ t : Fin m, (Q.P (Y t.castSucc) i - st.mu i)| ≤
      (m:ℝ)*(η/4*st.mu i) := by
    calc _ ≤ ∑ t : Fin m, |Q.P (Y t.castSucc) i - st.mu i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin m, η/4*st.mu i :=
        sum_le_sum (fun t _ => appendix_entry_absolute Q st η hentry _ i)
      _ = _ := by simp
  have hlarge : 2 ≤ η*((m+1 : ℕ)*st.mu i) := by
    have h := (div_le_iff₀ hη).mp hsize
    nlinarith
  have hstep : (m:ℝ)*(η/4*st.mu i) ≤ η/4*((m+1 : ℕ)*st.mu i) := by
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith [mul_nonneg hη.le (st.nonneg i)]
  have htri := abs_add_le (stateIndicator i (Y 0) - st.mu i)
    (∑ t : Fin m, (Q.P (Y t.castSucc) i - st.mu i))
  nlinarith

/-- The numerical scalar Freedman denominator is at most `(9/4) ell π_i`,
which yields the constant 36 for `u=(η/4) ell π_i`. -/
theorem appendix_scalar_exponent (η N : ℝ) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hN : 0 < N) :
    -((η*N/4)^2)/(2*((1+η/4)*N+(η*N/4)/3)) ≤ -(η^2*N/36) := by
  have hd : 0 < 2*((1+η/4)*N+(η*N/4)/3) := by positivity
  have hden : 2*((1+η/4)*N+(η*N/4)/3) ≤ (9/4)*N := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hη4) hN.le]
  have heq : (η*N/4)^2 / ((9/4)*N) = η^2*N/36 := by
    field_simp
    ring
  have hf := div_le_div_of_nonneg_left (sq_nonneg (η*N/4)) hd hden
  rw [heq] at hf
  simpa only [neg_div] using neg_le_neg hf

/-- Appendix A's single-residue visit-count estimate, from arbitrary initial
law. The only external premise is the original matrix Freedman theorem;
centering, adaptation, increment bounds and predictable variation have all
been established above for the actual indicator process. -/
theorem appendix_visit_count_tail {d m : ℕ} (Q : Stoch d) (st : Stationary Q)
    (mu : Fin d → ℝ) (hmu : ∀ a, 0 ≤ mu a) (hsum : ∑ a, mu a = 1)
    (η : ℝ) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hentry : ∀ a b, |Q.P a b / st.mu b - 1| ≤ η/4) (i : Fin d)
    (hsize : 2/η ≤ (m+1 : ℕ)*st.mu i) (hinput : MatrixFreedmanInput Q mu) :
    eventProb Q.P mu (fun Y : Fin (m+1) → Fin d =>
      η*(m+1 : ℕ)*st.mu i < |appendixVisitCount i Y - (m+1 : ℕ)*st.mu i|) ≤
      2*exp (-(η^2*(m+1 : ℕ)*st.mu i/36)) := by
  let N : ℝ := (m+1 : ℕ)*st.mu i
  have hN : 0 < N := mul_pos (Nat.cast_pos.mpr (by omega)) (st.pos i)
  let u : ℝ := η*N/4
  let v : ℝ := (1+η/4)*N
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hinc (Y : Fin (m+1) → Fin d)
      (hY : η*(m+1 : ℕ)*st.mu i < |appendixVisitCount i Y - (m+1 : ℕ)*st.mu i|) :
      u ≤ martingaleSumNorm (appendixIndicatorZ Q i) Y ∧
        predictableVariationNorm Q mu (appendixIndicatorZ Q i) Y ≤ v := by
    constructor
    · let S : ℝ := ∑ t : Fin m, (stateIndicator i (Y t.succ) - Q.P (Y t.castSucc) i)
      have hb := appendixIndicator_bias Q st η hη hentry i hsize Y
      have hdecomp := appendixVisitCount_decomposition Q i Y (st.mu i)
      have htri := abs_add_le S ((stateIndicator i (Y 0)-st.mu i) +
        ∑ t : Fin m, (Q.P (Y t.castSucc) i-st.mu i))
      have hS : u < |S| := by
        rw [hdecomp] at hY
        dsimp [u, N, S] at *
        have heq : (∑ t : Fin m, (stateIndicator i (Y t.succ) - Q.P (Y t.castSucc) i)) +
            (stateIndicator i (Y 0)-st.mu i) + ∑ t : Fin m, (Q.P (Y t.castSucc) i-st.mu i) =
            (∑ t : Fin m, (stateIndicator i (Y t.succ) - Q.P (Y t.castSucc) i)) +
            ((stateIndicator i (Y 0)-st.mu i) + ∑ t : Fin m, (Q.P (Y t.castSucc) i-st.mu i)) := by ring
        rw [heq] at hY
        nlinarith
      have hn := appendixScalarMatrix_abs_le_norm S
      have heq : (∑ t : Fin m, appendixIndicatorZ Q i t Y) = appendixScalarMatrix S :=
        appendixIndicator_sum Q i Y
      rw [← heq] at hn
      exact le_trans hS.le hn
    · simpa only [v, N, mul_assoc] using appendixIndicator_variation Q st mu η hη.le hentry i Y
  have hfree := appendixIndicator_freedman (m := m) Q mu hmu hsum i hinput u v hu hv
  calc _ ≤ eventProb Q.P mu (fun Y : Fin (m+1) → Fin d =>
        u ≤ martingaleSumNorm (appendixIndicatorZ Q i) Y ∧
          predictableVariationNorm Q mu (appendixIndicatorZ Q i) Y ≤ v) :=
      eventProb_mono Q.P mu Q.nonneg hmu hinc
    _ ≤ 2*exp (-(u^2)/(2*(v+u/3))) := by simpa only [Nat.cast_one, mul_one, one_mul] using hfree
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      simpa only [u, v, N, mul_assoc, mul_pow] using appendix_scalar_exponent η N hη hη4 hN

end PsgEst
