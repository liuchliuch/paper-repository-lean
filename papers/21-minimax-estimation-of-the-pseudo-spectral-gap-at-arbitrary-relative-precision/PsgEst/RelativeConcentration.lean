import PsgEst.EdgeBridge
import PsgEst.LaplacianCountsSpectrum

/-!
# Relative concentration for the actual normalized edge Laplacian

The only probabilistic inputs in the final proposition are the original scalar
Paulin inequality and the original matrix Freedman inequality. The unregularized
quadratic comparison, degree drift, event inclusion and deterministic normalization
are derived for the observed path and its actual transition counts.
-/

open Matrix BigOperators Real Finset
namespace PsgEst
namespace RelativeConcentration

attribute [local instance] Classical.propDecidable

/-- Conditional edge drift, with its actual empirical departure frequencies. -/
noncomputable def drift {d m : ℕ} (Q : Stoch d) (st : Stationary Q)
    (Y : Fin (m+1) → Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ :=
  ∑ i, ((outDeg Y i:ℝ)/(m:ℝ)) • edgeF Q st i

lemma drift_scaled {d m : ℕ} (Q : Stoch d) (st : Stationary Q)
    (Y : Fin (m+1) → Fin d) (hm : 0 < m) :
    (m:ℝ) • drift Q st Y = ∑ i, (outDeg Y i:ℝ) • edgeF Q st i := by
  unfold drift
  rw [smul_sum]
  apply sum_congr rfl
  intro i _
  rw [smul_smul]
  congr 1
  field_simp

lemma raw_centered_eq {d m : ℕ} (Q : Stoch d) (st : Stationary Q)
    (Y : Fin (m+1) → Fin d) (hm : 0 < m) :
    (m:ℝ) • empiricalHbar st.mu Y - ∑ i, (outDeg Y i:ℝ) • edgeF Q st i =
      (m:ℝ) • (empiricalHbar st.mu Y - drift Q st Y) := by
  rw [smul_sub, drift_scaled Q st Y hm]

/-- The constructed Freedman process is precisely the conjugate of the
observed edge sum minus its conditional drift. -/
lemma process_sum_eq {d m : ℕ} (Q : Stoch d) (st : Stationary Q) (τ : ℝ)
    (Y : Fin (m+1) → Fin d) (hm : 0 < m) :
    (∑ t : Fin m, edgeProcessZ Q st τ t Y) =
      edgeFinEquiv d (edgeProcessA Q st τ *
        ((m:ℝ) • (empiricalHbar st.mu Y - drift Q st Y)) * edgeProcessA Q st τ) := by
  rw [edgeProcess_sum_eq Q st τ Y hm, raw_centered_eq Q st Y hm]

/-- Positivity of each conditional edge matrix turns the departure degree event
into its exact unregularized drift comparison. -/
lemma drift_bounds {d m : ℕ} (Q : Stoch d) (st : Stationary Q)
    (Y : Fin (m+1) → Fin d) (hm : 0 < m) (η : ℝ)
    (hE : degreeEvent st.mu η Y) (x : Fin d ⊕ Fin d → ℝ) :
    (1-η)*(x ⬝ᵥ (stationaryEdgeH Q st *ᵥ x)) ≤ x ⬝ᵥ (drift Q st Y *ᵥ x) ∧
      x ⬝ᵥ (drift Q st Y *ᵥ x) ≤ (1+η)*(x ⬝ᵥ (stationaryEdgeH Q st *ᵥ x)) := by
  have hc := (degreeEvent_iff_counts Y st.mu η hm).mp hE
  have hFi : ∀ i, 0 ≤ x ⬝ᵥ (edgeF Q st i *ᵥ x) := by
    intro i
    simpa only [star_trivial] using (edgeF_posSemidef Q st i).2 x
  have hlo := sum_le_sum (s := (univ : Finset (Fin d))) (fun i _ =>
    mul_le_mul_of_nonneg_right (hc i).1 (hFi i))
  have hhi := sum_le_sum (s := (univ : Finset (Fin d))) (fun i _ =>
    mul_le_mul_of_nonneg_right (hc i).2.1 (hFi i))
  constructor
  · simpa only [drift, stationaryEdgeH, Matrix.sum_mulVec, Matrix.smul_mulVec,
      dotProduct_sum, dotProduct_smul, smul_eq_mul, mul_sum, mul_assoc] using hlo
  · simpa only [drift, stationaryEdgeH, Matrix.sum_mulVec, Matrix.smul_mulVec,
      dotProduct_sum, dotProduct_smul, smul_eq_mul, mul_sum, mul_assoc] using hhi

section RegularizerPullback
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma congruence_quadratic (A D : Matrix ι ι ℝ) (hA : A.IsHermitian) (x : ι → ℝ) :
    x ⬝ᵥ ((A*D*A) *ᵥ x) = (A*ᵥx) ⬝ᵥ (D *ᵥ (A*ᵥx)) := by
  have ht : Aᵀ = A := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, ht]

/-- The explicit inverse square root has inverse energy `H+τI`. -/
lemma regularizerInverse_energy (H : Matrix ι ι ℝ) (hH : H.IsHermitian)
    (hPSD : H.PosSemidef) (τ : ℝ) (hτ : 0 < τ) (x : ι → ℝ) :
    (regularizerInverse hH τ *ᵥ x) ⬝ᵥ (regularizerInverse hH τ *ᵥ x) =
      x ⬝ᵥ (H *ᵥ x) + τ*(x ⬝ᵥ x) := by
  let A := regularizer hH τ
  let B := regularizerInverse hH τ
  have hB : B.IsHermitian := spectralMultiplier_isHermitian hH _
  have hBB : B*B = H+τ • (1 : Matrix ι ι ℝ) := by
    calc
      B*B = B*(A*(H+τ • (1 : Matrix ι ι ℝ))*A)*B := by
        rw [regularizer_normalizes hH hPSD hτ, Matrix.mul_one]
      _ = (B*A)*(H+τ • (1 : Matrix ι ι ℝ))*(A*B) := by noncomm_ring
      _ = _ := by rw [regularizer_inverse_mul hH hPSD hτ,
        regularizer_mul_inverse hH hPSD hτ, Matrix.one_mul, Matrix.mul_one]
  have ht : Bᵀ = B := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.eq
  have hquad : x ⬝ᵥ ((B*B) *ᵥ x) = (B*ᵥx) ⬝ᵥ (B*ᵥx) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ht]
  rw [← hquad, hBB]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul]

end RegularizerPullback
/-- Conjugating the actual martingale norm bound by the explicit inverse
regularizer gives the first unregularized comparison in the proof of (19). -/
theorem martingale_deviation {d m : ℕ} (Q : Stoch d) (st : Stationary Q)
    (Y : Fin (m+1) → Fin d) (hm : 0 < m) (τ η : ℝ) (hτ : 0 < τ)
    (hnorm : martingaleSumNorm (edgeProcessZ Q st τ) Y ≤ η*(m:ℝ))
    (x : Fin d ⊕ Fin d → ℝ) :
    |x ⬝ᵥ ((empiricalHbar st.mu Y-drift Q st Y) *ᵥ x)| ≤
      η*(x ⬝ᵥ (stationaryEdgeH Q st *ᵥ x)+τ*(x ⬝ᵥ x)) := by
  let H := stationaryEdgeH Q st
  have hPSD : H.PosSemidef := stationaryEdgeH_posSemidef Q st
  let A := edgeProcessA Q st τ
  let B := regularizerInverse hPSD.isHermitian τ
  let D := empiricalHbar st.mu Y-drift Q st Y
  have hA : A.IsHermitian := regularizer_isHermitian hPSD.isHermitian τ
  have hABx : A *ᵥ (B *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec]
    change (regularizer hPSD.isHermitian τ * regularizerInverse hPSD.isHermitian τ) *ᵥ x = x
    rw [regularizer_mul_inverse hPSD.isHermitian hPSD hτ, Matrix.one_mulVec]
  have hn := hnorm
  change matrixEuclideanNorm (∑ t : Fin m, edgeProcessZ Q st τ t Y) ≤ η*(m:ℝ) at hn
  rw [process_sum_eq Q st τ Y hm] at hn
  change matrixEuclideanNorm (edgeFinEquiv d (A*((m:ℝ) • D)*A)) ≤ η*(m:ℝ) at hn
  have hq := edgeFin_norm_quadratic_le (A*((m:ℝ) • D)*A) (B*ᵥx)
  have hBx : 0 ≤ (B*ᵥx) ⬝ᵥ (B*ᵥx) := by
    simpa only [star_trivial] using dotProduct_star_self_nonneg (B*ᵥx)
  have hq' := hq.trans (mul_le_mul_of_nonneg_right hn hBx)
  rw [congruence_quadratic A ((m:ℝ) • D) hA, hABx] at hq'
  have henergy : (B*ᵥx) ⬝ᵥ (B*ᵥx) = x ⬝ᵥ (H*ᵥx)+τ*(x ⬝ᵥ x) :=
    regularizerInverse_energy H hPSD.isHermitian hPSD τ hτ x
  rw [henergy] at hq'
  have hmR : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, abs_mul,
    abs_of_pos hmR] at hq'
  apply (mul_le_mul_left hmR).mp
  convert hq' using 1 <;> ring

/-- Adding the actual count drift to the actual martingale deviation yields
(19), for the population and empirical matrices of the paper. -/
theorem form_bounds {d m : ℕ} (Q : Stoch d) (st : Stationary Q)
    (Y : Fin (m+1) → Fin d) (hm : 0 < m) (τ η : ℝ) (hτ : 0 < τ)
    (hE : degreeEvent st.mu η Y)
    (hnorm : martingaleSumNorm (edgeProcessZ Q st τ) Y ≤ η*(m:ℝ)) :
    ∀ x : Fin d ⊕ Fin d → ℝ,
      (1-2*η)*(x ⬝ᵥ (bipH (simil st.mu Q.P) *ᵥ x))-η*τ*(x ⬝ᵥ x) ≤
        x ⬝ᵥ (empiricalHbar st.mu Y *ᵥ x) ∧
      x ⬝ᵥ (empiricalHbar st.mu Y *ᵥ x) ≤
        (1+2*η)*(x ⬝ᵥ (bipH (simil st.mu Q.P) *ᵥ x))+η*τ*(x ⬝ᵥ x) := by
  intro x
  have hd := drift_bounds Q st Y hm η hE x
  have he := martingale_deviation Q st Y hm τ η hτ hnorm x
  have hH : stationaryEdgeH Q st = bipH (simil st.mu Q.P) :=
    stationary_edge_sum_eq_bipH Q st
  rw [hH] at hd he
  simp only [Matrix.sub_mulVec, dotProduct_sub, abs_le] at he
  constructor <;> nlinarith only [hd.1, hd.2, he.1, he.2]

/-- The actual success event of Proposition 1. -/
def good {d m : ℕ} (Q : Stoch d) (st : Stationary Q) (τ η : ℝ)
    (Y : Fin (m+1) → Fin d) : Prop :=
  degPos Y ∧ |(1-sigma2 (lHat Y))-(1-sigma2 (simil st.mu Q.P))| ≤
    η*(3*(1-sigma2 (simil st.mu Q.P))+τ)/(1-η)

/-- The concrete degree and martingale events imply the actual Proposition 1
success event, after the proved ordered-spectrum normalization. -/
theorem good_of_degree_and_norm {d m : ℕ} (hd : 1 < d) (Q : Stoch d) (st : Stationary Q)
    (Y : Fin (m+1) → Fin d) (hm : 0 < m) (τ η : ℝ)
    (hτ : 0 < τ) (hη : 0 < η) (hη' : η ≤ 1/4)
    (hE : degreeEvent st.mu η Y)
    (hnorm : martingaleSumNorm (edgeProcessZ Q st τ) Y ≤ η*(m:ℝ)) :
    good Q st τ η Y := by
  have hc := (degreeEvent_iff_counts Y st.mu η hm).mp hE
  have hout : degEvent (fun i => (outDeg Y i:ℝ)/(m:ℝ)) st.mu η :=
    fun i => ⟨(hc i).1, (hc i).2.1⟩
  have hin : degEvent (fun i => (inDeg Y i:ℝ)/(m:ℝ)) st.mu η :=
    fun i => ⟨(hc i).2.2.1, (hc i).2.2.2⟩
  have hforms := form_bounds Q st Y hm τ η hτ hE hnorm
  have hL : Lk Q st 1 = simil st.mu Q.P := by simp only [Lk, pow_one]
  have hresult := prop1_deterministic_counts hd Q st 1 Y hm τ η hτ hη hη' hout hin
    (fun x => by rw [hL]; exact (hforms x).1)
    (fun x => by rw [hL]; exact (hforms x).2)
  simpa only [good, hL] using hresult

/-- The one-state case has positive degrees as soon as one transition is
observed and both singular deficits equal one. -/
lemma good_one_state {m : ℕ} (Q : Stoch 1) (st : Stationary Q)
    (Y : Fin (m+1) → Fin 1) (hm : 0 < m) (τ η : ℝ)
    (hτ : 0 < τ) (hη : 0 < η) (hη' : η ≤ 1/4) : good Q st τ η Y := by
  have ho : outDeg Y 0 = m := by simpa only [Fin.sum_univ_one] using sum_outDeg Y
  have hi : inDeg Y 0 = m := by simpa only [Fin.sum_univ_one] using sum_inDeg Y
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    change 0 < outDeg Y 0 ∧ 0 < inDeg Y 0
    rw [ho, hi]
    exact ⟨hm,hm⟩
  · have hsig (M : Matrix (Fin 1) (Fin 1) ℝ) : sigma2 M = 0 := by
      unfold sigma2
      rw [dif_neg (by omega)]
    simp only [hsig, sub_zero, sub_self, abs_zero]
    exact div_nonneg (mul_nonneg hη.le (by linarith)) (by linarith)

/-- Proposition 1 from only the two original external probability inequalities.
Every martingale, variance, regularizer, count and spectral hypothesis has been
proved for this very trajectory process. -/
theorem proposition_1_of_external {d m : ℕ} [NeZero d] (Q : Stoch d) (st : Stationary Q)
    (τ η : ℝ) (mu : Fin d → ℝ) (hτ : 0 < τ) (hη : 0 < η) (hη' : η ≤ 1/4)
    (hmΓ : 1 ≤ (m:ℝ)*gammaPS Q st) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hPaulin : PaulinOriginalInput Q st (gammaPS Q st))
    (hFreedman : MatrixFreedmanInput Q mu) :
    pathMeasure Q.P mu (univ.filter fun Y : Fin (m+1) → Fin d => ¬ good Q st τ η Y) ≤
      4*(d:ℝ)/Stationary.star st*exp (-((m:ℝ)*Stationary.star st*gammaPS Q st*η^2)/36) +
      4*(d:ℝ)*exp (-(3*(m:ℝ)*Stationary.star st*τ*η^2)/16) := by
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    simp only [hm0, Nat.cast_zero, zero_mul] at hmΓ
    linarith
  by_cases hd : 1 < d
  · have hΓ : 0 < gammaPS Q st := by
      by_contra h
      have hle := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) (le_of_not_gt h)
      linarith
    have hdeg := degree_failure_bound Q st mu hmu hsum (gammaPS Q st) η hΓ hη
      (by linarith) hmΓ (paulin_upper_bounds Q st _ hΓ hPaulin)
    have hmart := edgeProcess_tail Q st mu hmu hsum τ η hτ hη hη' hm hFreedman
    have hpEq : pathMeasure Q.P mu (univ.filter fun Y : Fin (m+1) → Fin d => ¬ good Q st τ η Y) =
        eventProb Q.P mu (fun Y : Fin (m+1) → Fin d => ¬ good Q st τ η Y) := by
      unfold eventProb
      congr
    rw [hpEq]
    calc
      _ ≤ eventProb Q.P mu (fun Y : Fin (m+1) → Fin d =>
        (¬ degreeEvent st.mu η Y) ∨ (degreeEvent st.mu η Y ∧
          η*(m:ℝ) < martingaleSumNorm (edgeProcessZ Q st τ) Y)) := by
        apply eventProb_mono Q.P mu Q.nonneg hmu
        intro Y hfail
        by_cases hE : degreeEvent st.mu η Y
        · right
          refine ⟨hE, ?_⟩
          by_contra hnorm
          exact hfail (good_of_degree_and_norm hd Q st Y hm τ η hτ hη hη' hE (le_of_not_gt hnorm))
        · exact Or.inl hE
      _ ≤ eventProb Q.P mu (fun Y : Fin (m+1) → Fin d => ¬ degreeEvent st.mu η Y) +
        eventProb Q.P mu (fun Y : Fin (m+1) → Fin d => degreeEvent st.mu η Y ∧
          η*(m:ℝ) < martingaleSumNorm (edgeProcessZ Q st τ) Y) :=
        eventProb_or_le Q.P mu Q.nonneg hmu _ _
      _ ≤ _ := by
        have h := add_le_add hdeg hmart
        simpa only [neg_div] using h
  · have hd1 : d = 1 := by have := NeZero.ne d; omega
    subst d
    have hevent : (univ.filter fun Y : Fin (m+1) → Fin 1 => ¬ good Q st τ η Y) = ∅ := by
      ext Y
      simp only [mem_filter, mem_univ, true_and, Finset.not_mem_empty, iff_false, not_not]
      exact good_one_state Q st Y hm τ η hτ hη hη'
    rw [hevent]
    simp only [pathMeasure, sum_empty]
    have hp := Stationary.star_pos st
    positivity

end RelativeConcentration
end PsgEst
