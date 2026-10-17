import Paper38.GaussianLocalization
import Paper38.StandardizedShape

/-! The localized initial moment estimate (7.3), derived from actual Gaussian
sample moments. Only the raw Wishart covariance moment is an external input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Matrix MatrixOrder ENNReal

namespace Paper38.GaussianMomentMismatch
open Model HilbertCoordinates GaussianLocalization

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
lemma population_covariance_posDef (A : Mat d) (hA : A.PosDef) : (A*Aᵀ).PosDef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.mul_conjTranspose_self A (Matrix.vecMul_injective_iff_isUnit.mpr hA.isUnit)

omit [NeZero d] in
lemma sqrt_population_covariance (A : Mat d) (hA : A.PosDef) : CFC.sqrt (A*Aᵀ) = A := by
  have ht : Aᵀ = A := by simpa using hA.1
  exact (CFC.sqrt_eq_iff _ _ (population_covariance_posDef A hA).posSemidef.nonneg
    hA.posSemidef.nonneg).mpr (by rw [ht])

omit [NeZero d] in
lemma frobSq_sub_comm (A B : Mat d) : frobSq (A-B) = frobSq (B-A) := by
  unfold frobSq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (A i j - B i j) ^ 2 = (B i j - A i j) ^ 2
  ring

omit [NeZero d] in
lemma affine_covariance_difference_bound (A S : Mat d) :
    frobSq (A*S*Aᵀ - A*Aᵀ) ≤ frobNorm A ^ 4 * frobSq (S-1) := by
  have he : A*S*Aᵀ - A*Aᵀ = A*(S-1)*Aᵀ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  have hf : frobNorm (A*S*Aᵀ - A*Aᵀ) ≤ frobNorm A ^ 2 * frobNorm (S-1) := by
    rw [he]
    calc
      frobNorm (A*(S-1)*Aᵀ) ≤ frobNorm (A*(S-1)) * frobNorm Aᵀ := frobNorm_mul _ _
      _ ≤ (frobNorm A * frobNorm (S-1)) * frobNorm A := by
        rw [frobNorm_transpose]
        exact mul_le_mul_of_nonneg_right (frobNorm_mul _ _) (norm_nonneg _)
      _ = _ := by ring
  calc
    frobSq (A*S*Aᵀ-A*Aᵀ) = frobNorm (A*S*Aᵀ-A*Aᵀ) ^ 2 := (frobNorm_sq _).symm
    _ ≤ (frobNorm A ^ 2 * frobNorm (S-1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hf 2
    _ = _ := by rw [mul_pow, frobNorm_sq (S-1)]; ring

def mismatchConstant (A : Mat d) : ℝ :=
  max 1 (max (Sampling.opNorm A ^ 2) (frobNorm A ^ 4 / (AffineLifting.covarianceMin A : ℝ)))

lemma mismatchConstant_pos (A : Mat d) : 0 < mismatchConstant A :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- A pathwise moment bound for every symmetric well-conditioned raw covariance.
The constant depends only on the fixed population matrix. -/
theorem affine_mismatch_bound (μ : E d) (A : Mat d) (hA : A.PosDef)
    (z : E d) (S : Mat d) (hSym : Sᵀ = S) (ε : ℝ)
    (hε : 0 ≤ ε) (hε' : ε < 1) (hS : Sampling.opNorm (S-1) ≤ ε) :
    ‖rootState (μ + matVec A z) (A*S*Aᵀ) - rootState μ (A*Aᵀ)‖ ^ 2 ≤
      mismatchConstant A * (‖z‖ ^ 2 + frobSq (S-1)) := by
  have hpS := posDef_of_opNorm S hSym ε hε' hS
  have hpC : (A*S*Aᵀ).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hpS.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hA.isUnit)
  have hpD := population_covariance_posDef A hA
  let mD : ℝ := AffineLifting.covarianceMin A
  let mC : ℝ := (1-ε) * mD
  have hmD : 0 < mD := covarianceMin_pos A hA
  have hmC : 0 < mC := mul_pos (sub_pos.mpr hε') hmD
  have hLC : ∀ v : Fin d → ℝ, mC * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((A*S*Aᵀ) *ᵥ v) := by
    intro v
    have h := (affine_covariance_rayleigh A S hA ε hε hε' hS (vec d v)).1
    rw [norm_vec_sq] at h
    simpa only [quadratic, vec, WithLp.ofLp_toLp] using h
  have hLD : ∀ v : Fin d → ℝ, mD * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((A*Aᵀ) *ᵥ v) := by
    intro v
    have h := AffineLifting.lower_rayleigh (A*Aᵀ) hpD.1 (vec d v)
    rw [AffineLifting.inner_matVec_eq, norm_vec_sq] at h
    simpa only [vec, WithLp.ofLp_toLp] using h
  let den := Real.sqrt mC + Real.sqrt mD
  have hden : 0 < den := add_pos (Real.sqrt_pos.mpr hmC) (Real.sqrt_pos.mpr hmD)
  have hden2 : mD ≤ den ^ 2 := by
    have hc := Real.sqrt_nonneg mC
    have hd := Real.sqrt_nonneg mD
    have hsq := Real.sq_sqrt hmD.le
    dsimp [den]
    nlinarith
  have hbase := rootState_distance_sq_le (μ+matVec A z) μ (A*S*Aᵀ) (A*Aᵀ)
    hpC hpD mC mD hmC.le hmD.le hden hLC hLD
  have hmean : ‖μ+matVec A z-μ‖ ^ 2 ≤ Sampling.opNorm A ^ 2 * ‖z‖ ^ 2 := by
    simpa only [add_sub_cancel_left, mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (norm_matVec_le A z) 2
  have hcov0 : 0 ≤ frobSq (A*S*Aᵀ-A*Aᵀ) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hdiv : frobSq (A*S*Aᵀ-A*Aᵀ) / den ^ 2 ≤ frobSq (A*S*Aᵀ-A*Aᵀ) / mD :=
    div_le_div_of_nonneg_left hcov0 hmD hden2
  have hcov := affine_covariance_difference_bound A S
  have hcov' : frobSq (A*S*Aᵀ-A*Aᵀ) / mD ≤
      (frobNorm A ^ 4 / mD) * frobSq (S-1) := by
    calc
      _ ≤ (frobNorm A ^ 4 * frobSq (S-1)) / mD := div_le_div_of_nonneg_right hcov hmD.le
      _ = _ := by ring
  have hK1 : Sampling.opNorm A ^ 2 ≤ mismatchConstant A :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hK2 : frobNorm A ^ 4 / mD ≤ mismatchConstant A :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hF : 0 ≤ frobSq (S-1) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  calc
    _ ≤ ‖μ+matVec A z-μ‖ ^ 2 + frobSq (A*S*Aᵀ-A*Aᵀ) / den ^ 2 := hbase
    _ ≤ Sampling.opNorm A ^ 2 * ‖z‖ ^ 2 + (frobNorm A ^ 4 / mD) * frobSq (S-1) :=
      add_le_add hmean (hdiv.trans hcov')
    _ ≤ mismatchConstant A * (‖z‖ ^ 2 + frobSq (S-1)) := by
      nlinarith [mul_le_mul_of_nonneg_right hK1 (sq_nonneg ‖z‖),
        mul_le_mul_of_nonneg_right hK2 hF]

/-- Raw covariance control gives the actual initial moment-defect estimate.
This also applies to the high-probability event (7.6), with ε=1/2. -/
theorem initial_moment_mismatch_of_opNorm {N : ℕ} (hN : 0 < N) (μ : E d)
    (A : Mat d) (hA : A.PosDef) (ω : Sampling.Sample d N) (ε : ℝ)
    (hε : 0 ≤ ε) (hε' : ε < 1) (hOp : Sampling.opNorm (Sampling.covariance d N ω - 1) ≤ ε) :
    coordinateSqDist (Specification.cloudQ (initialCloud μ A ω)) (μ,A) ≤
      mismatchConstant A * Sampling.defect d N ω := by
  have hp := ModelBridges.empiricalCovariance_posSemidef (Sampling.cloud d N ω)
  have ht : (Sampling.covariance d N ω)ᵀ = Sampling.covariance d N ω := by simpa using hp.1
  have h := affine_mismatch_bound μ A hA (Sampling.mean d N ω) (Sampling.covariance d N ω)
    ht ε hε hε' hOp
  rw [← coordinateSqDist_toModel, toModel_rootState, toModel_rootState,
    sqrt_population_covariance A hA] at h
  change coordinateSqDist (empiricalMean (initialCloud μ A ω),
    covarianceRoot (empiricalCovariance (initialCloud μ A ω))) (μ,A) ≤ _
  rw [(initial_moments hN μ A ω).1, (initial_moments hN μ A ω).2]
  simpa only [Specification.cloudQ, Sampling.defect, frobSq_sub_comm,
    add_comm (‖Sampling.mean d N ω‖ ^ 2)] using h

/-- The source moment error on G_N is bounded by the raw sample defect. -/
theorem good_moment_mismatch {N : ℕ} (hN : 0 < N) (μ : E d) (A : Mat d) (hA : A.PosDef)
    (ω : Sampling.Sample d N) (hω : ω ∈ Sampling.good d N) :
    coordinateSqDist (Specification.cloudQ (initialCloud μ A ω)) (μ,A) ≤
      mismatchConstant A * Sampling.defect d N ω :=
  initial_moment_mismatch_of_opNorm hN μ A hA ω (1/4) (by norm_num) (by norm_num) hω.2

/-- Equation (7.3) in nonnegative-expectation form. The event measurability and
Wishart covariance moment are raw statistical inputs; the moment error is derived. -/
theorem expected_good_moment_mismatch (hd : 1 ≤ d) {N : ℕ} (hN : d+1 ≤ N)
    (mom : ExternalStatisticalInputs.CovarianceMoments d)
    (hgood : MeasurableSet (Sampling.good d N)) (μ : E d) (A : Mat d) (hA : A.PosDef) :
    (∫⁻ ω in Sampling.good d N,
      ENNReal.ofReal (coordinateSqDist (Specification.cloudQ (initialCloud μ A ω)) (μ,A))
      ∂Sampling.law d N) ≤
      ENNReal.ofReal ((mismatchConstant A * ((d : ℝ)*(d+2))) / N) := by
  have hNpos : 0 < N := by omega
  have hK := (mismatchConstant_pos A).le
  calc
    _ ≤ ∫⁻ ω in Sampling.good d N,
        ENNReal.ofReal (mismatchConstant A) * ENNReal.ofReal (Sampling.defect d N ω)
        ∂Sampling.law d N := by
      apply setLIntegral_mono' hgood
      intro ω hω
      rw [← ENNReal.ofReal_mul hK]
      exact ENNReal.ofReal_le_ofReal (good_moment_mismatch hNpos μ A hA ω hω)
    _ ≤ ∫⁻ ω, ENNReal.ofReal (mismatchConstant A) * ENNReal.ofReal (Sampling.defect d N ω)
        ∂Sampling.law d N := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (mismatchConstant A) * ∫⁻ ω,
        ENNReal.ofReal (Sampling.defect d N ω) ∂Sampling.law d N :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (mismatchConstant A) * ENNReal.ofReal (((d : ℝ)*(d+2))/N) :=
      mul_le_mul_left' (StandardizedShape.expected_defect hd hN mom) _
    _ = _ := by rw [← ENNReal.ofReal_mul hK]; congr 1; ring

/-- A bounded raw defect and covariance operator control place all high-
probability initial states in one deterministic compact coordinate box. -/
theorem initial_state_localized_of_defect {N : ℕ} (hN : 0 < N)
    (μ : E d) (A : Mat d) (hA : A.PosDef) (ω : Sampling.Sample d N)
    (M : ℝ) (hM : 0 ≤ M) (hdef : Sampling.defect d N ω ≤ M)
    (hOp : Sampling.opNorm (Sampling.covariance d N ω - 1) ≤ 1/2) :
    rootState (empiricalMean (initialCloud μ A ω)) (empiricalCovariance (initialCloud μ A ω)) ∈
      localizationBox μ A (Real.sqrt M) (1/2) := by
  have hF : 0 ≤ frobSq (1-Sampling.covariance d N ω) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hm2 : ‖Sampling.mean d N ω‖ ^ 2 ≤ M := by
    unfold Sampling.defect at hdef
    linarith
  have hm : ‖Sampling.mean d N ω‖ ≤ Real.sqrt M := by
    have hs := Real.sq_sqrt hM
    have hp := Real.sqrt_nonneg M
    have hn := norm_nonneg (Sampling.mean d N ω)
    nlinarith
  have hp := ModelBridges.empiricalCovariance_posSemidef (Sampling.cloud d N ω)
  have ht : (Sampling.covariance d N ω)ᵀ = Sampling.covariance d N ω := by simpa using hp.1
  rw [(initial_moments hN μ A ω).1, (initial_moments hN μ A ω).2]
  exact affine_state_mem_localizationBox μ A hA _ _ ht _ _ (Real.sqrt_nonneg M)
    (by norm_num) (by norm_num) hm hOp

omit [NeZero d] in
/-- Uniform-in-N form of (7.3) for the exact population Gaussian initialization. -/
theorem expected_good_gaussian_moment_mismatch (hd : 1 ≤ d)
    (mom : ExternalStatisticalInputs.CovarianceMoments d)
    (conc : ExternalStatisticalInputs.Concentration d)
    (μ : E d) (S0 : Mat d) (hS0 : S0.PosDef) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, d+1 ≤ N →
      (∫⁻ ω in Sampling.good d N,
        ENNReal.ofReal (coordinateSqDist
          (Specification.cloudQ (Specification.gaussianCloud μ S0 N ω)) (μ, covarianceRoot S0))
        ∂Sampling.law d N) ≤ ENNReal.ofReal (C/N) := by
  letI : NeZero d := ⟨by omega⟩
  let A := covarianceRoot S0
  have hA : A.PosDef := hS0.posDef_sqrt
  refine ⟨mismatchConstant A * ((d : ℝ)*(d+2)), ?_, ?_⟩
  · apply mul_pos (mismatchConstant_pos A)
    exact mul_pos (by exact_mod_cast (show 0 < d by omega)) (by positivity)
  · intro N hN
    exact expected_good_moment_mismatch hd hN mom (conc.good_measurable N) μ A hA

end Paper38.GaussianMomentMismatch
