import PUT.FourierModel
import PUT.RadialEstimate
import PUT.PrincipalCoefficients
import PUT.FullNormAssembly

/-!
# Whole radial Fourier-sector difference estimates

The local operators are the actual multiplication/inner-product expressions
of the preparation difference. Their decomposition into the principal
coefficient and the Dirichlet residual is proved here, rather than assumed.
-/
noncomputable section
namespace PUT.SectorEstimates
open MeasureTheory FourierModel
open scoped ENNReal ComplexConjugate

variable {d M : ℕ} {a : ℝ}

/-- Both constructions choose the same actual L² normalized moment vector. -/
theorem normalizedWeight_eq_radial (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (k : Fin d → ℕ) :
    RadialEstimate.normalizedWeight moments hd ha k = radial (by omega : 0 < d) ha k := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp (RadialEstimate.weight_memLp moments hd ha k).ofReal).trans
    (radial_ae (by omega : 0 < d) ha k).symm

private theorem weight_residual_identity (ha : 0 < a) (k : Fin d → ℕ)
    (i : Fin d) (p : Fin d → ℝ) (hp : ∀ j, 0 < p j) :
    Real.sqrt (p i) * weight a (degUp k i) p =
      createCoeff a k i * weight a k p + RadialEstimate.residualFun a k i p := by
  have hd : 0 < d := by have := i.isLt; omega
  have hq := RadialEstimate.postMean_pos k i ha hd
  have hb : (Real.sqrt (postMean a k i)) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hc := create_weight_id a k i p hp ha
  change Real.sqrt (p i) * weight a k p =
    Real.sqrt (postMean a k i) * weight a (degUp k i) p at hc
  change Real.sqrt (p i) * weight a (degUp k i) p =
    Real.sqrt (postMean a k i) * weight a k p +
      (p i - postMean a k i) / Real.sqrt (postMean a k i) * weight a k p
  apply (mul_left_cancel₀ hb)
  calc
    Real.sqrt (postMean a k i) * (Real.sqrt (p i) * weight a (degUp k i) p) =
        Real.sqrt (p i) * (Real.sqrt (postMean a k i) * weight a (degUp k i) p) := by ring
    _ = p i * weight a k p := by
      rw [← hc, ← mul_assoc, ← pow_two, Real.sq_sqrt (hp i).le]
    _ = Real.sqrt (postMean a k i) *
        (Real.sqrt (postMean a k i) * weight a k p +
        (p i - postMean a k i) / Real.sqrt (postMean a k i) * weight a k p) := by
      rw [mul_add]
      have hcancel : Real.sqrt (postMean a k i) *
          ((p i - postMean a k i) / Real.sqrt (postMean a k i) * weight a k p) =
          (p i - postMean a k i) * weight a k p := by field_simp
      rw [hcancel]
      rw [← mul_assoc, ← pow_two, Real.sq_sqrt hq.le]
      ring

/-- The radial residual of creation is an exact L² vector difference. -/
theorem sqrtMultiply_up (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (k : Fin d → ℕ) (i : Fin d) :
    sqrtMultiply (by omega : 0 < d) ha i (radial (by omega : 0 < d) ha (degUp k i)) =
      (createCoeff a k i : ℂ) • radial (by omega : 0 < d) ha k +
        RadialEstimate.residual moments hd ha k i := by
  apply Lp.ext
  have hr : RadialEstimate.residual moments hd ha k i =ᵐ[dirichletMeasure d a]
      (fun p => (RadialEstimate.residualFun a k i p : ℂ)) :=
    MemLp.coeFn_toLp (RadialEstimate.residual_memLp moments hd ha k i).ofReal
  filter_upwards [sqrtMultiply_ae (by omega : 0 < d) ha i (radial (by omega : 0 < d) ha (degUp k i)),
    radial_ae (by omega : 0 < d) ha (degUp k i), radial_ae (by omega : 0 < d) ha k, hr,
    Lp.coeFn_add ((createCoeff a k i : ℂ) • radial (by omega : 0 < d) ha k)
      (RadialEstimate.residual moments hd ha k i),
    Lp.coeFn_smul (createCoeff a k i : ℂ) (radial (by omega : 0 < d) ha k),
    dirichletMeasure_ae_positiveSimplex (by omega : 0 < d) ha]
      with p hm hu hk hres had hsm hp
  rw [hm, hu, had, Pi.add_apply, hsm, Pi.smul_apply, hk, hres, smul_eq_mul]
  exact_mod_cast weight_residual_identity ha k i p hp.1

theorem degUp_degDown (k : Fin d → ℕ) (i : Fin d) (hi : 0 < k i) :
    degUp (degDown k i) i = k := by
  funext j
  by_cases hj : j = i
  · subst j; simp [degUp, degDown, Nat.sub_add_cancel (by omega : 1 ≤ k i)]
  · simp [degUp, degDown, hj]

theorem createCoeff_down (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (k : Fin d → ℕ) (i : Fin d) (hi : 0 < k i) :
    createCoeff a (degDown k i) i = eraseCoeff a k i := by
  change Real.sqrt (postMean a (degDown k i) i) = Real.sqrt (postMeanMinus a k i)
  rw [RadialEstimate.postMean_down moments hd ha k i hi]

/-- The corresponding erasure residual, including the boundary `k_i = 1`. -/
theorem sqrtMultiply_down (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (k : Fin d → ℕ) (i : Fin d) (hi : 0 < k i) :
    sqrtMultiply (by omega : 0 < d) ha i (radial (by omega : 0 < d) ha k) =
      (eraseCoeff a k i : ℂ) • radial (by omega : 0 < d) ha (degDown k i) +
        RadialEstimate.residual moments hd ha (degDown k i) i := by
  have he := sqrtMultiply_up moments hd ha (degDown k i) i
  rwa [degUp_degDown k i hi, createCoeff_down moments hd ha k i hi] at he

/-- A principal rank-one column with the actual Euclidean coefficient vector. -/
def principalColumn (hd : 0 < d) (ha : 0 < a) (A : ℝ) (n : PhaseIndex d M) :
    RadialL2 d a →L[ℂ] EuclideanSpace ℂ (Coord d M) :=
  (innerSL ℂ (radial hd ha (degreeOf n))).smulRight
    (Principal.vector (Principal.principalPlus a A n))

theorem principalColumn_norm (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (A : ℝ) (hA : 0 < A) (hM : 0 < M)
    (n : PhaseIndex d M) :
    ‖principalColumn (by omega : 0 < d) ha A n‖ ≤
      Principal.creationBound a A d + etaM A M := by
  have hb := Principal.principalPlus_norm a A n ha hA (by omega : 0 < d) hM
  apply ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans hb)
  intro h
  change ‖inner ℂ (radial (by omega : 0 < d) ha (degreeOf n)) h •
    Principal.vector (Principal.principalPlus a A n)‖ ≤ _
  rw [norm_smul]
  have hin := norm_inner_le_norm (𝕜 := ℂ) (radial (by omega : 0 < d) ha (degreeOf n)) h
  rw [radial_norm moments hd ha, one_mul] at hin
  exact (mul_le_mul_of_nonneg_right hin (norm_nonneg _)).trans
    (by nlinarith [norm_nonneg h])

/-- The local full `D₊` column, with the adjacent actual radial multiplication. -/
def plusLocal (hd : 0 < d) (ha : 0 < a) (A : ℝ) (n : PhaseIndex d M) :
    RadialL2 d a →L[ℂ] EuclideanSpace ℂ (Coord d M) :=
  (EuclideanSpace.equiv (Coord d M) ℂ).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun ij =>
      ((1 / Real.sqrt M : ℝ) : ℂ) •
        (((cutoff A (degreeOf (shift n ij.1 ij.2)) : ℝ) : ℂ) •
          (innerSL ℂ (radial hd ha (degreeOf (shift n ij.1 ij.2))) ∘L sqrtMultiply hd ha ij.1) -
          ((cutoff A (degreeOf n) / Real.sqrt d : ℝ) : ℂ) •
            innerSL ℂ (radial hd ha (degreeOf n))))

@[simp] theorem plusLocal_apply (hd : 0 < d) (ha : 0 < a) (A : ℝ)
    (n : PhaseIndex d M) (h : RadialL2 d a) (ij : Coord d M) :
    plusLocal hd ha A n h ij = ((1 / Real.sqrt M : ℝ) : ℂ) *
      ((cutoff A (degreeOf (shift n ij.1 ij.2)) : ℂ) *
        inner ℂ (radial hd ha (degreeOf (shift n ij.1 ij.2))) (sqrtMultiply hd ha ij.1 h) -
        ((cutoff A (degreeOf n) / Real.sqrt d : ℝ) : ℂ) *
          inner ℂ (radial hd ha (degreeOf n)) h) := rfl


theorem plusLocal_decomposition (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (A : ℝ) (n : PhaseIndex d M) :
    plusLocal (by omega : 0 < d) ha A n =
      principalColumn (by omega : 0 < d) ha A n +
        RadialEstimate.creationResidualMap moments hd ha n A := by
  apply ContinuousLinearMap.ext
  intro h
  apply WithLp.ofLp_injective
  funext ij
  change plusLocal (by omega : 0 < d) ha A n h ij = _
  rw [plusLocal_apply]
  change _ = inner ℂ (radial (by omega : 0 < d) ha (degreeOf n)) h *
      (Principal.principalPlus a A n ij : ℂ) +
        RadialEstimate.creationResidualMap moments hd ha n A h ij
  rw [RadialEstimate.creationResidualMap_apply]
  by_cases hn : 0 ≤ n ij.1 ij.2
  · rw [degree_shift_creation n ij.1 ij.2 hn,
      ← sqrtMultiply_inner (by omega : 0 < d) ha ij.1,
      sqrtMultiply_up moments hd ha (degreeOf n) ij.1,
      inner_add_left, inner_smul_left]
    simp only [hn, if_true, Principal.principalPlus, Principal.creationPlus,
      Complex.conj_ofReal, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  · have hneg : n ij.1 ij.2 < 0 := lt_of_not_ge hn
    rw [degree_shift_erasure n ij.1 ij.2 hneg,
      ← sqrtMultiply_inner (by omega : 0 < d) ha ij.1,
      sqrtMultiply_radial_erasure (by omega : 0 < d) ha (degreeOf n) ij.1
        (Principal.degree_pos_of_negative n ij.1 ij.2 hneg), inner_smul_left]
    simp only [hn, if_false, Principal.principalPlus, Principal.erasurePlus,
      Complex.conj_ofReal, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul]
    ring

/-- Paper (19), for the actual whole radial sector, without any hypothesis
that discards or bounds a radial complement. -/
theorem plusLocal_norm_le (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (A : ℝ) (hA : 0 < A) (hM : 0 < M)
    (n : PhaseIndex d M) :
    ‖plusLocal (by omega : 0 < d) ha A n‖ ≤ FullNorm.plusEnvelope a A d M := by
  rw [plusLocal_decomposition moments hd ha A n]
  exact (norm_add_le _ _).trans (by
    have hp := principalColumn_norm moments hd ha A hA hM n
    have hr := RadialEstimate.creationResidualMap_paper_bound moments hd ha n A hA.le hM
    dsimp only [FullNorm.plusEnvelope, Principal.creationBound] at *
    linarith)

/-- The exact radial coefficient vector of the `D₋` output row. -/
def minusVector (hd : 0 < d) (ha : 0 < a) (A : ℝ) (n : PhaseIndex d M) :
    QueryModel.Register (Coord d M) (RadialL2 d a) :=
  WithLp.toLp 2 (fun ij => ((1 / Real.sqrt M : ℝ) : ℂ) •
    ((cutoff A (degreeOf n) : ℂ) • sqrtMultiply hd ha ij.1 (radial hd ha (degreeOf n)) -
      ((cutoff A (degreeOf (shift n ij.1 ij.2)) / Real.sqrt d : ℝ) : ℂ) •
        radial hd ha (degreeOf (shift n ij.1 ij.2))))

/-- The local `D₋` row acts on the full orthogonal sum of radial inputs. -/
def minusLocal (hd : 0 < d) (ha : 0 < a) (A : ℝ) (n : PhaseIndex d M) :
    QueryModel.Register (Coord d M) (RadialL2 d a) →L[ℂ] ℂ :=
  innerSL ℂ (minusVector hd ha A n)

@[simp] theorem minusVector_apply (hd : 0 < d) (ha : 0 < a) (A : ℝ)
    (n : PhaseIndex d M) (ij : Coord d M) :
    minusVector hd ha A n ij = ((1 / Real.sqrt M : ℝ) : ℂ) •
      ((cutoff A (degreeOf n) : ℂ) • sqrtMultiply hd ha ij.1 (radial hd ha (degreeOf n)) -
      ((cutoff A (degreeOf (shift n ij.1 ij.2)) / Real.sqrt d : ℝ) : ℂ) •
        radial hd ha (degreeOf (shift n ij.1 ij.2))) := rfl

def principalRowVector (hd : 0 < d) (ha : 0 < a) (A : ℝ) (n : PhaseIndex d M) :
    QueryModel.Register (Coord d M) (RadialL2 d a) :=
  WithLp.toLp 2 (fun ij => (Principal.principalMinus a A n ij : ℂ) •
    radial hd ha (degreeOf (shift n ij.1 ij.2)))

theorem principalRowVector_norm (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (A : ℝ) (n : PhaseIndex d M) :
    ‖principalRowVector (by omega : 0 < d) ha A n‖ =
      ‖Principal.vector (Principal.principalMinus a A n)‖ := by
  have heq : ‖principalRowVector (by omega : 0 < d) ha A n‖ ^ 2 =
      ‖Principal.vector (Principal.principalMinus a A n)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Principal.norm_vector_sq]
    apply Finset.sum_congr rfl
    intro ij _
    change ‖(Principal.principalMinus a A n ij : ℂ) •
      radial (by omega : 0 < d) ha (degreeOf (shift n ij.1 ij.2))‖ ^ 2 = _
    rw [norm_smul, radial_norm moments hd ha, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith [norm_nonneg (principalRowVector (by omega : 0 < d) ha A n),
    norm_nonneg (Principal.vector (Principal.principalMinus a A n))]

theorem minusVector_decomposition (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (A : ℝ) (n : PhaseIndex d M) :
    minusVector (by omega : 0 < d) ha A n =
      principalRowVector (by omega : 0 < d) ha A n +
        ((cutoff A (degreeOf n) / Real.sqrt M : ℝ) : ℂ) •
          RadialEstimate.erasureRowVector moments hd ha n := by
  apply WithLp.ofLp_injective
  funext ij
  change minusVector (by omega : 0 < d) ha A n ij = _
  rw [minusVector_apply]
  change _ = (Principal.principalMinus a A n ij : ℂ) •
      radial (by omega : 0 < d) ha (degreeOf (shift n ij.1 ij.2)) +
      ((cutoff A (degreeOf n) / Real.sqrt M : ℝ) : ℂ) •
        (if n ij.1 ij.2 < 0 then
          RadialEstimate.residual moments hd ha (degDown (degreeOf n) ij.1) ij.1 else 0)
  by_cases hn : 0 ≤ n ij.1 ij.2
  · rw [degree_shift_creation n ij.1 ij.2 hn,
      sqrtMultiply_radial_creation (by omega : 0 < d) ha (degreeOf n) ij.1]
    simp only [Principal.principalMinus, hn, if_true, Principal.creationMinus,
      not_lt.mpr hn, if_false, smul_zero, add_zero, Complex.ofReal_div,
      Complex.ofReal_sub, Complex.ofReal_mul]
    module
  · have hneg : n ij.1 ij.2 < 0 := lt_of_not_ge hn
    rw [degree_shift_erasure n ij.1 ij.2 hneg,
      sqrtMultiply_down moments hd ha (degreeOf n) ij.1
        (Principal.degree_pos_of_negative n ij.1 ij.2 hneg)]
    simp only [Principal.principalMinus, hn, if_false, Principal.erasureMinus, hneg, if_true,
      Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul]
    module

/-- Paper (20), for the complete radial row, including erasure residuals. -/
theorem minusLocal_norm_le (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (A : ℝ) (hA : 0 < A) (hM : 0 < M)
    (n : PhaseIndex d M) :
    ‖minusLocal (by omega : 0 < d) ha A n‖ ≤ FullNorm.minusEnvelope a A d M := by
  rw [minusLocal, innerSL_apply_norm, minusVector_decomposition moments hd ha A n]
  have htri := norm_add_le (principalRowVector (by omega : 0 < d) ha A n)
    (((cutoff A (degreeOf n) / Real.sqrt M : ℝ) : ℂ) •
      RadialEstimate.erasureRowVector moments hd ha n)
  have hres : ‖((cutoff A (degreeOf n) / Real.sqrt M : ℝ) : ℂ) •
      RadialEstimate.erasureRowVector moments hd ha n‖ ≤ A / Real.sqrt M := by
    have hr := RadialEstimate.erasureResidualRow_paper_bound moments hd ha n A hA.le hM
    simpa only [RadialEstimate.erasureResidualRow, norm_smul, innerSL_apply_norm] using hr
  have hp := Principal.principalMinus_norm a A n ha hA (by omega : 0 < d) hM
  rw [principalRowVector_norm moments hd ha A n] at htri
  dsimp only [FullNorm.minusEnvelope, Principal.creationBound] at *
  linarith


/-- Coordinate formula for the actual erasure row, with scalar normalization
and the conjugate-linear first inner-product convention made explicit. -/
theorem minusLocal_apply (hd : 0 < d) (ha : 0 < a) (A : ℝ)
    (n : PhaseIndex d M) (h : QueryModel.Register (Coord d M) (RadialL2 d a)) :
    minusLocal hd ha A n h = ∑ ij : Coord d M,
      ((1 / Real.sqrt M : ℝ) : ℂ) *
        ((cutoff A (degreeOf n) : ℂ) *
          inner ℂ (radial hd ha (degreeOf n)) (sqrtMultiply hd ha ij.1 (h ij)) -
        ((cutoff A (degreeOf (shift n ij.1 ij.2)) / Real.sqrt d : ℝ) : ℂ) *
          inner ℂ (radial hd ha (degreeOf (shift n ij.1 ij.2))) (h ij)) := by
  change inner ℂ (minusVector hd ha A n) h = _
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro ij _
  rw [minusVector_apply, inner_smul_left, inner_sub_left, inner_smul_left,
    inner_smul_left, sqrtMultiply_inner]
  simp only [Complex.conj_ofReal]

end PUT.SectorEstimates
