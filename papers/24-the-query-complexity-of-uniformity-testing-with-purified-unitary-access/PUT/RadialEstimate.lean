import PUT.ExternalMoments
import PUT.Moments
import PUT.Radial
import PUT.Fourier
import PUT.PrincipalCoefficients
import PUT.OperatorBridge
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The actual Dirichlet radial residuals of Lemma 1

Only the standard Dirichlet joint monomial moment law is an external input.
The normalized radial weights, their posterior first and second moments,
and the residual covariance calculations are computed here on the actual
continuous Dirichlet measure. The resulting vectors live in complex `L²`.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace PUT.RadialEstimate

variable {d : ℕ} {a : ℝ}

/-- The monomial in the standard joint moment formula. -/
def monomial (k : Fin d → ℕ) (p : Fin d → ℝ) : ℝ := ∏ i, p i ^ k i

theorem monomial_up (k : Fin d → ℕ) (i : Fin d) (p : Fin d → ℝ) :
    monomial (degUp k i) p = p i * monomial k p := by
  classical
  have heq : (fun j => p j ^ degUp k i j) =
      Function.update (fun j => p j ^ k j) i (p i ^ (k i + 1)) := by
    funext j
    by_cases h : j = i
    · subst j; simp [degUp]
    · simp [degUp, h]
  unfold monomial
  rw [heq, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i)
    (fun j => p j ^ k j), pow_succ]
  ring

theorem weight_sq_eq (k : Fin d → ℕ) (p : Fin d → ℝ)
    (hp : ∀ i, 0 < p i) (ha : 0 < a) :
    weight a k p ^ 2 = monomial k p / dirMoment a k := by
  unfold weight
  rw [div_pow, Real.sq_sqrt (dirMoment_pos a k ha).le, ← Finset.prod_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.rpow_mul_natCast (hp i).le ((k i : ℝ) / 2) 2]
  norm_num only [Nat.cast_ofNat]
  have he : ((k i : ℝ) / 2) * (2 : ℝ) = k i := by ring
  rw [he, Real.rpow_natCast]

theorem measurable_weight (a : ℝ) (k : Fin d → ℕ) :
    Measurable (weight a k) := by
  unfold weight
  fun_prop

theorem postMean_pos (k : Fin d → ℕ) (i : Fin d) (ha : 0 < a) (hd : 0 < d) :
    0 < postMean a k i := by
  unfold postMean
  exact div_pos (by positivity) (postTotal_pos a k ha hd)

theorem postTotal_up (k : Fin d → ℕ) (i : Fin d) :
    postTotal a (degUp k i) = postTotal a k + 1 := by
  simp [postTotal, degK_degUp]
  ring

private theorem normalize_cov_diag (q b s : ℝ) (hb : b ^ 2 = q)
    (hb0 : b ≠ 0) (hs : s ≠ 0) :
    ((q - q * q) / s) / (b * b) = (1 - b * b) / s := by
  rw [← hb]
  field_simp [hb0, hs]
  <;> ring

private theorem normalize_cov_offdiag (qi qj bi bj s : ℝ)
    (hi : bi ^ 2 = qi) (hj : bj ^ 2 = qj)
    (hbi : bi ≠ 0) (hbj : bj ≠ 0) (hs : s ≠ 0) :
    ((0 - qi * qj) / s) / (bi * bj) = (0 - bi * bj) / s := by
  rw [← hi, ← hj]
  field_simp [hbi, hbj, hs]
  <;> ring

section Moments

variable (hMom : External.DirichletJointMomentLaw) (hd : 2 ≤ d) (ha : 0 < a)
include hMom hd ha

private theorem weight_sq_ae (k : Fin d → ℕ) :
    (fun p => weight a k p ^ 2) =ᵐ[dirichletMeasure d a]
      (fun p => monomial k p / dirMoment a k) := by
  filter_upwards [dirichletMeasure_ae_positiveSimplex (by omega : 0 < d) ha] with p hp
  exact weight_sq_eq k p hp.1 ha

/-- Squared weights are genuinely integrable and normalized. -/
theorem weighted_zero (k : Fin d → ℕ) :
    Integrable (fun p => weight a k p ^ 2) (dirichletMeasure d a) ∧
      (∫ p, weight a k p ^ 2 ∂dirichletMeasure d a) = 1 := by
  have hm := hMom d a k hd ha
  have hi : Integrable (fun p => monomial k p / dirMoment a k)
      (dirichletMeasure d a) := hm.1.div_const _
  constructor
  · exact hi.congr (weight_sq_ae hMom hd ha k).symm
  · rw [integral_congr_ae (weight_sq_ae hMom hd ha k), integral_div]
    change (∫ p, (∏ i, p i ^ k i) ∂dirichletMeasure d a) / dirMoment a k = 1
    rw [hm.2, div_self (dirMoment_ne_zero a k ha)]

/-- First moment under the density `w_k²`, derived from the external raw
joint moment law and the rising-factorial ratio, not assumed posterior data. -/
theorem weighted_first (k : Fin d → ℕ) (i : Fin d) :
    Integrable (fun p => p i * weight a k p ^ 2) (dirichletMeasure d a) ∧
      (∫ p, p i * weight a k p ^ 2 ∂dirichletMeasure d a) = postMean a k i := by
  have hm : Integrable (monomial (degUp k i)) (dirichletMeasure d a) ∧
      (∫ p, monomial (degUp k i) p ∂dirichletMeasure d a) = dirMoment a (degUp k i) :=
    hMom d a (degUp k i) hd ha
  have he : (fun p => p i * weight a k p ^ 2) =ᵐ[dirichletMeasure d a]
      (fun p => monomial (degUp k i) p / dirMoment a k) := by
    filter_upwards [weight_sq_ae hMom hd ha k] with p hp
    rw [hp, monomial_up]
    ring
  constructor
  · exact (hm.1.div_const (dirMoment a k)).congr he.symm
  · rw [integral_congr_ae he, integral_div, hm.2, dirMoment_degUp]
    change ((a + k i) / postTotal a k * dirMoment a k) / dirMoment a k = _
    rw [mul_div_cancel_right₀ _ (dirMoment_ne_zero a k ha)]
    rfl

/-- Second moment under `w_k²`, with no assumed covariance formula. -/
theorem weighted_second (k : Fin d → ℕ) (i j : Fin d) :
    Integrable (fun p => p i * p j * weight a k p ^ 2) (dirichletMeasure d a) ∧
      (∫ p, p i * p j * weight a k p ^ 2 ∂dirichletMeasure d a) =
        ((if i = j then postMean a k i else 0)
          + postTotal a k * postMean a k i * postMean a k j) /
            (postTotal a k + 1) := by
  have hm : Integrable (monomial (degUp (degUp k i) j)) (dirichletMeasure d a) ∧
      (∫ p, monomial (degUp (degUp k i) j) p ∂dirichletMeasure d a) =
        dirMoment a (degUp (degUp k i) j) :=
    hMom d a (degUp (degUp k i) j) hd ha
  have he : (fun p => p i * p j * weight a k p ^ 2) =ᵐ[dirichletMeasure d a]
      (fun p => monomial (degUp (degUp k i) j) p / dirMoment a k) := by
    filter_upwards [weight_sq_ae hMom hd ha k] with p hp
    rw [hp, monomial_up, monomial_up]
    ring
  constructor
  · exact (hm.1.div_const (dirMoment a k)).congr he.symm
  · rw [integral_congr_ae he, integral_div, hm.2, dirMoment_degUp,
      dirMoment_degUp, postTotal_up]
    have hs := (postTotal_pos a k ha (by omega : 0 < d)).ne'
    have hs1 := (postTotal_add_one_pos a k ha).ne'
    have hm0 := dirMoment_ne_zero a k ha
    by_cases hij : i = j
    · subst j
      simp only [ite_true, degUp, Function.update_self, Nat.cast_add, Nat.cast_one]
      unfold postMean
      change _ = ((a + k i) / postTotal a k +
        postTotal a k * ((a + k i) / postTotal a k) * ((a + k i) / postTotal a k)) /
          (postTotal a k + 1)
      field_simp [hs, hs1, hm0]
      <;> ring
    · have hji : j ≠ i := Ne.symm hij
      simp only [hij, ite_false, degUp, Function.update_of_ne hji]
      unfold postMean
      change _ = (0 + postTotal a k * ((a + k i) / postTotal a k) *
        ((a + k j) / postTotal a k)) / (postTotal a k + 1)
      field_simp [hs, hs1, hm0]
      <;> ring

/-- Posterior covariance as an actual integral of the centered coordinates. -/
theorem weighted_covariance (k : Fin d → ℕ) (i j : Fin d) :
    Integrable (fun p => (p i - postMean a k i) * (p j - postMean a k j) *
      weight a k p ^ 2) (dirichletMeasure d a) ∧
    (∫ p, (p i - postMean a k i) * (p j - postMean a k j) * weight a k p ^ 2
      ∂dirichletMeasure d a) =
      ((if i = j then postMean a k i else 0) -
        postMean a k i * postMean a k j) / (postTotal a k + 1) := by
  let qi := postMean a k i
  let qj := postMean a k j
  have h0 := weighted_zero hMom hd ha k
  have hi := weighted_first hMom hd ha k i
  have hj := weighted_first hMom hd ha k j
  have hij := weighted_second hMom hd ha k i j
  have he : (fun p => (p i - qi) * (p j - qj) * weight a k p ^ 2) =
      (fun p => p i * p j * weight a k p ^ 2 - qj * (p i * weight a k p ^ 2)
        - qi * (p j * weight a k p ^ 2) + (qi * qj) * weight a k p ^ 2) := by
    funext p; ring
  have hint := ((hij.1.sub (hi.1.const_mul qj)).sub (hj.1.const_mul qi)).add
    (h0.1.const_mul (qi * qj))
  constructor
  · rw [he]; exact hint
  · change (∫ p, (p i - qi) * (p j - qj) * weight a k p ^ 2
      ∂dirichletMeasure d a) = _
    have hadd := integral_add ((hij.1.sub (hi.1.const_mul qj)).sub (hj.1.const_mul qi))
      (h0.1.const_mul (qi * qj))
    have hsub₁ := integral_sub (hij.1.sub (hi.1.const_mul qj)) (hj.1.const_mul qi)
    have hsub₂ := integral_sub hij.1 (hi.1.const_mul qj)
    simp only [Pi.add_apply, Pi.sub_apply] at hadd hsub₁ hsub₂
    rw [he, hadd, hsub₁, hsub₂]
    simp only [integral_const_mul, hi.2, hj.2, h0.2, hij.2, mul_one]
    change ((if i = j then qi else 0) + postTotal a k * qi * qj) /
      (postTotal a k + 1) - qj * qi - qi * qj + qi * qj =
        ((if i = j then qi else 0) - qi * qj) / (postTotal a k + 1)
    have hs := (postTotal_add_one_pos a k ha).ne'
    field_simp [hs]
    <;> ring

/-- The real-valued residual whose complex `L²` class is used below. -/
def residualFun (a : ℝ) (k : Fin d → ℕ) (i : Fin d) (p : Fin d → ℝ) : ℝ :=
  (p i - postMean a k i) / Real.sqrt (postMean a k i) * weight a k p

/-- The Gram entries are actual integrals of the normalized residuals. -/
theorem residual_integral (k : Fin d → ℕ) (i j : Fin d) :
    (∫ p, residualFun a k i p * residualFun a k j p ∂dirichletMeasure d a) =
      ((if i = j then 1 else 0) -
        Real.sqrt (postMean a k i) * Real.sqrt (postMean a k j)) /
          (postTotal a k + 1) := by
  have hcov := weighted_covariance hMom hd ha k i j
  have hqi := postMean_pos k i ha (by omega : 0 < d)
  have hqj := postMean_pos k j ha (by omega : 0 < d)
  have hbi := (Real.sqrt_pos.mpr hqi).ne'
  have hbj := (Real.sqrt_pos.mpr hqj).ne'
  have hs := (postTotal_add_one_pos a k ha).ne'
  have he : (fun p => residualFun a k i p * residualFun a k j p) =
      (fun p => ((p i - postMean a k i) * (p j - postMean a k j) * weight a k p ^ 2) /
        (Real.sqrt (postMean a k i) * Real.sqrt (postMean a k j))) := by
    funext p; unfold residualFun; ring
  rw [he, integral_div, hcov.2]
  have hi : Real.sqrt (postMean a k i) ^ 2 = postMean a k i := Real.sq_sqrt hqi.le
  have hj : Real.sqrt (postMean a k j) ^ 2 = postMean a k j := Real.sq_sqrt hqj.le
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    exact normalize_cov_diag (postMean a k i) (Real.sqrt (postMean a k i))
      (postTotal a k + 1) hi hbi hs
  · simp only [hij, ite_false]
    exact normalize_cov_offdiag (postMean a k i) (postMean a k j)
      (Real.sqrt (postMean a k i)) (Real.sqrt (postMean a k j))
      (postTotal a k + 1) hi hj hbi hbj hs

/-- The real residual is genuinely square integrable. -/
theorem residual_memLp (k : Fin d → ℕ) (i : Fin d) :
    MemLp (residualFun a k i) 2 (dirichletMeasure d a) := by
  apply (memLp_two_iff_integrable_sq (by
    unfold residualFun
    exact ((measurable_pi_apply i).sub measurable_const |>.div_const _ |>.mul
      (measurable_weight a k)).aestronglyMeasurable)).mpr
  have h := (weighted_covariance hMom hd ha k i i).1.div_const
    (Real.sqrt (postMean a k i) ^ 2)
  convert h using 1
  funext p
  unfold residualFun
  ring

/-- The paper's radial residual as an actual element of complex `L²(μ_a)`. -/
def residual (k : Fin d → ℕ) (i : Fin d) :
    Lp ℂ 2 (dirichletMeasure d a) :=
  (residual_memLp hMom hd ha k i).ofReal.toLp (fun p => (residualFun a k i p : ℂ))

/-- Exact complex Gram identity (16), with the concrete Dirichlet residuals. -/
theorem residual_gram (k : Fin d → ℕ) (i j : Fin d) :
    inner ℂ (residual hMom hd ha k i) (residual hMom hd ha k j) =
      ((if i = j then 1 else 0) -
        (Real.sqrt (postMean a k i) : ℂ) * star (Real.sqrt (postMean a k j) : ℂ)) /
          ((postTotal a k + 1 : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have hei : residual hMom hd ha k i =ᵐ[dirichletMeasure d a]
      (fun p => (residualFun a k i p : ℂ)) :=
    MemLp.coeFn_toLp (residual_memLp hMom hd ha k i).ofReal
  have hej : residual hMom hd ha k j =ᵐ[dirichletMeasure d a]
      (fun p => (residualFun a k j p : ℂ)) :=
    MemLp.coeFn_toLp (residual_memLp hMom hd ha k j).ofReal
  have he : (fun p => inner ℂ (residual hMom hd ha k i p) (residual hMom hd ha k j p))
      =ᵐ[dirichletMeasure d a]
      (fun p => ((residualFun a k i p * residualFun a k j p : ℝ) : ℂ)) := by
    filter_upwards [hei, hej] with p hi hj
    change inner ℂ ((residual hMom hd ha k i) p) ((residual hMom hd ha k j) p) = _
    rw [hi, hj]
    simp [RCLike.inner_apply, mul_comm]
  rw [integral_congr_ae he, integral_complex_ofReal, residual_integral hMom hd ha k i j]
  norm_cast
  split_ifs <;> simp [*]

/-- The genuine analysis-map norm bound used for the creation residuals. -/
theorem radial_plus_analysis_bound (k : Fin d → ℕ) :
    ‖OperatorBridge.radialAnalysis (residual hMom hd ha k)‖ ≤
      1 / Real.sqrt (postTotal a k + 1) := by
  let b : EuclideanSpace ℂ (Fin d) :=
    WithLp.toLp 2 (fun i => (Real.sqrt (postMean a k i) : ℂ))
  apply OperatorBridge.norm_radialAnalysis_le_of_gram (residual hMom hd ha k) b
    (postTotal a k + 1) (postTotal_add_one_pos a k ha)
  intro i j
  exact residual_gram hMom hd ha k i j

/-- The concrete radial weight belongs to the actual real L² space. -/
theorem weight_memLp (k : Fin d → ℕ) :
    MemLp (weight a k) 2 (dirichletMeasure d a) := by
  exact (memLp_two_iff_integrable_sq (measurable_weight a k).aestronglyMeasurable).mpr
    (weighted_zero hMom hd ha k).1

/-- The normalized moment vector `w_k` as a genuine complex L² vector. -/
def normalizedWeight (k : Fin d → ℕ) : Lp ℂ 2 (dirichletMeasure d a) :=
  (weight_memLp hMom hd ha k).ofReal.toLp (fun p => (weight a k p : ℂ))

theorem normalizedWeight_inner_self (k : Fin d → ℕ) :
    inner ℂ (normalizedWeight hMom hd ha k) (normalizedWeight hMom hd ha k) = 1 := by
  rw [L2.inner_def]
  have hw : normalizedWeight hMom hd ha k =ᵐ[dirichletMeasure d a]
      (fun p => (weight a k p : ℂ)) :=
    MemLp.coeFn_toLp (weight_memLp hMom hd ha k).ofReal
  have he : (fun p => inner ℂ ((normalizedWeight hMom hd ha k) p)
      ((normalizedWeight hMom hd ha k) p)) =ᵐ[dirichletMeasure d a]
      (fun p => ((weight a k p ^ 2 : ℝ) : ℂ)) := by
    filter_upwards [hw] with p hp
    rw [hp]
    simp [RCLike.inner_apply, pow_two]
  rw [integral_congr_ae he, integral_complex_ofReal, (weighted_zero hMom hd ha k).2]
  simp

theorem normalizedWeight_norm (k : Fin d → ℕ) :
    ‖normalizedWeight hMom hd ha k‖ = 1 := by
  have h : ‖normalizedWeight hMom hd ha k‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), normalizedWeight_inner_self hMom hd ha k]
    rfl
  nlinarith [norm_nonneg (normalizedWeight hMom hd ha k)]

/-- Residuals are orthogonal to the normalized radial moment vector. -/
theorem residual_orthogonal_weight (k : Fin d → ℕ) (i : Fin d) :
    inner ℂ (residual hMom hd ha k i) (normalizedWeight hMom hd ha k) = 0 := by
  rw [L2.inner_def]
  have hr : residual hMom hd ha k i =ᵐ[dirichletMeasure d a]
      (fun p => (residualFun a k i p : ℂ)) :=
    MemLp.coeFn_toLp (residual_memLp hMom hd ha k i).ofReal
  have hw : normalizedWeight hMom hd ha k =ᵐ[dirichletMeasure d a]
      (fun p => (weight a k p : ℂ)) :=
    MemLp.coeFn_toLp (weight_memLp hMom hd ha k).ofReal
  have he : (fun p => inner ℂ ((residual hMom hd ha k i) p)
      ((normalizedWeight hMom hd ha k) p)) =ᵐ[dirichletMeasure d a]
      (fun p => (((p i * weight a k p ^ 2 - postMean a k i * weight a k p ^ 2) /
        Real.sqrt (postMean a k i) : ℝ) : ℂ)) := by
    filter_upwards [hr, hw] with p hp hwp
    rw [hp, hwp]
    simp only [RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    unfold residualFun
    ring
  rw [integral_congr_ae he, integral_complex_ofReal, integral_div]
  have h0 := weighted_zero hMom hd ha k
  have hi := weighted_first hMom hd ha k i
  have hsub := integral_sub hi.1 (h0.1.const_mul (postMean a k i))
  simp only [Pi.sub_apply] at hsub
  rw [hsub, integral_const_mul, hi.2, h0.2]
  simp

/-- The diagonal of the actual Gram matrix computes each residual norm. -/
theorem residual_norm_sq (k : Fin d → ℕ) (i : Fin d) :
    ‖residual hMom hd ha k i‖ ^ 2 =
      (1 - postMean a k i) / (postTotal a k + 1) := by
  have hq := postMean_pos k i ha (by omega : 0 < d)
  have he : inner ℂ (residual hMom hd ha k i) (residual hMom hd ha k i) =
      (((1 - postMean a k i) / (postTotal a k + 1) : ℝ) : ℂ) := by
    rw [residual_gram hMom hd ha k i i]
    simp only [ite_true, Complex.star_def, Complex.conj_ofReal]
    norm_cast
    rw [← sq, Real.sq_sqrt hq.le]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), he]
  rfl

/-- Removing one positive label degree removes exactly one from the total. -/
theorem postTotal_down_add_one (k : Fin d → ℕ) (i : Fin d) (hi : 0 < k i) :
    postTotal a (degDown k i) + 1 = postTotal a k := by
  unfold postTotal
  rw [degK_degDown k i hi, Nat.cast_sub (one_le_degK_of_pos hi)]
  push_cast
  ring

/-- The mean in the preceding posterior is the paper's `q_i^-`. -/
theorem postMean_down (k : Fin d → ℕ) (i : Fin d) (hi : 0 < k i) :
    postMean a (degDown k i) i = postMeanMinus a k i := by
  unfold postMean postMeanMinus
  rw [degK_degDown k i hi]
  simp only [degDown, Function.update_self]
  rw [Nat.cast_sub (by omega : 1 ≤ k i), Nat.cast_sub (one_le_degK_of_pos hi)]
  push_cast
  ring

/-- The paper's `s_i` is the residual of the preceding Dirichlet posterior,
so its exact norm is computed rather than postulated. -/
theorem erasure_residual_norm_sq (k : Fin d → ℕ) (i : Fin d) (hi : 0 < k i) :
    ‖residual hMom hd ha (degDown k i) i‖ ^ 2 =
      (1 - postMeanMinus a k i) / postTotal a k := by
  rw [residual_norm_sq hMom hd ha, postTotal_down_add_one hMom hd ha k i hi,
    postMean_down hMom hd ha k i hi]

/-- The exact erasure residual norm is at most `1/(ad+K)`. -/
theorem erasure_residual_norm_sq_le (k : Fin d → ℕ) (i : Fin d) (hi : 0 < k i) :
    ‖residual hMom hd ha (degDown k i) i‖ ^ 2 ≤ 1 / postTotal a k := by
  rw [erasure_residual_norm_sq hMom hd ha k i hi]
  have hq : 0 ≤ postMeanMinus a k i := by
    rw [← postMean_down hMom hd ha k i hi]
    exact (postMean_pos (degDown k i) i ha (by omega : 0 < d)).le
  exact div_le_div_of_nonneg_right (by linarith) (postTotal_pos a k ha (by omega : 0 < d)).le

/-- The actual creation output on the radial complement, with all query
coordinates and the source cutoff weights retained. -/
def creationResidualMap {M : ℕ} (n : PhaseIndex d M) (A : ℝ) :
    Lp ℂ 2 (dirichletMeasure d a) →L[ℂ] EuclideanSpace ℂ (Fin d × Fin M) :=
  (EuclideanSpace.equiv (Fin d × Fin M) ℂ).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun ij =>
      (if 0 ≤ n ij.1 ij.2 then
        ((cutoff A (degUp (degreeOf n) ij.1) / Real.sqrt M : ℝ) : ℂ)
      else 0) • innerSL ℂ (residual hMom hd ha (degreeOf n) ij.1))

@[simp] theorem creationResidualMap_apply {M : ℕ} (n : PhaseIndex d M) (A : ℝ)
    (x : Lp ℂ 2 (dirichletMeasure d a)) (ij : Fin d × Fin M) :
    creationResidualMap hMom hd ha n A x ij =
      (if 0 ≤ n ij.1 ij.2 then
        ((cutoff A (degUp (degreeOf n) ij.1) / Real.sqrt M : ℝ) : ℂ)
      else 0) * inner ℂ (residual hMom hd ha (degreeOf n) ij.1) x := rfl

/-- The weighted creation norm estimate, before replacing `S+1` by `ad`.
This is an actual operator bound, including every masked query coordinate. -/
theorem creationResidualMap_norm_le {M : ℕ} (n : PhaseIndex d M) (A : ℝ)
    (hA : 0 ≤ A) (hM : 0 < M) :
    ‖creationResidualMap hMom hd ha n A‖ ≤
      A / Real.sqrt (postTotal a (degreeOf n) + 1) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hcoord (i : Fin d) (j : Fin M) :
      ‖creationResidualMap hMom hd ha n A x (i, j)‖ ^ 2 ≤
        (A ^ 2 / M) * ‖inner ℂ (residual hMom hd ha (degreeOf n) i) x‖ ^ 2 := by
    rw [creationResidualMap_apply]
    by_cases hn : 0 ≤ n i j
    · rw [if_pos hn, norm_mul, mul_pow]
      have hc := cutoff_le_of_nonneg hA (degUp (degreeOf n) i)
      have hc2 : cutoff A (degUp (degreeOf n) i) ^ 2 ≤ A ^ 2 :=
        pow_le_pow_left₀ (cutoff_nonneg _ _) hc 2
      have hcn : ‖((cutoff A (degUp (degreeOf n) i) / Real.sqrt M : ℝ) : ℂ)‖ ^ 2 =
          cutoff A (degUp (degreeOf n) i) ^ 2 / M := by
        simp [Complex.norm_real, Real.norm_eq_abs, div_pow, Real.sq_sqrt hMr.le]
      rw [hcn]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hc2 hMr.le) (sq_nonneg _)
    · simp only [if_neg hn, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      positivity
  have hsum : ‖creationResidualMap hMom hd ha n A x‖ ^ 2 ≤
      A ^ 2 * ‖OperatorBridge.radialAnalysis (residual hMom hd ha (degreeOf n)) x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    calc
      _ ≤ ∑ i : Fin d, ∑ j : Fin M,
          (A ^ 2 / M) * ‖inner ℂ (residual hMom hd ha (degreeOf n) i) x‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcoord i j
      _ = A ^ 2 * ∑ i : Fin d,
          ‖inner ℂ (residual hMom hd ha (degreeOf n) i) x‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        field_simp [hMr.ne']
      _ = _ := by
        rw [EuclideanSpace.norm_sq_eq]
        simp only [OperatorBridge.radialAnalysis_apply]
  have hana := (OperatorBridge.radialAnalysis (residual hMom hd ha (degreeOf n))).le_of_opNorm_le
    (radial_plus_analysis_bound hMom hd ha (degreeOf n)) x
  have hana2 := pow_le_pow_left₀ (norm_nonneg _) hana 2
  have hfinal : ‖creationResidualMap hMom hd ha n A x‖ ^ 2 ≤
      ((A / Real.sqrt (postTotal a (degreeOf n) + 1)) * ‖x‖) ^ 2 := by
    calc
      _ ≤ A ^ 2 * ‖OperatorBridge.radialAnalysis (residual hMom hd ha (degreeOf n)) x‖ ^ 2 := hsum
      _ ≤ A ^ 2 * ((1 / Real.sqrt (postTotal a (degreeOf n) + 1)) * ‖x‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hana2 (sq_nonneg A)
      _ = _ := by ring
  exact le_of_sq_le_sq hfinal (by positivity)

/-- The actual sector creation residual obeys the paper's `A/√(ad)` bound. -/
theorem creationResidualMap_paper_bound {M : ℕ} (n : PhaseIndex d M) (A : ℝ)
    (hA : 0 ≤ A) (hM : 0 < M) :
    ‖creationResidualMap hMom hd ha n A‖ ≤ A / Real.sqrt (a * d) := by
  have had : 0 < a * (d : ℝ) := mul_pos ha (by exact_mod_cast (by omega : 0 < d))
  have hS : a * (d : ℝ) ≤ postTotal a (degreeOf n) + 1 := by
    unfold postTotal
    have hknn : (0 : ℝ) ≤ (degK (degreeOf n) : ℝ) := Nat.cast_nonneg _
    linarith
  exact (creationResidualMap_norm_le hMom hd ha n A hA hM).trans
    (div_le_div_of_nonneg_left hA (Real.sqrt_pos.mpr had) (Real.sqrt_le_sqrt hS))

/-- The full erasure row vector; its coordinates are genuine L² residuals
in orthogonal query input blocks, with the negative-coordinate mask retained. -/
def erasureRowVector {M : ℕ} (n : PhaseIndex d M) :
    PiLp 2 (fun _ : Fin d × Fin M => Lp ℂ 2 (dirichletMeasure d a)) :=
  WithLp.toLp 2 (fun ij => if n ij.1 ij.2 < 0 then
    residual hMom hd ha (degDown (degreeOf n) ij.1) ij.1 else 0)

/-- The paper's row is the actual bounded functional against this direct-sum
vector, scaled by `α(k)/√M`. -/
def erasureResidualRow {M : ℕ} (n : PhaseIndex d M) (A : ℝ) :
    PiLp 2 (fun _ : Fin d × Fin M => Lp ℂ 2 (dirichletMeasure d a)) →L[ℂ] ℂ :=
  ((cutoff A (degreeOf n) / Real.sqrt M : ℝ) : ℂ) •
    innerSL ℂ (erasureRowVector hMom hd ha n)

/-- Counting negative coordinates is combined with their actual residual
norms, giving the `K/S` row-vector estimate. -/
theorem erasureRowVector_norm_sq_le {M : ℕ} (n : PhaseIndex d M) :
    ‖erasureRowVector hMom hd ha n‖ ^ 2 ≤
      (degK (degreeOf n) : ℝ) / postTotal a (degreeOf n) := by
  rw [PiLp.norm_sq_eq_of_L2]
  have hcoord (ij : Fin d × Fin M) :
      ‖erasureRowVector hMom hd ha n ij‖ ^ 2 ≤
        (if n ij.1 ij.2 < 0 then (1 : ℝ) else 0) / postTotal a (degreeOf n) := by
    change ‖(if n ij.1 ij.2 < 0 then
      residual hMom hd ha (degDown (degreeOf n) ij.1) ij.1 else 0)‖ ^ 2 ≤ _
    by_cases hn : n ij.1 ij.2 < 0
    · rw [if_pos hn, if_pos hn]
      exact erasure_residual_norm_sq_le hMom hd ha (degreeOf n) ij.1
        (Principal.degree_pos_of_negative n ij.1 ij.2 hn)
    · simp [hn]
  calc
    _ ≤ ∑ ij : Fin d × Fin M,
        (if n ij.1 ij.2 < 0 then (1 : ℝ) else 0) / postTotal a (degreeOf n) :=
      Finset.sum_le_sum fun ij _ => hcoord ij
    _ = (∑ ij : Fin d × Fin M, if n ij.1 ij.2 < 0 then (1 : ℝ) else 0) /
        postTotal a (degreeOf n) := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (Principal.negativeCount_le_degree n)
      (postTotal_pos a (degreeOf n) ha (by omega : 0 < d)).le

/-- The actual erasure row, including its `K/M` dependence, obeys the
squared estimate derived in paper (18). -/
theorem erasureResidualRow_norm_sq_le {M : ℕ} (n : PhaseIndex d M) (A : ℝ)
    (hA : 0 ≤ A) (hM : 0 < M) :
    ‖erasureResidualRow hMom hd ha n A‖ ^ 2 ≤
      (A ^ 2 / M) * ((degK (degreeOf n) : ℝ) / postTotal a (degreeOf n)) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have he : ‖erasureResidualRow hMom hd ha n A‖ ^ 2 =
      (cutoff A (degreeOf n) ^ 2 / M) * ‖erasureRowVector hMom hd ha n‖ ^ 2 := by
    unfold erasureResidualRow
    rw [norm_smul, innerSL_apply_norm, mul_pow]
    simp [Complex.norm_real, Real.norm_eq_abs, div_pow, Real.sq_sqrt hMr.le]
  rw [he]
  have hc : cutoff A (degreeOf n) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (cutoff_nonneg _ _) (cutoff_le_of_nonneg hA _) 2
  exact mul_le_mul
    (div_le_div_of_nonneg_right hc hMr.le)
    (erasureRowVector_norm_sq_le hMom hd ha n)
    (sq_nonneg _) (by positivity)

/-- The full actual erasure residual row is at most `A/√M`. -/
theorem erasureResidualRow_paper_bound {M : ℕ} (n : PhaseIndex d M) (A : ℝ)
    (hA : 0 ≤ A) (hM : 0 < M) :
    ‖erasureResidualRow hMom hd ha n A‖ ≤ A / Real.sqrt M := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hS := postTotal_pos a (degreeOf n) ha (by omega : 0 < d)
  have hKS : (degK (degreeOf n) : ℝ) / postTotal a (degreeOf n) ≤ 1 := by
    apply (div_le_one hS).mpr
    unfold postTotal
    have had : 0 ≤ a * (d : ℝ) := by positivity
    linarith
  have hsq : ‖erasureResidualRow hMom hd ha n A‖ ^ 2 ≤ (A / Real.sqrt M) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hMr.le]
    exact (erasureResidualRow_norm_sq_le hMom hd ha n A hA hM).trans
      (by simpa using mul_le_mul_of_nonneg_left hKS (by positivity : 0 ≤ A ^ 2 / (M : ℝ)))
  exact le_of_sq_le_sq hsq (by positivity)

end Moments

end PUT.RadialEstimate
