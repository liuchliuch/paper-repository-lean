import Paper38.GaussianEnergy
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Genuine Fréchet differentiation of the actual Gaussian potential average. -/
noncomputable section
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal Matrix Matrix.Norms.Frobenius

namespace Paper38.GaussianDifferentiation
open Paper38.Model Paper38.GaussianCoupling Paper38.GaussianEnergy

variable {d : ℕ}

-- Explicit type annotation avoids a higher-order typeclass elaboration ambiguity
-- for the norm topology on the twice-curried differential space.
local instance secondDifferential_continuousENorm (d : ℕ) :
    ContinuousENorm (Coordinates d →L[ℝ] Coordinates d →L[ℝ] ℝ) :=
  @SeminormedAddGroup.toContinuousENorm (Coordinates d →L[ℝ] Coordinates d →L[ℝ] ℝ)
    (inferInstance : SeminormedAddGroup (Coordinates d →L[ℝ] Coordinates d →L[ℝ] ℝ))

local instance (d : ℕ) : IsProbabilityMeasure (standardGaussian d) :=
  GaussianCoupling.standardGaussian_probability d

/-- Matrix action, promoted using finite-dimensional continuity. -/
def matrixAction (d : ℕ) : Mat d →L[ℝ] E d →L[ℝ] E d :=
  (((LinearMap.toContinuousLinearMap : (E d →ₗ[ℝ] E d) ≃ₗ[ℝ] (E d →L[ℝ] E d)).toLinearMap).comp
    (Matrix.toEuclideanLin : Mat d ≃ₗ[ℝ] (E d →ₗ[ℝ] E d)).toLinearMap).toContinuousLinearMap

@[simp] lemma matrixAction_apply (A : Mat d) (z : E d) :
    matrixAction d A z = matVec A z := rfl

/-- Evaluation at the common standard Gaussian variable is linear in `(μ,A)`. -/
def evaluation (z : E d) : Coordinates d →L[ℝ] E d :=
  ContinuousLinearMap.fst ℝ (E d) (Mat d) +
    ((matrixAction d).flip z).comp (ContinuousLinearMap.snd ℝ (E d) (Mat d))

@[simp] lemma evaluation_apply (z : E d) (q : Coordinates d) :
    evaluation z q = q.1 + matVec q.2 z := rfl

lemma evaluation_continuous : Continuous (evaluation : E d → Coordinates d →L[ℝ] E d) := by
  unfold evaluation
  fun_prop

lemma evaluation_norm_bound (z : E d) : ‖evaluation z‖ ≤ 1 + ‖(matrixAction d).flip‖ * ‖z‖ := by
  unfold evaluation
  calc
    ‖ContinuousLinearMap.fst ℝ (E d) (Mat d) +
      ((matrixAction d).flip z).comp (ContinuousLinearMap.snd ℝ (E d) (Mat d))‖ ≤
        ‖ContinuousLinearMap.fst ℝ (E d) (Mat d)‖ +
          ‖((matrixAction d).flip z).comp (ContinuousLinearMap.snd ℝ (E d) (Mat d))‖ := norm_add_le _ _
    _ ≤ 1 + ‖(matrixAction d).flip‖ * ‖z‖ := by
      have hf := ContinuousLinearMap.norm_fst_le ℝ (E d) (Mat d)
      have hs := ContinuousLinearMap.norm_snd_le ℝ (E d) (Mat d)
      have hc := ContinuousLinearMap.opNorm_comp_le ((matrixAction d).flip z)
        (ContinuousLinearMap.snd ℝ (E d) (Mat d))
      have hz := (matrixAction d).flip.le_opNorm z
      have hprod := mul_le_mul_of_nonneg_left hs (norm_nonneg ((matrixAction d).flip z))
      nlinarith

lemma evaluation_norm_sq_integrable :
    Integrable (fun z : E d => ‖evaluation z‖ ^ 2) (standardGaussian d) := by
  have hz : Integrable (fun z : E d => ‖z‖ ^ 2) (standardGaussian d) := by
    simpa [matVec, vec, Matrix.mulVec, dotProduct] using
      affine_norm_sq_integrable (0 : E d) (1 : Mat d)
  let K := ‖(matrixAction d).flip‖
  have hb : Integrable (fun z : E d => 2 + 2 * K ^ 2 * ‖z‖ ^ 2) (standardGaussian d) :=
    (integrable_const 2).add (hz.const_mul (2 * K ^ 2))
  apply hb.mono' (evaluation_continuous.norm.pow 2).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := evaluation_norm_bound z
  have hn : 0 ≤ ‖evaluation z‖ := norm_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  change ‖evaluation z‖ ^ 2 ≤ 2 + 2 * K ^ 2 * ‖z‖ ^ 2
  change ‖evaluation z‖ ≤ 1 + K * ‖z‖ at h
  nlinarith [sq_nonneg (1 - K * ‖z‖)]

/-- The genuine expected-potential component of `Model.energy`. -/
def potentialAverage (V : E d → ℝ) (q : Coordinates d) : ℝ :=
  ∫ z, V (evaluation z q) ∂standardGaussian d

/-- Pointwise differential before integration. -/
def integrandDifferential (V : E d → ℝ) (q : Coordinates d) (z : E d) :
    Coordinates d →L[ℝ] ℝ := (fderiv ℝ V (evaluation z q)).comp (evaluation z)

lemma potential_integrand_hasFDerivAt {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (q : Coordinates d) (z : E d) :
    HasFDerivAt (fun p : Coordinates d => V (evaluation z p))
      (integrandDifferential V q z) q := by
  exact (hV.regularity.differentiable (by norm_num) (evaluation z q)).hasFDerivAt.comp q
    (evaluation z).hasFDerivAt

lemma differential_integrand_continuous {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (q : Coordinates d) :
    Continuous (integrandDifferential V q) := by
  exact ((hV.regularity.continuous_fderiv (by norm_num)).comp
    (evaluation_continuous.clm_apply continuous_const)).clm_comp evaluation_continuous

lemma differential_integrand_norm_bound {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (q₀ q : Coordinates d) (hq : q ∈ Metric.ball q₀ 1)
    (z : E d) :
    ‖integrandDifferential V q z‖ ≤ ‖fderiv ℝ V 0‖ +
      (‖fderiv ℝ V 0‖ + 2 * β * (‖q₀‖ + 1)) * ‖evaluation z‖ ^ 2 := by
  have hβ : 0 ≤ β := hV.alpha_pos.le.trans hV.alpha_le_beta
  have hdist : ‖q - q₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hq
  have hqnorm : ‖q‖ ≤ ‖q₀‖ + 1 := by linarith [norm_le_norm_sub_add q q₀]
  have hL := (evaluation z).le_opNorm q
  have hL' := mul_le_mul_of_nonneg_left hqnorm (norm_nonneg (evaluation z))
  have hgrowth := PotentialBounds.fderiv_linear_growth hV (evaluation z q)
  have hcomp : ‖integrandDifferential V q z‖ ≤
      ‖fderiv ℝ V (evaluation z q)‖ * ‖evaluation z‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have heval : ‖evaluation z‖ ≤ 1 + ‖evaluation z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖evaluation z‖ - 1)]
  have hg := mul_le_mul_of_nonneg_right hgrowth (norm_nonneg (evaluation z))
  have hβL := mul_nonneg (mul_nonneg hβ (norm_nonneg (evaluation z)))
    (show 0 ≤ ‖evaluation z‖ * (‖q₀‖ + 1) - ‖evaluation z q‖ by linarith)
  have hg0 := mul_le_mul_of_nonneg_left heval (norm_nonneg (fderiv ℝ V 0))
  nlinarith

lemma differential_integrand_integrable {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (q : Coordinates d) :
    Integrable (integrandDifferential V q) (standardGaussian d) := by
  have hb : Integrable (fun z : E d => ‖fderiv ℝ V 0‖ +
      (‖fderiv ℝ V 0‖ + 2 * β * (‖q‖ + 1)) * ‖evaluation z‖ ^ 2) (standardGaussian d) :=
    (integrable_const _).add (evaluation_norm_sq_integrable.const_mul _)
  apply hb.mono' (differential_integrand_continuous hV q).aestronglyMeasurable
  filter_upwards [] with z
  exact differential_integrand_norm_bound hV q q (Metric.mem_ball_self (by norm_num)) z

/-- The actual first Fréchet variation of the Gaussian potential average.
Every domination and integrability premise is proved from the original source hypotheses. -/
lemma potentialAverage_hasFDerivAt {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (q : Coordinates d) :
    HasFDerivAt (potentialAverage V)
      (∫ z, integrandDifferential V q z ∂standardGaussian d) q := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p z => V (evaluation z p)) (F' := integrandDifferential V)
    (bound := fun z => ‖fderiv ℝ V 0‖ +
      (‖fderiv ℝ V 0‖ + 2 * β * (‖q‖ + 1)) * ‖evaluation z‖ ^ 2) (ε := 1) (by norm_num)
  · exact Filter.Eventually.of_forall (fun p =>
      (hV.regularity.continuous.comp (evaluation_continuous.clm_apply continuous_const)).aestronglyMeasurable)
  · exact potential_integrable hV q.1 q.2
  · exact (differential_integrand_continuous hV q).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z p hp => differential_integrand_norm_bound hV q p hp z)
  · exact (integrable_const _).add (evaluation_norm_sq_integrable.const_mul _)
  · exact Filter.Eventually.of_forall (fun z p _ => potential_integrand_hasFDerivAt hV p z)

lemma potentialAverage_fderiv {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (q : Coordinates d) :
    fderiv ℝ (potentialAverage V) q = ∫ z, integrandDifferential V q z ∂standardGaussian d :=
  (potentialAverage_hasFDerivAt hV q).fderiv

lemma potentialAverage_first_variation {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (q w : Coordinates d) :
    fderiv ℝ (potentialAverage V) q w =
      ∫ z, (fderiv ℝ V (q.1 + matVec q.2 z)) (w.1 + matVec w.2 z) ∂standardGaussian d := by
  rw [potentialAverage_fderiv hV]
  exact ContinuousLinearMap.integral_apply (differential_integrand_integrable hV q) w

/-- Pointwise second differential of the actual potential integrand. -/
def integrandSecondDifferential (V : E d → ℝ) (q : Coordinates d) (z : E d) :
    Coordinates d →L[ℝ] Coordinates d →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (Coordinates d) (E d) ℝ).flip (evaluation z)).comp
    ((fderiv ℝ (fderiv ℝ V) (evaluation z q)).comp (evaluation z))

@[simp] lemma integrandSecondDifferential_apply (V : E d → ℝ) (q u w : Coordinates d) (z : E d) :
    integrandSecondDifferential V q z u w =
      (fderiv ℝ (fderiv ℝ V) (evaluation z q) (evaluation z u)) (evaluation z w) := rfl

lemma differential_integrand_hasFDerivAt {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (q : Coordinates d) (z : E d) :
    HasFDerivAt (fun p => integrandDifferential V p z)
      (integrandSecondDifferential V q z) q := by
  have h₁ : ContDiff ℝ 1 (fderiv ℝ V) := hV.regularity.fderiv_right (by norm_num)
  have hd : HasFDerivAt (fun p : Coordinates d => fderiv ℝ V (evaluation z p))
      ((fderiv ℝ (fderiv ℝ V) (evaluation z q)).comp (evaluation z)) q :=
    (h₁.differentiable (by norm_num) (evaluation z q)).hasFDerivAt.comp q (evaluation z).hasFDerivAt
  have hconst : HasFDerivAt (fun _ : Coordinates d => evaluation z)
      (0 : Coordinates d →L[ℝ] Coordinates d →L[ℝ] E d) q := hasFDerivAt_const (evaluation z) q
  simpa [integrandDifferential, integrandSecondDifferential] using hd.clm_comp hconst

lemma second_integrand_continuous_z {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (q : Coordinates d) :
    Continuous (integrandSecondDifferential V q) := by
  have h₁ : ContDiff ℝ 1 (fderiv ℝ V) := hV.regularity.fderiv_right (by norm_num)
  have h₂ := h₁.continuous_fderiv (by norm_num)
  have hpre : Continuous (fun z : E d =>
      (ContinuousLinearMap.compL ℝ (Coordinates d) (E d) ℝ).flip (evaluation z)) :=
    (ContinuousLinearMap.compL ℝ (Coordinates d) (E d) ℝ).flip.continuous.comp evaluation_continuous
  have hinner := (h₂.comp (evaluation_continuous.clm_apply (continuous_const : Continuous (fun _ : E d => q)))).clm_comp evaluation_continuous
  exact hpre.clm_comp hinner

lemma second_integrand_continuous_q {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (z : E d) :
    Continuous (fun q : Coordinates d => integrandSecondDifferential V q z) := by
  have h₁ : ContDiff ℝ 1 (fderiv ℝ V) := hV.regularity.fderiv_right (by norm_num)
  have h₂ := h₁.continuous_fderiv (by norm_num)
  unfold integrandSecondDifferential
  fun_prop

lemma second_integrand_norm_bound {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (q : Coordinates d) (z : E d) :
    ‖integrandSecondDifferential V q z‖ ≤ 2 * β * ‖evaluation z‖ ^ 2 := by
  have hβ : 0 ≤ β := hV.alpha_pos.le.trans hV.alpha_le_beta
  have hc := ContinuousLinearMap.opNorm_comp_le
    ((ContinuousLinearMap.compL ℝ (Coordinates d) (E d) ℝ).flip (evaluation z))
    ((fderiv ℝ (fderiv ℝ V) (evaluation z q)).comp (evaluation z))
  have hc' := ContinuousLinearMap.opNorm_comp_le
    (fderiv ℝ (fderiv ℝ V) (evaluation z q)) (evaluation z)
  have hflip := (ContinuousLinearMap.compL ℝ (Coordinates d) (E d) ℝ).flip.le_opNorm (evaluation z)
  have hnorm : ‖(ContinuousLinearMap.compL ℝ (Coordinates d) (E d) ℝ).flip‖ ≤ 1 := by
    simpa using ContinuousLinearMap.norm_compL_le (𝕜 := ℝ) (E := Coordinates d) (Fₗ := E d) (Gₗ := ℝ)
  have hpre : ‖(ContinuousLinearMap.compL ℝ (Coordinates d) (E d) ℝ).flip (evaluation z)‖ ≤ ‖evaluation z‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hnorm (norm_nonneg (evaluation z))]
  have hH := PotentialBounds.hessian_opNorm_bound hV (evaluation z q)
  have hinner : ‖(fderiv ℝ (fderiv ℝ V) (evaluation z q)).comp (evaluation z)‖ ≤ 2 * β * ‖evaluation z‖ := by
    exact hc'.trans (mul_le_mul_of_nonneg_right hH (norm_nonneg (evaluation z)))
  calc
    ‖integrandSecondDifferential V q z‖ ≤
      ‖(ContinuousLinearMap.compL ℝ (Coordinates d) (E d) ℝ).flip (evaluation z)‖ *
        ‖(fderiv ℝ (fderiv ℝ V) (evaluation z q)).comp (evaluation z)‖ := hc
    _ ≤ ‖evaluation z‖ * (2 * β * ‖evaluation z‖) :=
      mul_le_mul hpre hinner
        (norm_nonneg ((fderiv ℝ (fderiv ℝ V) (evaluation z q)).comp (evaluation z)))
        (norm_nonneg (evaluation z))
    _ = _ := by ring

lemma second_integrand_integrable {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (q : Coordinates d) :
    Integrable (integrandSecondDifferential V q) (standardGaussian d) := by
  exact Integrable.mono' (β := Coordinates d →L[ℝ] Coordinates d →L[ℝ] ℝ)
    (f := integrandSecondDifferential V q)
    (evaluation_norm_sq_integrable.const_mul (2 * β))
    (second_integrand_continuous_z hV q).aestronglyMeasurable
    (Filter.Eventually.of_forall (second_integrand_norm_bound hV q))

/-- Fréchet differentiation under the integral a second time, with the
original bounded continuous Hessian providing all domination. -/
lemma integralDifferential_hasFDerivAt {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (q : Coordinates d) :
    HasFDerivAt (fun p => ∫ z, integrandDifferential V p z ∂standardGaussian d)
      (∫ z, integrandSecondDifferential V q z ∂standardGaussian d) q := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := integrandDifferential V) (F' := integrandSecondDifferential V)
    (bound := fun z => 2 * β * ‖evaluation z‖ ^ 2) (ε := 1) (by norm_num)
  · exact Filter.Eventually.of_forall (fun p => (differential_integrand_continuous hV p).aestronglyMeasurable)
  · exact differential_integrand_integrable hV q
  · exact (second_integrand_continuous_z hV q).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z p _ => second_integrand_norm_bound hV p z)
  · exact evaluation_norm_sq_integrable.const_mul (2 * β)
  · exact Filter.Eventually.of_forall (fun z p _ => differential_integrand_hasFDerivAt hV p z)

lemma integralSecondDifferential_continuous {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) :
    Continuous (fun q : Coordinates d => ∫ z, integrandSecondDifferential V q z ∂standardGaussian d) := by
  exact continuous_of_dominated
    (fun q => (second_integrand_continuous_z hV q).aestronglyMeasurable)
    (fun q => Filter.Eventually.of_forall (second_integrand_norm_bound hV q))
    (evaluation_norm_sq_integrable.const_mul (2 * β))
    (Filter.Eventually.of_forall (second_integrand_continuous_q hV))

/-- Full C² regularity of the genuine Gaussian potential average. -/
lemma potentialAverage_contDiff {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) : ContDiff ℝ 2 (potentialAverage V) := by
  have hd : fderiv ℝ (potentialAverage V) =
      (fun q => ∫ z, integrandDifferential V q z ∂standardGaussian d) :=
    funext (potentialAverage_fderiv hV)
  have hdd : fderiv ℝ (fun q => ∫ z, integrandDifferential V q z ∂standardGaussian d) =
      (fun q => ∫ z, integrandSecondDifferential V q z ∂standardGaussian d) :=
    funext (fun q => (integralDifferential_hasFDerivAt hV q).fderiv)
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
  refine ⟨fun q => (potentialAverage_hasFDerivAt hV q).differentiableAt, by simp, ?_⟩
  rw [hd, contDiff_one_iff_fderiv]
  refine ⟨fun q => (integralDifferential_hasFDerivAt hV q).differentiableAt, ?_⟩
  rw [hdd]
  exact integralSecondDifferential_continuous hV

/-- Evaluation of a twice-curried differential at two fixed directions. -/
def evaluateSecond (u w : Coordinates d) :
    (Coordinates d →L[ℝ] Coordinates d →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ w).comp
    (ContinuousLinearMap.apply ℝ (Coordinates d →L[ℝ] ℝ) u)

/-- Exact second Fréchet variation of the genuine Gaussian potential average. -/
lemma potentialAverage_second_variation {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (q u w : Coordinates d) :
    (fderiv ℝ (fderiv ℝ (potentialAverage V)) q u) w =
      ∫ z, (fderiv ℝ (fderiv ℝ V) (q.1 + matVec q.2 z)
        (u.1 + matVec u.2 z)) (w.1 + matVec w.2 z) ∂standardGaussian d := by
  have hd : fderiv ℝ (potentialAverage V) =
      (fun p => ∫ z, integrandDifferential V p z ∂standardGaussian d) := funext (potentialAverage_fderiv hV)
  rw [hd, (integralDifferential_hasFDerivAt hV q).fderiv]
  exact (ContinuousLinearMap.integral_comp_comm
    (E := Coordinates d →L[ℝ] Coordinates d →L[ℝ] ℝ) (Fₗ := ℝ) (𝕜 := ℝ)
    (φ := integrandSecondDifferential V q) (evaluateSecond u w)
    (second_integrand_integrable hV q)).symm

end Paper38.GaussianDifferentiation
