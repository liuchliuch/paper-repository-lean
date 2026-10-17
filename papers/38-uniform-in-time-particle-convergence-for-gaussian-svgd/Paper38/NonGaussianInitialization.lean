import Paper38.ParticleLimit
import Paper38.ExternalMatrixAnalysis
import Paper38.SourceFlowMeasurability
import Paper38.ExternalEmpiricalTransport

/-! The own deterministic whitening-continuity step of Corollary 2.7.
The raw empirical Wasserstein and ordinary moment strong laws are kept separate;
none of their conclusions contains a whitening or a particle limit. -/

noncomputable section
namespace Paper38.NonGaussianInitialization

open Paper38.Model Paper38.Transport Paper38.AffineLifting Paper38.ParticleLimit
open MeasureTheory Set Filter
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.Frobenius ENNReal NNReal Topology

variable {d : ℕ}

/-- The exact common-index cost for an arbitrary centered empirical cloud. -/
lemma centered_affine_index_cost {N : ℕ} (hN : 0 < N) (x : Fin N → E d)
    (u : E d) (A : Mat d) :
    (N : ℝ)⁻¹ * ∑ i, ‖u + matVec A (x i - empiricalMean x)‖ ^ 2 =
      ‖u‖ ^ 2 + (A * empiricalCovariance x * A.transpose).trace := by
  let zc := fun i => ModelBridges.coordinates (x i)
  have hh := Standardization.centered_affine_cost hN zc A (-ModelBridges.coordinates u)
  have hpoint (i : Fin N) : ‖u + matVec A (x i - empiricalMean x)‖ ^ 2 =
      Standardization.sqNorm (A *ᵥ Empirical.centered zc i - (-ModelBridges.coordinates u)) := by
    rw [← ModelBridges.sqNorm_coordinates]
    have hm : ModelBridges.coordinates (empiricalMean x) = Empirical.mean zc :=
      ModelBridges.empiricalMean_coordinates x
    congr 1
    change ModelBridges.coordinates u + A *ᵥ (ModelBridges.coordinates (x i) -
      ModelBridges.coordinates (empiricalMean x)) =
        A *ᵥ Empirical.centered zc i - (-ModelBridges.coordinates u)
    rw [hm]
    simp only [Empirical.centered, sub_neg_eq_add]
    exact add_comm _ _
  have hu : Standardization.sqNorm (-ModelBridges.coordinates u) = ‖u‖ ^ 2 := by
    simpa only [ModelBridges.coordinates, WithLp.ofLp_neg, norm_neg] using
      ModelBridges.sqNorm_coordinates (-u)
  simp_rw [hpoint]
  rw [hh, hu]
  rw [← ModelBridges.empiricalCovariance_coordinates]
  ring

/-- Replacing empirical centering/whitening by its fixed limit has vanishing
actual transport cost. This is the corresponding-sample coupling in Ex19. -/
theorem empirical_whitening_replacement [NeZero d]
    (x : (n : ℕ) → Fin (n + 1) → E d) (W : ℕ → Mat d) (W0 : Mat d) (μ : E d)
    (hW : Tendsto W atTop (𝓝 W0))
    (hm : Tendsto (fun n => empiricalMean (x n)) atTop (𝓝 μ))
    (Sigma : Mat d) (hS : Tendsto (fun n => empiricalCovariance (x n)) atTop (𝓝 Sigma)) :
    Tendsto (fun n => w2sq (empiricalLaw (standardizedCloud (x n) (W n)))
      (empiricalLaw (fun i => matVec W0 (x n i - μ)))) atTop (𝓝 0) := by
  have hA : Tendsto (fun n => W n - W0) atTop (𝓝 (0 : Mat d)) := by
    simpa only [sub_self] using hW.sub_const W0
  have hu : Tendsto (fun n => matVec W0 (μ - empiricalMean (x n))) atTop (𝓝 0) := by
    have hh := (GaussianAffine.continuous_matVec W0).continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := μ)).sub hm)
    have hz : matVec W0 (0 : E d) = 0 := (Matrix.toEuclideanLin W0).map_zero
    simpa only [sub_self, hz, Function.comp_def] using hh
  have htrace : Tendsto
      (fun n => ((W n - W0) * empiricalCovariance (x n) * (W n - W0).transpose).trace)
      atTop (𝓝 0) := by
    have hc : Continuous (fun p : Mat d × Mat d => (p.1 * p.2 * p.1.transpose).trace) := by fun_prop
    simpa using hc.continuousAt.tendsto.comp (hA.prodMk_nhds hS)
  have hcost : Tendsto
      (fun n => ‖matVec W0 (μ - empiricalMean (x n))‖ ^ 2 +
        ((W n - W0) * empiricalCovariance (x n) * (W n - W0).transpose).trace)
      atTop (𝓝 0) := by simpa using (hu.norm.pow 2).add htrace
  have hof := ENNReal.tendsto_ofReal hcost
  simp only [ENNReal.ofReal_zero] at hof
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hof
    (fun _ => zero_le _) (fun n => ?_)
  have hp (i : Fin (n + 1)) : standardizedCloud (x n) (W n) i - matVec W0 (x n i - μ) =
      matVec W0 (μ - empiricalMean (x n)) +
        matVec (W n - W0) (x n i - empiricalMean (x n)) := by
    have hlin : matVec (W n - W0) (x n i - empiricalMean (x n)) =
        matVec (W n) (x n i - empiricalMean (x n)) -
          matVec W0 (x n i - empiricalMean (x n)) :=
      (TransportParticleAffine.matrixAction (x n i - empiricalMean (x n))).map_sub (W n) W0
    have hv : matVec W0 (x n i - μ) =
        matVec W0 (x n i - empiricalMean (x n)) - matVec W0 (μ - empiricalMean (x n)) := by
      rw [← show matVec W0 ((x n i - empiricalMean (x n)) - (μ - empiricalMean (x n))) =
        matVec W0 (x n i - empiricalMean (x n)) - matVec W0 (μ - empiricalMean (x n)) from
          (Matrix.toEuclideanLin W0).map_sub _ _]
      congr 1
      abel
    rw [hlin, hv]
    unfold standardizedCloud
    abel
  have hh := empirical_w2sq_le_index_cost (Nat.succ_pos n)
    (standardizedCloud (x n) (W n)) (fun i => matVec W0 (x n i - μ))
  simpa only [hp, centered_affine_index_cost (Nat.succ_pos n)] using hh

/-- Actual standardized empirical laws converge in quadratic transport, from
raw empirical convergence and ordinary centering/covariance/whitening limits. -/
theorem standardized_empirical_tendsto [NeZero d]
    (ν : Measure (E d)) [IsProbabilityMeasure ν]
    (x : (n : ℕ) → Fin (n + 1) → E d) (W : ℕ → Mat d) (W0 : Mat d) (μ : E d)
    (hW0 : IsUnit W0) (hW : Tendsto W atTop (𝓝 W0))
    (hm : Tendsto (fun n => empiricalMean (x n)) atTop (𝓝 μ))
    (Sigma : Mat d) (hS : Tendsto (fun n => empiricalCovariance (x n)) atTop (𝓝 Sigma))
    (hraw : Tendsto (fun n => w2sq (empiricalLaw (x n)) ν) atTop (𝓝 0)) :
    Tendsto (fun n => w2sq (empiricalLaw (standardizedCloud (x n) (W n)))
      (ν.map (fun y => matVec W0 (y - μ)))) atTop (𝓝 0) := by
  let f : E d → E d := fun y => matVec W0 (y - μ)
  have hf : Continuous f := (GaussianAffine.continuous_matVec W0).comp (continuous_id.sub continuous_const)
  letI := Measure.isProbabilityMeasure_map hf.measurable.aemeasurable (μ := ν)
  letI : ∀ n, IsProbabilityMeasure (empiricalLaw (x n)) :=
    fun n => AffineLifting.empiricalLaw_probability (Nat.succ_pos n) (x n)
  letI : ∀ n, IsProbabilityMeasure (empiricalLaw (standardizedCloud (x n) (W n))) :=
    fun n => AffineLifting.empiricalLaw_probability (Nat.succ_pos n) _
  letI : ∀ n, IsProbabilityMeasure (empiricalLaw (fun i => f (x n i))) :=
    fun n => AffineLifting.empiricalLaw_probability (Nat.succ_pos n) _
  have hfixed : Tendsto (fun n => w2sq (empiricalLaw (fun i => f (x n i))) (ν.map f))
      atTop (𝓝 0) := by
    have hof := ENNReal.Tendsto.const_mul hraw (a := (covarianceMax W0 : ℝ≥0∞)) (Or.inr ENNReal.coe_ne_top)
    simp only [mul_zero] at hof
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hof
      (fun _ => zero_le _) (fun n => ?_)
    have heq : f = fun y => -matVec W0 μ + matVec W0 y := by
      funext y
      change matVec W0 (y - μ) = _
      rw [show matVec W0 (y - μ) = matVec W0 y - matVec W0 μ from
        (Matrix.toEuclideanLin W0).map_sub _ _]
      abel
    have h := (matrix_affine_two_sided (empiricalLaw (x n)) ν (-matVec W0 μ) W0 hW0).2
    rw [← heq, empiricalLaw_map (Nat.succ_pos n) (x n) f hf.measurable] at h
    exact h
  have hreplace := empirical_whitening_replacement x W W0 μ hW hm Sigma hS
  have hsum := (ENNReal.Tendsto.const_mul hreplace (a := 2) (Or.inr (by norm_num))).add
    (ENNReal.Tendsto.const_mul hfixed (a := 2) (Or.inr (by norm_num)))
  simp only [mul_zero, add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le _) (fun n => w2sq_triangle
      (empiricalLaw (standardizedCloud (x n) (W n))) (empiricalLaw (fun i => f (x n i))) (ν.map f))

/-- Principal matrix square roots are continuous along the actual symmetric
covariance matrices, using only the standard root differential baseline. -/
theorem covarianceRoot_tendsto
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (S : ℕ → Mat d) (Sigma : Mat d) (hSigma : Sigma.PosDef)
    (hsym : ∀ n, (S n).transpose = S n) (hS : Tendsto S atTop (𝓝 Sigma)) :
    Tendsto (fun n => covarianceRoot (S n)) atTop (𝓝 (covarianceRoot Sigma)) := by
  have hSigmaSym : Sigma.transpose = Sigma := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hSigma.isHermitian.eq
  let q : ℕ → HilbertCoordinates.Tangent d := fun n => HilbertMobility.encode d (0, S n)
  let q0 := HilbertMobility.encode d (0, Sigma)
  have hq : Tendsto q atTop (𝓝 q0) :=
    (HilbertMobility.encode d).continuous.tendsto _ |>.comp
      ((tendsto_const_nhds (x := (0 : E d))).prodMk_nhds hS)
  have hq0 : q0 ∈ HilbertCoordinates.Domain d := by
    change (HilbertCoordinates.toModel d q0).2.PosDef
    rw [HilbertMobility.toModel_encode _ hSigmaSym]
    exact hSigma
  have hr := (HilbertCoordinates.matrixProjection d).continuous.tendsto
    (ExternalMatrixAnalysis.principalRoot q0) |>.comp ((sqrt q0 hq0).continuousAt.tendsto.comp hq)
  have heq (n : ℕ) : HilbertCoordinates.matrixProjection d (ExternalMatrixAnalysis.principalRoot (q n)) =
      covarianceRoot (S n) := by
    change (HilbertCoordinates.toModel d (ExternalMatrixAnalysis.principalRoot (q n))).2 = _
    rw [ExternalMatrixAnalysis.toModel_principalRoot]
    change CFC.sqrt (HilbertCoordinates.toModel d (q n)).2 = _
    rw [HilbertMobility.toModel_encode _ (hsym n)]
    rfl
  have heq0 : HilbertCoordinates.matrixProjection d (ExternalMatrixAnalysis.principalRoot q0) =
      covarianceRoot Sigma := by
    change (HilbertCoordinates.toModel d (ExternalMatrixAnalysis.principalRoot q0)).2 = _
    rw [ExternalMatrixAnalysis.toModel_principalRoot]
    change CFC.sqrt (HilbertCoordinates.toModel d q0).2 = _
    rw [HilbertMobility.toModel_encode _ hSigmaSym]
    rfl
  simpa only [heq, heq0, Function.comp_def] using hr

/-- The empirical principal inverse roots converge to the population inverse
root; whitening continuity is proved, not included in the raw SLLN baseline. -/
theorem principal_whitening_tendsto
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (S : ℕ → Mat d) (Sigma : Mat d) (hSigma : Sigma.PosDef)
    (hsym : ∀ n, (S n).transpose = S n) (hS : Tendsto S atTop (𝓝 Sigma)) :
    Tendsto (fun n => (covarianceRoot (S n))⁻¹) atTop (𝓝 (covarianceRoot Sigma)⁻¹) :=
  (CoefficientRegularity.matrixInverse_contDiffAt (n := 0) hSigma.posDef_sqrt.isUnit).continuousAt.tendsto.comp
    (covarianceRoot_tendsto sqrt S Sigma hSigma hsym hS)

/-- Ex19 in squared form on the common probability-one raw strong-law event. -/
theorem ae_standardized_empirical_tendsto [NeZero d]
    {Ω : Type*} [MeasurableSpace Ω]
    (stronglaws : ExternalEmpiricalTransport.RawEmpiricalStrongLaws Ω d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure (E d)) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → E d) (hmeas : ∀ n, Measurable (X n))
    (hindep : ProbabilityTheory.iIndepFun X P) (hlaw : ∀ n, Measure.map (X n) P = ν)
    (hsecond : Integrable (fun x : E d => ‖x‖ ^ 2) ν)
    (hSigma : (ExternalEmpiricalTransport.populationCovariance ν).PosDef) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => w2sq
        (empiricalLaw (standardizedCloud (fun i : Fin (n + 1) => X i ω)
          (covarianceRoot (empiricalCovariance (fun i : Fin (n + 1) => X i ω)))⁻¹))
        (ν.map (fun y => matVec (covarianceRoot (ExternalEmpiricalTransport.populationCovariance ν))⁻¹
          (y - ExternalEmpiricalTransport.populationMean ν)))) atTop (𝓝 0) := by
  filter_upwards [stronglaws P ν X hmeas hindep hlaw hsecond] with ω hω
  let x := fun n (i : Fin (n + 1)) => X i ω
  have hsym (n : ℕ) : (empiricalCovariance (x n)).transpose = empiricalCovariance (x n) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (ModelBridges.empiricalCovariance_posSemidef (x n)).isHermitian.eq
  have hW := principal_whitening_tendsto sqrt _ _ hSigma hsym hω.2.2
  have hunit : IsUnit (covarianceRoot (ExternalEmpiricalTransport.populationCovariance ν))⁻¹ :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _
      ((Matrix.isUnit_iff_isUnit_det _).mp hSigma.posDef_sqrt.isUnit))
  exact standardized_empirical_tendsto ν x _ _ _ hunit hW hω.2.1 _ hω.2.2 hω.1

/-- Passing to lower/upper limits in the proved affine spectral bounds gives
exactly the three inequalities of source (2.21). -/
theorem spectral_liminf_limsup (shape err : ℕ → ℝ≥0∞) (D : ℝ≥0∞)
    (a b : ℝ≥0) (hshape : Tendsto shape atTop (𝓝 D))
    (hlower : ∀ᶠ n in atTop, (a : ℝ≥0∞) * shape n ≤ err n)
    (hupper : ∀ᶠ n in atTop, err n ≤ (b : ℝ≥0∞) * shape n) :
    (a : ℝ≥0∞) * D ≤ liminf err atTop ∧ liminf err atTop ≤ limsup err atTop ∧
      limsup err atTop ≤ (b : ℝ≥0∞) * D := by
  have ha := ENNReal.Tendsto.const_mul (a := (a : ℝ≥0∞)) hshape (Or.inr ENNReal.coe_ne_top)
  have hb := ENNReal.Tendsto.const_mul (a := (b : ℝ≥0∞)) hshape (Or.inr ENNReal.coe_ne_top)
  refine ⟨?_, liminf_le_limsup, ?_⟩
  · rw [← ha.liminf_eq]
    exact liminf_le_liminf hlower
  · rw [← hb.limsup_eq]
    exact limsup_le_limsup hupper

/-- Actual shape defects converge to the population standardized shape defect,
by the proved genuine transport continuity theorem. -/
theorem standardized_shape_error_tendsto [NeZero d]
    (ν : Measure (E d)) [IsProbabilityMeasure ν]
    (z : (n : ℕ) → Fin (n + 1) → E d)
    (η : Measure (E d)) [IsProbabilityMeasure η]
    (hz : Tendsto (fun n => w2sq (empiricalLaw (z n)) η) atTop (𝓝 0)) :
    Tendsto (fun n => w2sq (empiricalLaw (z n)) (standardGaussian d)) atTop
      (𝓝 (w2sq η (standardGaussian d))) := by
  letI : ∀ n, IsProbabilityMeasure (empiricalLaw (z n)) :=
    fun n => AffineLifting.empiricalLaw_probability (Nat.succ_pos n) _
  letI := GaussianAffine.standardGaussian_probability d
  have hconst : Tendsto (fun _ : ℕ => w2sq (standardGaussian d) (standardGaussian d))
      atTop (𝓝 0) := by simp only [w2sq_self]; exact tendsto_const_nhds
  exact w2sq_tendsto_of_perturbations η (standardGaussian d)
    (fun n => empiricalLaw (z n)) (fun _ => standardGaussian d) hz hconst

end Paper38.NonGaussianInitialization
