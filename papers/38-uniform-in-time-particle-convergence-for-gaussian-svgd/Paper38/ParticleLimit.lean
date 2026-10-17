import Paper38.TransportParticleAffine
import Paper38.LinearMatrixODE
import Paper38.TransportContinuity
import Paper38.HilbertCoordinates
import Paper38.Specification
import Paper38.GaussianCoefficientModel

/-! Finite-cloud cost identities and exact limiting-shape algebra used by
Proposition 2.6. This file works with the actual Model empirical measures. -/

noncomputable section
namespace Paper38.ParticleLimit

open Paper38.Model Paper38.Transport Paper38.AffineLifting Paper38.TransportParticleAffine
open MeasureTheory Set Filter
open scoped BigOperators Matrix MatrixOrder ENNReal NNReal Topology

variable {d N : ℕ}

lemma frobSq_nonneg (A : Mat d) : 0 ≤ frobSq A :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Ordinary finite Cauchy--Schwarz gives Frobenius submultiplicativity. -/
lemma frobSq_mul_le (A B : Mat d) : frobSq (A * B) ≤ frobSq A * frobSq B := by
  calc
    frobSq (A * B) ≤ ∑ i, ∑ j, (∑ k, A i k ^ 2) * (∑ k, B k j ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) (fun k => B k j)
    _ = frobSq A * frobSq B := by
      have hc : (∑ j, ∑ k, B k j ^ 2) = frobSq B := Finset.sum_comm
      simp_rw [← Finset.mul_sum]
      rw [hc, ← Finset.sum_mul]
      rfl

/-- The common-index coupling, expressed in the paper's real Euclidean cost. -/
theorem empirical_w2sq_le_index_cost (hN : 0 < N) (x y : Fin N → E d) :
    w2sq (empiricalLaw x) (empiricalLaw y) ≤
      ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, ‖x i - y i‖ ^ 2) := by
  rw [GaussianCoupling.empiricalLaw_eq_transport_empirical hN,
    GaussianCoupling.empiricalLaw_eq_transport_empirical hN]
  refine (indexed_coupling_upper x y).trans_eq ?_
  symm
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg N)),
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hN), ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  simp only [Fintype.card_fin]
  simp_rw [edist_dist, dist_eq_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]

/-- The standardized cloud gives the same exact synchronous cost as a standard
Gaussian: zero mean removes the cross term and identity covariance gives the
Frobenius square. This is the equality in source Section 6, Ex18. -/
theorem isotropic_affine_index_cost (hN : 0 < N) (z : Fin N → E d)
    (hzmean : empiricalMean z = 0) (hzcov : empiricalCovariance z = 1)
    (u : E d) (A : Mat d) :
    (N : ℝ)⁻¹ * ∑ i, ‖u + matVec A (z i)‖ ^ 2 = ‖u‖ ^ 2 + frobSq A := by
  let zc := fun i => ModelBridges.coordinates (z i)
  have hm : Empirical.mean zc = 0 := by
    rw [← ModelBridges.empiricalMean_coordinates, hzmean]
    rfl
  have hc : Empirical.covariance zc = 1 := by
    rw [← ModelBridges.empiricalCovariance_coordinates, hzcov]
  have hh := Standardization.centered_affine_cost hN zc A (-ModelBridges.coordinates u)
  have hpoint (i : Fin N) : ‖u + matVec A (z i)‖ ^ 2 =
      Standardization.sqNorm (A *ᵥ Empirical.centered zc i - (-ModelBridges.coordinates u)) := by
    rw [← ModelBridges.sqNorm_coordinates]
    simp only [Empirical.centered, hm, sub_zero, sub_neg_eq_add]
    congr 1
    ext j
    simp only [ModelBridges.coordinates, WithLp.ofLp_add, matVec, vec, WithLp.ofLp_toLp,
      Pi.add_apply, zc]
    ring
  have hu : Standardization.sqNorm (-ModelBridges.coordinates u) = ‖u‖ ^ 2 := by
    simpa only [ModelBridges.coordinates, WithLp.ofLp_neg, norm_neg] using
      ModelBridges.sqNorm_coordinates (-u)
  simp_rw [hpoint]
  rw [hh, hc, Matrix.mul_one, Standardization.trace_self_transpose, hu]
  change frobSq A + ‖u‖ ^ 2 = ‖u‖ ^ 2 + frobSq A
  ring

/-- Equation Ex18's upper bound for the two actual affine empirical clouds. -/
theorem isotropic_affine_w2sq_le (hN : 0 < N) (z : Fin N → E d)
    (hzmean : empiricalMean z = 0) (hzcov : empiricalCovariance z = 1)
    (m n : E d) (B D : Mat d) :
    w2sq (empiricalLaw (fun i => m + matVec B (z i)))
      (empiricalLaw (fun i => n + matVec D (z i))) ≤
      ENNReal.ofReal (‖m - n‖ ^ 2 + frobSq (B - D)) := by
  have hpoint (i : Fin N) : (m + matVec B (z i)) - (n + matVec D (z i)) =
      (m - n) + matVec (B - D) (z i) := by
    have hlin : matVec (B - D) (z i) = matVec B (z i) - matVec D (z i) :=
      (matrixAction (z i)).map_sub B D
    rw [hlin]
    abel
  have hh := empirical_w2sq_le_index_cost hN
    (fun i => m + matVec B (z i)) (fun i => n + matVec D (z i))
  simpa only [hpoint, isotropic_affine_index_cost hN z hzmean hzcov] using hh

/-- An affine moment/tail rate yields the source physical-time full-law rate. -/
theorem affine_empirical_exp_rate (hN : 0 < N) (z : Fin N → E d)
    (hzmean : empiricalMean z = 0) (hzcov : empiricalCovariance z = 1)
    (m : ℝ → E d) (mstar : E d) (B : ℝ → Mat d) (Binf : Mat d)
    (Cm CB decay : ℝ)
    (hm : ∀ t, 0 ≤ t → ‖m t - mstar‖ ^ 2 ≤ Cm * Real.exp (-2 * decay * t))
    (hB : ∀ t, 0 ≤ t → frobSq (B t - Binf) ≤ CB * Real.exp (-2 * decay * t))
    (t : ℝ) (ht : 0 ≤ t) :
    w2sq (empiricalLaw (fun i => m t + matVec (B t) (z i)))
      (empiricalLaw (fun i => mstar + matVec Binf (z i))) ≤
      ENNReal.ofReal ((Cm + CB) * Real.exp (-2 * decay * t)) := by
  apply (isotropic_affine_w2sq_le hN z hzmean hzcov (m t) mstar (B t) Binf).trans
  apply ENNReal.ofReal_le_ofReal
  nlinarith [hm t ht, hB t ht]

/-- Common-index couplings give actual transport convergence from finite-particle
coordinate convergence, without any replacement metric. -/
theorem empirical_w2sq_tendsto (hN : 0 < N) (X : ℝ → Fin N → E d) (y : Fin N → E d)
    (hX : ∀ i, Tendsto (fun t => X t i) atTop (𝓝 (y i))) :
    Tendsto (fun t => w2sq (empiricalLaw (X t)) (empiricalLaw y)) atTop (𝓝 0) := by
  have hs : Tendsto (fun t => ∑ i, ‖X t i - y i‖ ^ 2) atTop (𝓝 0) := by
    have h := tendsto_finset_sum Finset.univ (fun i _ => ((hX i).sub (tendsto_const_nhds (x := y i))).norm.pow 2)
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero] using h
  have hr : Tendsto (fun t => (N : ℝ)⁻¹ * ∑ i, ‖X t i - y i‖ ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero] using hs.const_mul (N : ℝ)⁻¹
  have he : Tendsto (fun t => ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, ‖X t i - y i‖ ^ 2))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
    (fun _ => zero_le _) (fun t => empirical_w2sq_le_index_cost hN (X t) y)

/-- Passing to the limit in the proved affine covariance identity identifies the
limiting covariance; no covariance identity at infinity is an input. -/
theorem affine_covariance_limit (X : ℝ → Fin N → E d) (B : ℝ → Mat d)
    (Binf Sigma : Mat d)
    (hB : Tendsto B atTop (𝓝 Binf))
    (hSigma : Tendsto (fun t => empiricalCovariance (X t)) atTop (𝓝 Sigma))
    (hcov : ∀ t, 0 ≤ t → B t * (B t).transpose = empiricalCovariance (X t)) :
    Binf * Binf.transpose = Sigma := by
  have hc : Continuous (fun A : Mat d => A * A.transpose) := by fun_prop
  have hlim := hc.continuousAt.tendsto.comp hB
  have hactual : Tendsto (fun t => empiricalCovariance (X t)) atTop
      (𝓝 (Binf * Binf.transpose)) := by
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hcov t ht
  exact tendsto_nhds_unique hactual hSigma

lemma particleCoefficient_eq_gaussianCoefficient (V : E d → ℝ) (x : Fin N → E d)
    (hS : (empiricalCovariance x).PosDef) :
    particleCoefficient V x = gaussianCoefficient V (Specification.cloudQ x) := by
  have hs : covarianceRoot (empiricalCovariance x) * covarianceRoot (empiricalCovariance x) =
      empiricalCovariance x := CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg
  unfold gaussianCoefficient Specification.cloudQ
  rw [hs]
  rfl

/-- Source (6.15)'s last identity follows algebraically from the two variational
stationarity identities. Those identities remain separate energy obligations. -/
lemma gaussianCoefficient_zero_of_stationarity (V : E d → ℝ) (qstar : Coordinates d)
    (hA : qstar.2.PosDef)
    (hm : meanGradient V qstar.1 (qstar.2 * qstar.2) = 0)
    (hGamma : meanHessian V qstar.1 (qstar.2 * qstar.2) = (qstar.2 * qstar.2)⁻¹) :
    gaussianCoefficient V qstar = 0 := by
  have hu : IsUnit (qstar.2 * qstar.2) := hA.isUnit.mul hA.isUnit
  have hd := (Matrix.isUnit_iff_isUnit_det (qstar.2 * qstar.2)).mp hu
  unfold gaussianCoefficient
  rw [hm, hGamma, Matrix.nonsing_inv_mul _ hd]
  ext i j
  simp [outer]

/-- The source coefficient envelope (6.17), derived from a genuine Lipschitz
bound in Euclidean--Frobenius coordinates and the actual q decay. -/
theorem coefficient_decay_of_lipschitz (V : E d → ℝ) (q : ℝ → Coordinates d)
    (qstar : Coordinates d) (Kset : Set (Coordinates d)) (K : ℝ≥0) (Q decay : ℝ)
    (hLip : LipschitzOnWith K
      (fun u : HilbertCoordinates.Ambient d =>
        HilbertCoordinates.flattenEquiv d
          (gaussianCoefficient V ((HilbertCoordinates.ambientEquiv d).symm u)))
      (HilbertCoordinates.ambientEquiv d '' Kset))
    (hstar : qstar ∈ Kset) (hzero : gaussianCoefficient V qstar = 0)
    (hqmem : ∀ t, 0 ≤ t → q t ∈ Kset)
    (hq : ∀ t, 0 ≤ t → coordinateSqDist (q t) qstar ≤ Q ^ 2 * Real.exp (-2 * decay * t))
    (t : ℝ) (ht : 0 ≤ t) :
    frobSq (gaussianCoefficient V (q t)) ≤
      ((K : ℝ) * |Q|) ^ 2 * Real.exp (-2 * decay * t) := by
  have hh := hLip.dist_le_mul (HilbertCoordinates.ambientEquiv d (q t))
    (Set.mem_image_of_mem (HilbertCoordinates.ambientEquiv d) (hqmem t ht))
    (HilbertCoordinates.ambientEquiv d qstar) (Set.mem_image_of_mem (HilbertCoordinates.ambientEquiv d) hstar)
  simp only [dist_eq_norm, ContinuousLinearEquiv.symm_apply_apply, hzero,
    map_zero, sub_zero] at hh
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh
  rw [HilbertCoordinates.norm_flatten_sq, mul_pow,
    ← HilbertCoordinates.coordinateSqDist_eq_norm_ambient] at hsq
  calc
    frobSq (gaussianCoefficient V (q t)) ≤ (K : ℝ) ^ 2 * coordinateSqDist (q t) qstar := hsq
    _ ≤ (K : ℝ) ^ 2 * (Q ^ 2 * Real.exp (-2 * decay * t)) :=
      mul_le_mul_of_nonneg_left (hq t ht) (sq_nonneg _)
    _ = _ := by rw [mul_pow, sq_abs]; ring

/-- A source-coordinate exponential estimate implies convergence in the
actual parameter topology; the Euclidean--Frobenius norm is used explicitly. -/
theorem coordinate_tendsto_of_exp_bound (q : ℝ → Coordinates d) (qstar : Coordinates d)
    (Q decay : ℝ) (hdecay : 0 < decay)
    (hq : ∀ t, 0 ≤ t → coordinateSqDist (q t) qstar ≤ Q ^ 2 * Real.exp (-2 * decay * t)) :
    Tendsto q atTop (𝓝 qstar) := by
  have hnorm : ∀ t, 0 ≤ t →
      ‖HilbertCoordinates.ambientEquiv d (q t) - HilbertCoordinates.ambientEquiv d qstar‖ ≤
        |Q| * Real.exp (-decay * t) := by
    intro t ht
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [← HilbertCoordinates.coordinateSqDist_eq_norm_ambient]
    have he : Real.exp (-2 * decay * t) = Real.exp (-decay * t) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      coordinateSqDist (q t) qstar ≤ Q ^ 2 * Real.exp (-2 * decay * t) := hq t ht
      _ = (|Q| * Real.exp (-decay * t)) ^ 2 := by rw [he, mul_pow, sq_abs]
  have hexp : Tendsto (fun t : ℝ => Real.exp (-decay * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hdecay))
  have hnormlim : Tendsto (fun t =>
      ‖HilbertCoordinates.ambientEquiv d (q t) - HilbertCoordinates.ambientEquiv d qstar‖)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      ((eventually_ge_atTop (0 : ℝ)).mono (fun t ht => hnorm t ht))
    simpa only [mul_zero] using hexp.const_mul |Q|
  have hamb := tendsto_iff_norm_sub_tendsto_zero.mpr hnormlim
  have hraw := (HilbertCoordinates.ambientEquiv d).symm.continuous.tendsto
    (HilbertCoordinates.ambientEquiv d qstar) |>.comp hamb
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hraw

/-- Principal square roots converging in q-coordinates force the original
empirical covariance to converge to the square of the limiting root. -/
theorem particle_covariance_tendsto {V : E d → ℝ} (X : ℝ → Fin N → E d)
    (hX : particleSolution V X) (qstar : Coordinates d)
    (hq : Tendsto (fun t => Specification.cloudQ (X t)) atTop (𝓝 qstar)) :
    Tendsto (fun t => empiricalCovariance (X t)) atTop (𝓝 (qstar.2 * qstar.2)) := by
  have hA := (continuous_snd.tendsto qstar).comp hq
  have hprod := hA.mul hA
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact CFC.sqrt_mul_sqrt_self (empiricalCovariance (X t)) (hX.1 t ht).posSemidef.nonneg

/-- Full-law error convergence (2.19) is a consequence of the proved genuine
transport continuity theorem, once the two concrete path limits are known. -/
theorem full_law_error_tendsto [NeZero d] (hN : 0 < N)
    (X : ℝ → Fin N → E d) (xinf : Fin N → E d) (p : Specification.MomentPath d)
    (qstar : Coordinates d)
    (hX : ∀ i, Tendsto (fun t => X t i) atTop (𝓝 (xinf i)))
    (hq : Tendsto p.q atTop (𝓝 qstar)) :
    Tendsto (fun t => w2sq (empiricalLaw (X t)) (p.law t)) atTop
      (𝓝 (w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2))) := by
  letI := AffineLifting.empiricalLaw_probability hN xinf
  letI : ∀ t, IsProbabilityMeasure (empiricalLaw (X t)) :=
    fun t => AffineLifting.empiricalLaw_probability hN (X t)
  letI := GaussianAffine.gaussianLaw_probability qstar.1 qstar.2
  letI : ∀ t, IsProbabilityMeasure (p.law t) :=
    fun t => GaussianAffine.gaussianLaw_probability (p.mean t) (covarianceRoot (p.cov t))
  have hgauss : Tendsto (fun t => w2sq (p.law t) (gaussianLaw qstar.1 qstar.2)) atTop (𝓝 0) := by
    have hcost : Tendsto (fun t => coordinateSqDist (p.q t) qstar) atTop (𝓝 0) := by
      have hc : Continuous (fun q : Coordinates d => coordinateSqDist q qstar) := by
        simp only [coordinateSqDist, frobSq]
        fun_prop
      simpa [coordinateSqDist, frobSq] using hc.continuousAt.tendsto.comp hq
    have hof : Tendsto (fun t => ENNReal.ofReal (coordinateSqDist (p.q t) qstar)) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hcost
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hof
      (fun _ => zero_le _) (fun t => GaussianCoupling.gaussian_w2sq_le
        (p.mean t) qstar.1 (covarianceRoot (p.cov t)) qstar.2)
  exact w2sq_tendsto_of_perturbations (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2)
    (fun t => empiricalLaw (X t)) p.law (empirical_w2sq_tendsto hN X xinf hX) hgauss

lemma covarianceMin_pos [NeZero d] (B : Mat d) (hB : IsUnit B) :
    0 < covarianceMin B := by
  have hgram : (B.transpose * B).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.conjTranspose_mul_self B (Matrix.mulVec_injective_iff_isUnit.mpr hB)
  change (0 : ℝ) < eigenMin (B * B.transpose) (covariancePSD B).isHermitian
  unfold eigenMin
  rw [← gram_covariance_eigenvalues B]
  rw [Finset.lt_inf'_iff]
  intro i hi
  exact hgram.eigenvalues_pos i

/-- Equation (2.20), including its strictly positive standardized-shape floor,
for the identified limiting covariance. -/
theorem limiting_shape_floor [NeZero d] (hN : 0 < N) (z : Fin N → E d)
    (m : E d) (B A : Mat d) (hB : IsUnit B)
    (hcov : B * B.transpose = A * A.transpose) :
    ((covarianceMin B : ℝ≥0∞) * w2sq (empiricalLaw z) (standardGaussian d) ≤
      w2sq (empiricalLaw (fun i => m + matVec B (z i))) (gaussianLaw m A) ∧
    w2sq (empiricalLaw (fun i => m + matVec B (z i))) (gaussianLaw m A) ≤
      (covarianceMax B : ℝ≥0∞) * w2sq (empiricalLaw z) (standardGaussian d)) ∧
    0 < w2sq (empiricalLaw (fun i => m + matVec B (z i))) (gaussianLaw m A) := by
  letI := AffineLifting.empiricalLaw_probability hN z
  letI := GaussianAffine.standardGaussian_probability d
  have h := matrix_affine_two_sided (empiricalLaw z) (standardGaussian d) m B hB
  rw [empiricalLaw_map hN z _ (continuous_const.add (GaussianAffine.continuous_matVec B)).measurable] at h
  change _ ≤ w2sq _ (gaussianLaw m B) ∧ w2sq _ (gaussianLaw m B) ≤ _ at h
  rw [GaussianAffine.gaussianLaw_eq_of_covariance m B A hcov] at h
  refine ⟨h, ?_⟩
  have hmin : (0 : ℝ≥0∞) < covarianceMin B := by exact_mod_cast covarianceMin_pos B hB
  have hshape := GaussianCoupling.empirical_standardGaussian_w2sq_pos (NeZero.pos d) hN z
  exact (ENNReal.mul_pos hmin.ne' hshape.ne').trans_le h.1

/-- The limiting affine factor differs from the principal covariance root by an
orthogonal matrix. This proves the shape is preserved up to rotation. -/
theorem limiting_orthogonal_factor (A B : Mat d) (hA : IsUnit A)
    (hcov : B * B.transpose = A * A.transpose) :
    (A⁻¹ * B) * (A⁻¹ * B).transpose = 1 := by
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hA
  calc
    (A⁻¹ * B) * (A⁻¹ * B).transpose =
        A⁻¹ * (B * B.transpose) * (A⁻¹).transpose := by
      rw [Matrix.transpose_mul]
      noncomm_ring
    _ = A⁻¹ * (A * A.transpose) * (A⁻¹).transpose := by rw [hcov]
    _ = (A⁻¹ * A) * (A⁻¹ * A).transpose := by
      rw [Matrix.transpose_mul]
      noncomm_ring
    _ = 1 := by rw [Matrix.nonsing_inv_mul A hd]; simp

/-- Reconstruction of the limit law is independent of every whitening choice,
because it equals one and the same centered affine cloud. Orthogonal changes
of coordinates are included without any coordinate-dependent-law premise. -/
theorem limit_cloud_whitening_independent (x : Fin N → E d) (W W' L : Mat d)
    (hW : IsWhitening x W) (hW' : IsWhitening x W') (m : E d) :
    empiricalLaw (fun i => m + matVec (L * W⁻¹) (standardizedCloud x W i)) =
      empiricalLaw (fun i => m + matVec (L * W'⁻¹) (standardizedCloud x W' i)) := by
  congr 1
  funext i
  exact ((standardized_affine_lift x W L hW m).1 i).symm.trans
    ((standardized_affine_lift x W' L hW' m).1 i)

/-- Two limiting clouds obtained from any whitening constructions coincide,
since each is the coordinatewise limit of the same actual particle path. -/
theorem limiting_cloud_unique (X : ℝ → Fin N → E d) (xinf yinf : Fin N → E d)
    (hx : ∀ i, Tendsto (fun t => X t i) atTop (𝓝 (xinf i)))
    (hy : ∀ i, Tendsto (fun t => X t i) atTop (𝓝 (yinf i))) : xinf = yinf := by
  funext i
  exact tendsto_nhds_unique (hx i) (hy i)

end Paper38.ParticleLimit
