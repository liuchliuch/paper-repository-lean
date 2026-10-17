import Paper38.ParticleLimit
import Paper38.CoefficientRegularity

/-! Finite-particle limiting shape from the actual Gaussian moment decay.
Only an arbitrary-coefficient standard linear matrix-ODE theorem is an external
input. Affine reconstruction, covariance identification, exponential transport
rate, error limit, and positive finite-atom floor are derived here. -/

noncomputable section
namespace Paper38.ParticleLimit

open Paper38.Model Paper38.Transport Paper38.TransportParticleAffine Paper38.AffineLifting
open MeasureTheory Set Filter
open scoped BigOperators Matrix MatrixOrder ENNReal NNReal Topology

variable {d N : ℕ}

/-- The full shape-law construction from a principal fundamental matrix and its
standard linear-system tail estimate. Every Gaussian/particle conclusion is
proved rather than supplied as linear-ODE input. -/
theorem limit_from_fundamental [NeZero d] (hN : 0 < N)
    (V : E d → ℝ) (X : ℝ → Fin N → E d) (hX : particleSolution V X)
    (hC : ContinuousOn (fun t => particleCoefficient V (X t)) (Ici 0))
    (qstar : Coordinates d) (hqstar : qstar.2.PosDef)
    (Q decay : ℝ) (hdecay : 0 < decay)
    (hq : ∀ t, 0 ≤ t → coordinateSqDist (Specification.cloudQ (X t)) qstar ≤
      Q ^ 2 * Real.exp (-2 * decay * t))
    (L : ℝ → Mat d) (Linf : Mat d) (M : ℝ)
    (hL0 : L 0 = 1)
    (hL : ∀ t, 0 ≤ t → HasDerivWithinAt L
      (particleCoefficient V (X t) * L t) (Ici 0) t)
    (hLinf : IsUnit Linf) (hLlim : Tendsto L atTop (𝓝 Linf))
    (htail : ∀ t, 0 ≤ t → frobSq (L t - Linf) ≤ M ^ 2 * Real.exp (-2 * decay * t))
    (W : Mat d) (hW : IsWhitening (X 0) W) :
    ∃ (Binf : Mat d) (xinf : Fin N → E d),
      IsUnit Binf ∧ Binf * Binf.transpose = qstar.2 * qstar.2.transpose ∧
      (∀ i, xinf i = qstar.1 + matVec Linf (X 0 i - empiricalMean (X 0))) ∧
      (∀ i, xinf i = qstar.1 + matVec Binf (standardizedCloud (X 0) W i)) ∧
      (∀ t, 0 ≤ t → w2sq (empiricalLaw (X t)) (empiricalLaw xinf) ≤
        ENNReal.ofReal ((Q ^ 2 + M ^ 2 * (empiricalCovariance (X 0)).trace) *
          Real.exp (-2 * decay * t))) ∧
      (∀ i, Tendsto (fun t => X t i) atTop (𝓝 (xinf i))) ∧
      (∀ p : Specification.MomentPath d, Tendsto p.q atTop (𝓝 qstar) →
        Tendsto (fun t => w2sq (empiricalLaw (X t)) (p.law t)) atTop
          (𝓝 (w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2)))) ∧
      ((covarianceMin Binf : ℝ≥0∞) * w2sq
          (empiricalLaw (standardizedCloud (X 0) W)) (standardGaussian d) ≤
        w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2) ∧
       w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2) ≤
        (covarianceMax Binf : ℝ≥0∞) * w2sq
          (empiricalLaw (standardizedCloud (X 0) W)) (standardGaussian d)) ∧
      0 < w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2) := by
  let z := standardizedCloud (X 0) W
  let B : ℝ → Mat d := fun t => L t * W⁻¹
  let Binf := Linf * W⁻¹
  let xinf : Fin N → E d := fun i => qstar.1 + matVec Binf (z i)
  have hunitW := whitening_isUnit (X 0) W hW
  have hunitWi : IsUnit W⁻¹ := (Matrix.isUnit_iff_isUnit_det W⁻¹).mpr
    (Matrix.isUnit_nonsing_inv_det W ((Matrix.isUnit_iff_isUnit_det W).mp hunitW))
  have hunitB : IsUnit Binf := hLinf.mul hunitWi
  have hrepr (t : ℝ) (ht : 0 ≤ t) :
      X t = fun i => empiricalMean (X t) + matVec (B t) (z i) := by
    funext i
    exact (particle_affine_representation hN V X hX hC L hL0 hL t ht i).trans
      ((standardized_affine_lift (X 0) W (L t) hW (empiricalMean (X t))).1 i)
  have hcov (t : ℝ) (ht : 0 ≤ t) : B t * (B t).transpose = empiricalCovariance (X t) :=
    ((standardized_affine_lift (X 0) W (L t) hW (empiricalMean (X t))).2).trans
      (particle_affine_covariance hN V X hX hC L hL0 hL t ht).symm
  have hBlim : Tendsto B atTop (𝓝 Binf) := by
    exact hLlim.mul_const W⁻¹
  have hqlim := coordinate_tendsto_of_exp_bound
    (fun t => Specification.cloudQ (X t)) qstar Q decay hdecay hq
  have hAlim := particle_covariance_tendsto X hX qstar hqlim
  have hsym : qstar.2.transpose = qstar.2 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hqstar.isHermitian.eq
  have hBcov : Binf * Binf.transpose = qstar.2 * qstar.2.transpose := by
    rw [hsym]
    exact affine_covariance_limit X B Binf (qstar.2 * qstar.2) hBlim hAlim hcov
  have hmeanlim : Tendsto (fun t => empiricalMean (X t)) atTop (𝓝 qstar.1) :=
    (continuous_fst.tendsto qstar).comp hqlim
  have hXlim (i : Fin N) : Tendsto (fun t => X t i) atTop (𝓝 (xinf i)) := by
    have hh := hmeanlim.add ((matrixAction (z i)).continuous_of_finiteDimensional.tendsto Binf |>.comp hBlim)
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact congrFun (hrepr t ht).symm i
  have hWi : frobSq W⁻¹ = (empiricalCovariance (X 0)).trace := by
    rw [← whitening_inverse_covariance (X 0) W hW]
    exact (Standardization.trace_self_transpose W⁻¹).symm
  have hBtail (t : ℝ) (ht : 0 ≤ t) :
      frobSq (B t - Binf) ≤ (M ^ 2 * (empiricalCovariance (X 0)).trace) *
        Real.exp (-2 * decay * t) := by
    have hd : B t - Binf = (L t - Linf) * W⁻¹ := by
      dsimp [B, Binf]
      rw [Matrix.sub_mul]
    rw [hd]
    calc
      frobSq ((L t - Linf) * W⁻¹) ≤ frobSq (L t - Linf) * frobSq W⁻¹ := frobSq_mul_le _ _
      _ ≤ (M ^ 2 * Real.exp (-2 * decay * t)) * frobSq W⁻¹ :=
        mul_le_mul_of_nonneg_right (htail t ht) (frobSq_nonneg _)
      _ = _ := by rw [hWi]; ring
  have hmeantail (t : ℝ) (ht : 0 ≤ t) :
      ‖empiricalMean (X t) - qstar.1‖ ^ 2 ≤ Q ^ 2 * Real.exp (-2 * decay * t) := by
    apply (le_add_of_nonneg_right (frobSq_nonneg
      (covarianceRoot (empiricalCovariance (X t)) - qstar.2))).trans (hq t ht)
  have hz := ModelBridges.standardizedCloud_moments hN (X 0) W hW
  have hcost (t : ℝ) (ht : 0 ≤ t) :
      w2sq (empiricalLaw (X t)) (empiricalLaw xinf) ≤
        ENNReal.ofReal ((Q ^ 2 + M ^ 2 * (empiricalCovariance (X 0)).trace) *
          Real.exp (-2 * decay * t)) := by
    rw [hrepr t ht]
    exact affine_empirical_exp_rate hN z hz.1 hz.2
      (fun t => empiricalMean (X t)) qstar.1 B Binf
      (Q ^ 2) (M ^ 2 * (empiricalCovariance (X 0)).trace) decay hmeantail hBtail t ht
  have hfloor := limiting_shape_floor hN z qstar.1 Binf qstar.2 hunitB hBcov
  refine ⟨Binf, xinf, hunitB, hBcov, ?_, fun _ => rfl, hcost, hXlim, ?_, hfloor.1, hfloor.2⟩
  · intro i
    exact ((standardized_affine_lift (X 0) W Linf hW qstar.1).1 i).symm
  · intro p hp
    exact full_law_error_tendsto hN X xinf p qstar hXlim hp

/-- One tail constant is chosen before the particle number, cloud and whitening.
The Gaussian coefficient envelope is derived from source-coordinate decay and
the proved coefficient Lipschitz estimate; it is not a linear-ODE input field. -/
theorem uniform_limit_from_lipschitz_moment_decay [NeZero d]
    (hlinear : LinearMatrixODE.StandardDecayingFundamentalMatrixTheorem d)
    (V : E d → ℝ) (qstar : Coordinates d) (hqstar : qstar.2.PosDef)
    (Kset : Set (Coordinates d)) (K : ℝ≥0) (Q decay : ℝ) (hdecay : 0 < decay)
    (hLip : LipschitzOnWith K
      (fun u : HilbertCoordinates.Ambient d => HilbertCoordinates.flattenEquiv d
        (gaussianCoefficient V ((HilbertCoordinates.ambientEquiv d).symm u)))
      (HilbertCoordinates.ambientEquiv d '' Kset))
    (hstar : qstar ∈ Kset) (hzero : gaussianCoefficient V qstar = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ) (hN : 0 < N)
      (X : ℝ → Fin N → E d) (hX : particleSolution V X)
      (hC : ContinuousOn (fun t => particleCoefficient V (X t)) (Ici 0))
      (W : Mat d) (hW : IsWhitening (X 0) W),
      (∀ t, 0 ≤ t → Specification.cloudQ (X t) ∈ Kset) →
      (∀ t, 0 ≤ t → coordinateSqDist (Specification.cloudQ (X t)) qstar ≤
        Q ^ 2 * Real.exp (-2 * decay * t)) →
      ∃ Linf : Mat d, IsUnit Linf ∧
    ∃ (Binf : Mat d) (xinf : Fin N → E d),
      IsUnit Binf ∧ Binf * Binf.transpose = qstar.2 * qstar.2.transpose ∧
      (∀ i, xinf i = qstar.1 + matVec Linf (X 0 i - empiricalMean (X 0))) ∧
      (∀ i, xinf i = qstar.1 + matVec Binf (standardizedCloud (X 0) W i)) ∧
      (∀ t, 0 ≤ t → w2sq (empiricalLaw (X t)) (empiricalLaw xinf) ≤
        ENNReal.ofReal ((Q ^ 2 + M ^ 2 * (empiricalCovariance (X 0)).trace) *
          Real.exp (-2 * decay * t))) ∧
      (∀ i, Tendsto (fun t => X t i) atTop (𝓝 (xinf i))) ∧
      (∀ p : Specification.MomentPath d, Tendsto p.q atTop (𝓝 qstar) →
        Tendsto (fun t => w2sq (empiricalLaw (X t)) (p.law t)) atTop
          (𝓝 (w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2)))) ∧
      ((covarianceMin Binf : ℝ≥0∞) * w2sq
          (empiricalLaw (standardizedCloud (X 0) W)) (standardGaussian d) ≤
        w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2) ∧
       w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2) ≤
        (covarianceMax Binf : ℝ≥0∞) * w2sq
          (empiricalLaw (standardizedCloud (X 0) W)) (standardGaussian d)) ∧
      0 < w2sq (empiricalLaw xinf) (gaussianLaw qstar.1 qstar.2) := by
  obtain ⟨M, hM, hstandard⟩ := hlinear ((K : ℝ) * |Q|) decay (by positivity) hdecay
  refine ⟨M, hM, ?_⟩
  intro N hN X hX hC W hW hmem hq
  have hcoef (t : ℝ) (ht : 0 ≤ t) : frobSq (particleCoefficient V (X t)) ≤
      ((K : ℝ) * |Q|) ^ 2 * Real.exp (-2 * decay * t) := by
    rw [particleCoefficient_eq_gaussianCoefficient V (X t) (hX.1 t ht)]
    exact coefficient_decay_of_lipschitz V (fun t => Specification.cloudQ (X t))
      qstar Kset K Q decay hLip hstar hzero hmem hq t ht
  obtain ⟨L, Linf, hL0, hL, hunit, hLinf, hLlim, htail⟩ :=
    hstandard (fun t => particleCoefficient V (X t)) hC hcoef
  exact ⟨Linf, hLinf, limit_from_fundamental hN V X hX hC qstar hqstar Q decay hdecay
    hq L Linf M hL0 hL hLinf hLlim htail W hW⟩

end Paper38.ParticleLimit
