import Paper38.Model
import Paper38.EmpiricalCovarianceDynamics
import Paper38.GaussianFullRank
import Paper38.GaussianStatistics
import Paper38.Standardization
import Paper38.MomentClosure
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Bridges between the paper's Euclidean model and its coordinate proofs.
The coordinate map is the canonical continuous linear equivalence. It is used to transport
algebra and differentiability, and no equality of the Euclidean and coordinate sup norms is used. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix MatrixOrder

namespace Paper38.ModelBridges

open Paper38.Model

variable {N d : ℕ}

/-- Coordinates of a Euclidean vector; this is the underlying canonical linear equivalence. -/
def coordinates (x : E d) : Fin d → ℝ := WithLp.ofLp x

lemma outer_coordinates (x y : E d) :
    outer x y = Matrix.vecMulVec (coordinates x) (coordinates y) := rfl

lemma matVec_coordinates (A : Mat d) (x : E d) :
    coordinates (matVec A x) = A *ᵥ coordinates x := rfl

/-- The actual Euclidean sample mean agrees exactly with the coordinate arithmetic mean. -/
theorem empiricalMean_coordinates (x : Fin N → E d) :
    coordinates (empiricalMean x) = Empirical.mean (fun i => coordinates (x i)) := by
  let e := WithLp.linearEquiv 2 ℝ (Fin d → ℝ)
  change e ((N : ℝ)⁻¹ • ∑ i, x i) = (N : ℝ)⁻¹ • ∑ i, e (x i)
  rw [map_smul, map_sum]

/-- The actual Euclidean empirical covariance is the coordinate matrix `N⁻¹YYᵀ`. -/
theorem empiricalCovariance_coordinates (x : Fin N → E d) :
    empiricalCovariance x = Empirical.covariance (fun i => coordinates (x i)) := by
  ext j k
  rw [Empirical.covariance_apply, ← empiricalMean_coordinates]
  change (N : ℝ)⁻¹ * (∑ i, outer (x i - empiricalMean x)
    (x i - empiricalMean x)) j k = _
  rw [Matrix.sum_apply]
  rfl

lemma affineSpan_coordinates_iff (x : Fin N → E d) :
    affineSpan ℝ (Set.range (fun i => coordinates (x i))) = ⊤ ↔
      affineSpan ℝ (Set.range x) = ⊤ := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toAffineEquiv
  constructor
  · intro h
    have hm := e.symm.toAffineMap.span_eq_top_of_surjective e.symm.surjective h
    change affineSpan ℝ (e.symm '' Set.range (e ∘ x)) = ⊤ at hm
    rw [← Set.range_comp] at hm
    have hs : e.symm ∘ (e ∘ x) = x := by
      funext i
      exact e.symm_apply_apply (x i)
    rw [hs] at hm
    exact hm
  · intro h
    have hm := e.toAffineMap.span_eq_top_of_surjective e.surjective h
    change affineSpan ℝ (e '' Set.range x) = ⊤ at hm
    rw [← Set.range_comp] at hm
    exact hm

/-- Rank endpoint for the actual empirical covariance in the paper's model. -/
theorem empiricalCovariance_rank_le (x : Fin N → E d) :
    (empiricalCovariance x).rank ≤ N - 1 := by
  rw [empiricalCovariance_coordinates]
  exact Empirical.rank_covariance_le_all _

/-- Exact deterministic full-rank characterization in the actual Euclidean model. -/
theorem empiricalCovariance_posDef_iff_affineSpan (hN : 0 < N) (x : Fin N → E d) :
    (empiricalCovariance x).PosDef ↔ affineSpan ℝ (Set.range x) = ⊤ := by
  rw [empiricalCovariance_coordinates, Empirical.covariance_posDef_iff_affineSpan hN,
    affineSpan_coordinates_iff]

/-- Necessity of `N≥d+1` for the actual unregularized positive-definite covariance. -/
theorem dimension_add_one_le_of_empiricalCovariance_posDef (hN : 0 < N)
    (x : Fin N → E d) (h : (empiricalCovariance x).PosDef) : d + 1 ≤ N := by
  rw [empiricalCovariance_coordinates] at h
  exact Empirical.dimension_add_one_le_of_posDef hN _ h

/-- The endpoint sufficiency for i.i.d. sampling from any density, under its actual product law. -/
theorem ae_empiricalCovariance_posDef {μ : Measure (E d)} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hN : d + 1 ≤ N) :
    ∀ᵐ x : Fin N → E d ∂Measure.pi (fun _ => μ), (empiricalCovariance x).PosDef := by
  have hN' : Module.finrank ℝ (E d) + 1 ≤ N := by
    simpa only [E, finrank_euclideanSpace_fin] using hN
  filter_upwards [GaussianFullRank.ae_affineSpan_eq_top hμ hN'] with x hx
  exact (empiricalCovariance_posDef_iff_affineSpan (by omega) x).mpr hx

/-- Coordinate derivatives are transported by the actual continuous linear equivalence. -/
lemma hasDerivAt_coordinates {f : ℝ → E d} {v : E d} {t : ℝ}
    (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => coordinates (f s)) (coordinates v) t := by
  exact (EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf

/-- The converse derivative transport also uses continuity of the inverse equivalence. -/
lemma hasDerivAt_of_coordinates {f : ℝ → E d} {v : E d} {t : ℝ}
    (hf : HasDerivAt (fun s => coordinates (f s)) (coordinates v) t) :
    HasDerivAt f v t := by
  have h := (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf
  simpa only [Function.comp_def, coordinates, EuclideanSpace.equiv,
    PiLp.continuousLinearEquiv_symm_apply, WithLp.toLp_ofLp] using h

/-- Actual Euclidean affine particles satisfy the same mean/covariance closure. -/
theorem affine_particle_moment_closure (hN : 0 < N)
    (X : ℝ → Fin N → E d) (t : ℝ) (C : Mat d) (m : E d)
    (hX : ∀ i, HasDerivAt (fun s => X s i) (matVec C (X t i) - m) t) :
    HasDerivAt (fun s => empiricalMean (X s)) (matVec C (empiricalMean (X t)) - m) t ∧
    HasDerivAt (fun s => empiricalCovariance (X s))
      (C * empiricalCovariance (X t) + empiricalCovariance (X t) * Cᵀ) t := by
  have hXc : ∀ i, HasDerivAt (fun s => coordinates (X s i))
      (C *ᵥ coordinates (X t i) - coordinates m) t := by
    intro i
    exact hasDerivAt_coordinates (hX i)
  rcases Empirical.affine_particle_moment_closure hN
    (fun s i => coordinates (X s i)) t C (coordinates m) hXc with ⟨hmean, hcov⟩
  constructor
  · apply hasDerivAt_of_coordinates
    simpa only [empiricalMean_coordinates, coordinates, WithLp.ofLp_sub,
      matVec_coordinates] using hmean
  · simpa only [empiricalCovariance_coordinates] using hcov

/-- Actual standard Gaussian initialization attains the positive-definite endpoint. -/
theorem ae_standardGaussian_empiricalCovariance_posDef (hN : d + 1 ≤ N) :
    ∀ᵐ x : Fin N → E d ∂Measure.pi (fun _ => standardGaussian d),
      (empiricalCovariance x).PosDef := by
  letI : IsProbabilityMeasure (standardGaussian d) := by
    unfold standardGaussian
    exact Measure.isProbabilityMeasure_map
      (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.aemeasurable
  apply ae_empiricalCovariance_posDef (hN := hN)
  simpa only [standardGaussian, vec] using
    GaussianStatistics.gaussianEuclidean_absolutelyContinuous d

lemma hasDerivWithinAt_coordinates {f : ℝ → E d} {v : E d} {t : ℝ} {s : Set ℝ}
    (hf : HasDerivWithinAt f v s t) :
    HasDerivWithinAt (fun u => coordinates (f u)) (coordinates v) s t := by
  exact (EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t hf

lemma hasDerivWithinAt_of_coordinates {f : ℝ → E d} {v : E d} {t : ℝ} {s : Set ℝ}
    (hf : HasDerivWithinAt (fun u => coordinates (f u)) (coordinates v) s t) :
    HasDerivWithinAt f v s t := by
  have h := (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t hf
  simpa only [Function.comp_def, coordinates, EuclideanSpace.equiv,
    PiLp.continuousLinearEquiv_symm_apply, WithLp.toLp_ofLp] using h

/-- The affine derivative closure on a domain also includes physical time zero. -/
theorem affine_particle_moment_closure_within (hN : 0 < N)
    (X : ℝ → Fin N → E d) (t : ℝ) {s : Set ℝ} (C : Mat d) (m : E d)
    (hX : ∀ i, HasDerivWithinAt (fun u => X u i) (matVec C (X t i) - m) s t) :
    HasDerivWithinAt (fun u => empiricalMean (X u))
      (matVec C (empiricalMean (X t)) - m) s t ∧
    HasDerivWithinAt (fun u => empiricalCovariance (X u))
      (C * empiricalCovariance (X t) + empiricalCovariance (X t) * Cᵀ) s t := by
  have hXc : ∀ i, HasDerivWithinAt (fun u => coordinates (X u i))
      (C *ᵥ coordinates (X t i) - coordinates m) s t := by
    intro i
    exact hasDerivWithinAt_coordinates (hX i)
  rcases Empirical.affine_particle_moment_closure_within hN
    (fun u i => coordinates (X u i)) t C (coordinates m) hXc with ⟨hmean, hcov⟩
  constructor
  · apply hasDerivWithinAt_of_coordinates
    simpa only [empiricalMean_coordinates, coordinates, WithLp.ofLp_sub,
      matVec_coordinates] using hmean
  · simpa only [empiricalCovariance_coordinates] using hcov

/-- Coordinate dot products here retain the original Euclidean squared norm. -/
lemma coordinate_dot_self (x : E d) :
    coordinates x ⬝ᵥ coordinates x = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  simp only [coordinates, dotProduct, pow_two]
  rfl

/-- Schwarz symmetry follows from the actual `C²` potential. -/
theorem hessian_transpose (V : E d → ℝ) (hV : ContDiff ℝ 2 V) (x : E d) :
    (hessian V x)ᵀ = hessian V x := by
  ext i j
  exact hV.contDiffAt.isSymmSndFDerivAt (by simp)
    (vec d (Pi.single j 1)) (vec d (Pi.single i 1))

/-- Exact Gaussian Hessian averaging preserves this derived symmetry. -/
theorem meanHessian_transpose (V : E d → ℝ) (hV : ContDiff ℝ 2 V)
    (μ : E d) (S : Mat d) : (meanHessian V μ S)ᵀ = meanHessian V μ S := by
  ext i j
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => congrFun (congrFun (hessian_transpose V hV x) i) j

lemma momentField_mean_coordinates (V : E d → ℝ) (μ : E d) (S : Mat d) :
    coordinates ((momentField V μ S).1) =
      Mobility.momentMean (coordinates μ) (coordinates (meanGradient V μ S)) S
        (meanHessian V μ S) := by
  rw [Mobility.momentMean, coordinate_dot_self]
  rfl

lemma momentField_covariance_coordinates (V : E d → ℝ) (μ : E d) (S : Mat d) :
    (momentField V μ S).2 = Mobility.momentCov (coordinates μ)
      (coordinates (meanGradient V μ S)) S (meanHessian V μ S) := by
  simp only [momentField, Mobility.momentCov, outer_coordinates, two_smul]

lemma particleCoefficient_coordinates (V : E d → ℝ) (x : Fin N → E d) :
    particleCoefficient V x = MomentClosure.projectedCoefficient (coordinates (empiricalMean x))
      (coordinates (meanGradient V (empiricalMean x) (empiricalCovariance x)))
      (empiricalCovariance x) (meanHessian V (empiricalMean x) (empiricalCovariance x)) := rfl

lemma empiricalCovariance_posSemidef (x : Fin N → E d) :
    (empiricalCovariance x).PosSemidef := by
  rw [empiricalCovariance_coordinates]
  exact Empirical.covariance_posSemidef _

lemma affine_mean_eq_momentField (V : E d → ℝ) (x : Fin N → E d) :
    matVec (particleCoefficient V x) (empiricalMean x) -
      meanGradient V (empiricalMean x) (empiricalCovariance x) =
        (momentField V (empiricalMean x) (empiricalCovariance x)).1 := by
  apply (EuclideanSpace.equiv (Fin d) ℝ).injective
  change particleCoefficient V x *ᵥ coordinates (empiricalMean x) -
    coordinates (meanGradient V (empiricalMean x) (empiricalCovariance x)) =
      coordinates ((momentField V (empiricalMean x) (empiricalCovariance x)).1)
  rw [momentField_mean_coordinates, particleCoefficient_coordinates]
  exact MomentClosure.affine_mean_eq_momentMean _ _ _ _

lemma affine_covariance_eq_momentField (V : E d → ℝ) (hV : ContDiff ℝ 2 V)
    (x : Fin N → E d) :
    particleCoefficient V x * empiricalCovariance x +
      empiricalCovariance x * (particleCoefficient V x)ᵀ =
        (momentField V (empiricalMean x) (empiricalCovariance x)).2 := by
  rw [momentField_covariance_coordinates, particleCoefficient_coordinates]
  apply MomentClosure.affine_covariance_eq_momentCov
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (empiricalCovariance_posSemidef x).isHermitian.eq
  · exact meanHessian_transpose V hV _ _

/-- Exact local-domain closure of the actual projected particle field (2.5) into (2.3).
Hessian symmetry is proved from the actual C² hypothesis, rather than supplied as closure data. -/
theorem projected_particle_moment_closure_within (V : E d → ℝ) (hV : ContDiff ℝ 2 V)
    (hN : 0 < N) (X : ℝ → Fin N → E d) (t : ℝ) {s : Set ℝ}
    (hX : ∀ i, HasDerivWithinAt (fun u => X u i) (particleField V (X t) i) s t) :
    HasDerivWithinAt (fun u => empiricalMean (X u))
      (momentField V (empiricalMean (X t)) (empiricalCovariance (X t))).1 s t ∧
    HasDerivWithinAt (fun u => empiricalCovariance (X u))
      (momentField V (empiricalMean (X t)) (empiricalCovariance (X t))).2 s t := by
  rcases affine_particle_moment_closure_within hN X t (particleCoefficient V (X t))
    (meanGradient V (empiricalMean (X t)) (empiricalCovariance (X t))) hX with ⟨hmean, hcov⟩
  rw [affine_mean_eq_momentField] at hmean
  rw [affine_covariance_eq_momentField V hV] at hcov
  exact ⟨hmean, hcov⟩

/-- Empirical moments of an actual projected particle solution solve the original moment ODE. -/
theorem particleSolution_momentSolution (V : E d → ℝ) (hV : ContDiff ℝ 2 V)
    (hN : 0 < N) (X : ℝ → Fin N → E d) (hX : particleSolution V X) :
    momentSolution V (fun t => empiricalMean (X t)) (fun t => empiricalCovariance (X t)) := by
  refine ⟨hX.1, ?_⟩
  intro t ht
  exact projected_particle_moment_closure_within V hV hN X t (hX.2 t ht)

/-- Coordinates of the paper's centered affine lift. -/
lemma affine_lift_coordinates (x : Fin N → E d) (b : E d) (L : Mat d) :
    (fun i => coordinates (b + matVec L (x i - empiricalMean x))) =
      (fun i => coordinates b + L *ᵥ Empirical.centered (fun j => coordinates (x j)) i) := by
  funext i
  change coordinates b + L *ᵥ (coordinates (x i) - coordinates (empiricalMean x)) = _
  rw [empiricalMean_coordinates]
  rfl

/-- The actual Euclidean affine lift has the prescribed empirical mean (6.2). -/
theorem empiricalMean_affine_lift (hN : 0 < N) (x : Fin N → E d) (b : E d) (L : Mat d) :
    empiricalMean (fun i => b + matVec L (x i - empiricalMean x)) = b := by
  apply (EuclideanSpace.equiv (Fin d) ℝ).injective
  change coordinates (empiricalMean (fun i => b + matVec L (x i - empiricalMean x))) = coordinates b
  rw [empiricalMean_coordinates, affine_lift_coordinates, Empirical.mean_affine_lift hN]

/-- Exact empirical covariance of the actual Euclidean affine lift (6.3). -/
theorem empiricalCovariance_affine_lift (hN : 0 < N) (x : Fin N → E d)
    (b : E d) (L : Mat d) :
    empiricalCovariance (fun i => b + matVec L (x i - empiricalMean x)) =
      L * empiricalCovariance x * Lᵀ := by
  rw [empiricalCovariance_coordinates, affine_lift_coordinates,
    Empirical.covariance_affine_lift hN, ← empiricalCovariance_coordinates]

lemma standardizedCloud_coordinates (x : Fin N → E d) (R : Mat d) (i : Fin N) :
    coordinates (standardizedCloud x R i) =
      R *ᵥ Empirical.centered (fun j => coordinates (x j)) i := by
  change R *ᵥ (coordinates (x i) - coordinates (empiricalMean x)) = _
  rw [empiricalMean_coordinates]
  rfl

lemma sqNorm_coordinates (x : E d) : Standardization.sqNorm (coordinates x) = ‖x‖ ^ 2 := by
  simpa only [coordinates, WithLp.toLp_ofLp] using
    Standardization.sqNorm_eq_euclidean (coordinates x)

/-- Equation (6.9) in the actual Euclidean norm, original sample covariance and principal whitening. -/
theorem principal_standardized_identity_and_bound (hN : 0 < N) (x : Fin N → E d)
    (hS : (empiricalCovariance x).PosDef) :
    let H := covarianceRoot (empiricalCovariance x)
    ((N : ℝ)⁻¹ * ∑ i, ‖standardizedCloud x H⁻¹ i - x i‖ ^ 2 =
      frobSq (1 - H) + ‖empiricalMean x‖ ^ 2) ∧
    ((N : ℝ)⁻¹ * ∑ i, ‖standardizedCloud x H⁻¹ i - x i‖ ^ 2 ≤
      frobSq (1 - empiricalCovariance x) + ‖empiricalMean x‖ ^ 2) := by
  have hSc : (Empirical.covariance (fun i => coordinates (x i))).PosDef := by
    rw [← empiricalCovariance_coordinates]
    exact hS
  have h := Standardization.principal_standardized_identity_and_bound hN
    (fun i => coordinates (x i)) hSc
  rw [← empiricalCovariance_coordinates] at h
  have hz (i : Fin N) :
      Standardization.standardized (fun i => coordinates (x i))
        (CFC.sqrt (empiricalCovariance x)) i =
      coordinates (standardizedCloud x (CFC.sqrt (empiricalCovariance x))⁻¹ i) := by
    symm
    exact standardizedCloud_coordinates x _ i
  have hc (i : Fin N) :
      Standardization.sqNorm
        (Standardization.standardized (fun i => coordinates (x i))
          (CFC.sqrt (empiricalCovariance x)) i - coordinates (x i)) =
      ‖standardizedCloud x (CFC.sqrt (empiricalCovariance x))⁻¹ i - x i‖ ^ 2 := by
    rw [hz]
    exact sqNorm_coordinates _
  simpa only [hc, ← empiricalMean_coordinates, sqNorm_coordinates,
    Standardization.frobSq, frobSq, covarianceRoot] using h

/-- Any whitening in the paper produces a cloud with exactly zero mean and identity covariance. -/
theorem standardizedCloud_moments (hN : 0 < N) (x : Fin N → E d) (R : Mat d)
    (hR : IsWhitening x R) :
    empiricalMean (standardizedCloud x R) = 0 ∧
      empiricalCovariance (standardizedCloud x R) = 1 := by
  have hm := empiricalMean_affine_lift hN x (0 : E d) R
  have hc := empiricalCovariance_affine_lift hN x (0 : E d) R
  constructor
  · simpa only [zero_add, standardizedCloud] using hm
  · have he : empiricalCovariance (standardizedCloud x R) =
        R * empiricalCovariance x * Rᵀ := by
      simpa only [zero_add, standardizedCloud] using hc
    exact he.trans hR

end Paper38.ModelBridges
