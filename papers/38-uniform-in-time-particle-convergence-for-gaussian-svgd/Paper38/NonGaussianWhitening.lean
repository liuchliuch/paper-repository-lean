import Paper38.GaussianAffine
import Paper38.ExternalEmpiricalTransport
import Paper38.TransportGluing
import Paper38.AffineLifting
import Mathlib.Probability.Independence.Basic

/-! Invertible affine restoration preserves the non-Gaussian shape defect in
Corollary 2.7. All laws and costs below are the actual Model pushforwards and
quadratic transport infima. -/
noncomputable section
namespace Paper38.NonGaussianWhitening
open MeasureTheory ProbabilityTheory
open Model ExternalEmpiricalTransport
open scoped Matrix MatrixOrder ENNReal
variable {d : ℕ}

/-- Applying the inverse affine map to any law and then restoring it gives the
original law. This measure identity requires no moment hypothesis. -/
theorem affine_restoration (ν : Measure (E d)) (μ : E d) (A : Mat d)
    (hA : IsUnit A) :
    (ν.map (fun y => matVec A⁻¹ (y-μ))).map (fun z => μ+matVec A z) = ν := by
  have hwhite : Measurable (fun y : E d => matVec A⁻¹ (y-μ)) :=
    ((GaussianAffine.continuous_matVec A⁻¹).comp (continuous_id.sub continuous_const)).measurable
  have hrestore : Measurable (fun z : E d => μ+matVec A z) :=
    (continuous_const.add (GaussianAffine.continuous_matVec A)).measurable
  rw [Measure.map_map hrestore hwhite]
  have hid : (fun z : E d => μ+matVec A z) ∘ (fun y => matVec A⁻¹ (y-μ)) = id := by
    funext y
    change μ + matVec A (matVec A⁻¹ (y-μ)) = y
    rw [← GaussianAffine.matVec_mul,
      Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)]
    simp only [matVec, Matrix.one_mulVec, vec, WithLp.toLp_ofLp]
    abel
  rw [hid, Measure.map_id]

/-- If the principal-coordinate whitened law were standard Gaussian, affine
restoration would make the original law exactly the matching Gaussian. -/
theorem law_eq_gaussian_of_whitened_eq_standard
    (ν : Measure (E d)) (μ : E d) (A : Mat d) (hA : IsUnit A)
    (hwhite : ν.map (fun y => matVec A⁻¹ (y-μ)) = standardGaussian d) :
    ν = gaussianLaw μ A := by
  calc
    ν = (ν.map (fun y => matVec A⁻¹ (y-μ))).map (fun z => μ+matVec A z) :=
      (affine_restoration ν μ A hA).symm
    _ = gaussianLaw μ A := by rw [hwhite]; rfl

/-- A non-Gaussian law has a nonzero standardized shape defect under every
invertible affine standardization, in particular under the actual principal root. -/
theorem whitened_ne_standard_of_nongaussian
    (ν : Measure (E d)) (μ : E d) (A : Mat d) (hA : IsUnit A)
    (hnon : ν ≠ gaussianLaw μ A) :
    ν.map (fun y => matVec A⁻¹ (y-μ)) ≠ standardGaussian d := by
  intro heq
  exact hnon (law_eq_gaussian_of_whitened_eq_standard ν μ A hA heq)

/-- Actual principal population whitening preserves non-Gaussianity. The mean
and covariance in the conclusion are the genuine population integrals. -/
theorem population_whitened_ne_standard
    (ν : Measure (E d)) (hS : (populationCovariance ν).PosDef)
    (hnon : ν ≠ gaussianLaw (populationMean ν) (covarianceRoot (populationCovariance ν))) :
    ν.map (fun y => matVec (covarianceRoot (populationCovariance ν))⁻¹
      (y-populationMean ν)) ≠ standardGaussian d :=
  whitened_ne_standard_of_nongaussian ν _ _ hS.posDef_sqrt.isUnit hnon

/-- The non-Gaussian population shape has strictly positive actual quadratic
transport cost. Only the ordinary zero-cost separation theorem is supplied. -/
theorem population_whitened_cost_pos
    (separation : QuadraticTransportSeparation d)
    (ν : Measure (E d)) [IsProbabilityMeasure ν]
    (hS : (populationCovariance ν).PosDef)
    (hnon : ν ≠ gaussianLaw (populationMean ν) (covarianceRoot (populationCovariance ν))) :
    0 < Transport.w2sq
      (ν.map (fun y => matVec (covarianceRoot (populationCovariance ν))⁻¹
        (y-populationMean ν))) (standardGaussian d) := by
  let f : E d → E d := fun y => matVec (covarianceRoot (populationCovariance ν))⁻¹
    (y-populationMean ν)
  have hf : Continuous f :=
    (GaussianAffine.continuous_matVec _).comp (continuous_id.sub continuous_const)
  letI : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hf.measurable.aemeasurable
  letI := GaussianAffine.standardGaussian_probability d
  exact (pos_iff_ne_zero).mpr (fun hzero =>
    population_whitened_ne_standard ν hS hnon (separation (ν.map f) (standardGaussian d) hzero))

/-- The finite joint law of an i.i.d. sequence on an arbitrary probability
space is the actual product law used by the proved full-rank theorem. -/
theorem iid_initialCloud_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure (E d)) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → E d) (hX : ∀ n, Measurable (X n))
    (hind : iIndepFun X P) (hlaw : ∀ n, Measure.map (X n) P = ν) (N : ℕ) :
    P.map (fun ω (i : Fin N) => X i ω) = Measure.pi (fun _ : Fin N => ν) := by
  have hfin : iIndepFun (fun i : Fin N => X i) P :=
    iIndepFun.precomp Fin.val_injective hind
  have hjoint := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i : Fin N => (hX i).aemeasurable)).mp hfin
  simpa only [hlaw] using hjoint

/-- Actual positive definiteness for any one admissible sample count on the
common i.i.d. probability space; density is discharged by the product-law proof. -/
theorem ae_iid_empiricalCovariance_posDef {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure (E d)) [IsProbabilityMeasure ν] (hac : ν ≪ volume)
    (X : ℕ → Ω → E d) (hX : ∀ n, Measurable (X n))
    (hind : iIndepFun X P) (hlaw : ∀ n, Measure.map (X n) P = ν)
    (N : ℕ) (hN : d+1 ≤ N) :
    ∀ᵐ ω ∂P, (empiricalCovariance (fun i : Fin N => X i ω)).PosDef := by
  have hprod := ModelBridges.ae_empiricalCovariance_posDef hac hN
  have hjoint := iid_initialCloud_law P ν X hX hind hlaw N
  have hmap : ∀ᵐ x ∂P.map (fun ω (i : Fin N) => X i ω), (empiricalCovariance x).PosDef := by
    rw [hjoint]
    exact hprod
  have hmeas : Measurable (fun ω (i : Fin N) => X i ω) :=
    measurable_pi_lambda _ (fun i => hX i)
  exact MeasureTheory.ae_of_ae_map hmeas.aemeasurable hmap

/-- One full-measure event covers all sample counts at and above the source
endpoint N=d+1. This is a countable intersection, not a full-rank baseline. -/
theorem ae_iid_empiricalCovariance_posDef_all {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure (E d)) [IsProbabilityMeasure ν] (hac : ν ≪ volume)
    (X : ℕ → Ω → E d) (hX : ∀ n, Measurable (X n))
    (hind : iIndepFun X P) (hlaw : ∀ n, Measure.map (X n) P = ν) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, d+1 ≤ N →
      (empiricalCovariance (fun i : Fin N => X i ω)).PosDef := by
  apply ae_all_iff.mpr
  intro N
  by_cases hN : d+1 ≤ N
  · filter_upwards [ae_iid_empiricalCovariance_posDef P ν hac X hX hind hlaw N hN] with ω hω
    exact fun _ => hω
  · exact Filter.Eventually.of_forall fun _ h => False.elim (hN h)

/-- Positive-count indexing matching the raw strong-law convention n+1. -/
theorem ae_iid_empiricalCovariance_posDef_succ_all {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure (E d)) [IsProbabilityMeasure ν] (hac : ν ≪ volume)
    (X : ℕ → Ω → E d) (hX : ∀ n, Measurable (X n))
    (hind : iIndepFun X P) (hlaw : ∀ n, Measure.map (X n) P = ν) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, d ≤ n →
      (empiricalCovariance (fun i : Fin (n+1) => X i ω)).PosDef := by
  filter_upwards [ae_iid_empiricalCovariance_posDef_all P ν hac X hX hind hlaw] with ω hω
  intro n hn
  exact hω (n+1) (by omega)

/-- Every actual Hermitian eigenvalue of a scalar covariance is the scalar. -/
theorem eigenvalues_scalar {S : Mat d} (hS : S.IsHermitian) (c : ℝ)
    (hscalar : S = c • (1 : Mat d)) (i : Fin d) : hS.eigenvalues i = c := by
  have hmv : S *ᵥ ⇑(hS.eigenvectorBasis i) = c • ⇑(hS.eigenvectorBasis i) := by
    calc
      S *ᵥ ⇑(hS.eigenvectorBasis i) = (c • (1 : Mat d)) *ᵥ ⇑(hS.eigenvectorBasis i) :=
        congrArg (fun B : Mat d => B *ᵥ ⇑(hS.eigenvectorBasis i)) hscalar
      _ = _ := by simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hS.eigenvalues_eq i, hmv]
  simp only [dotProduct_smul, smul_eq_mul]
  have hn : ‖hS.eigenvectorBasis i‖ = 1 := hS.eigenvectorBasis.orthonormal.1 i
  have hid : (star ⇑(hS.eigenvectorBasis i)) ⬝ᵥ ⇑(hS.eigenvectorBasis i) = (1 : ℝ) := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, real_inner_self_eq_norm_sq, hn]
    norm_num
  rw [hid, mul_one]
  rfl

/-- In the isotropic case both actual spectral distortion factors equal σ²,
so the source lower/upper large-N floors squeeze to its stated exact limit. -/
theorem isotropic_spectral_factors [NeZero d] (A : Mat d) (σ : ℝ)
    (hcov : A*A.transpose = σ^2 • (1 : Mat d)) :
    (AffineLifting.covarianceMin A : ℝ) = σ^2 ∧
      (AffineLifting.covarianceMax A : ℝ) = σ^2 := by
  have heig : (AffineLifting.covariancePSD A).isHermitian.eigenvalues = fun _ => σ^2 := by
    funext i
    exact eigenvalues_scalar (AffineLifting.covariancePSD A).isHermitian (σ^2) hcov i
  constructor
  · change AffineLifting.eigenMin (A*A.transpose) _ = σ^2
    unfold AffineLifting.eigenMin
    rw [heig]
    simp
  · change AffineLifting.eigenMax (A*A.transpose) _ = σ^2
    unfold AffineLifting.eigenMax
    rw [heig]
    simp

end Paper38.NonGaussianWhitening
