import Paper35.CovarianceSpectral
import Paper35.GaussianSpectrum
import Mathlib.Analysis.InnerProductSpace.Positive

/-! The actual covariance form is identified with its Riesz operator and
coordinate covariance matrix. Its norm is the largest ordinary eigenvalue,
including zero covariance, in every positive dimension. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Paper35.Source.WeightedModel
variable {d : ℕ}

/-- Riesz operator of the actual tilted covariance form. -/
def covarianceOperator (m : WeightedModel d) : Space d →L[ℝ] Space d :=
  InnerProductSpace.continuousLinearMapOfBilin m.covarianceForm

lemma covarianceOperator_inner (m : WeightedModel d) (u v : Space d) :
    inner ℝ (m.covarianceOperator u) v = m.covarianceForm u v :=
  InnerProductSpace.continuousLinearMapOfBilin_apply m.covarianceForm u v

lemma covarianceOperator_norm (m : WeightedModel d) :
    ‖m.covarianceOperator‖ = m.covarianceSpectralNorm := by
  apply ContinuousLinearMap.opNorm_ext
  intro u
  change ‖(InnerProductSpace.toDual ℝ (Space d)).symm (m.covarianceForm u)‖ = ‖m.covarianceForm u‖
  exact (InnerProductSpace.toDual ℝ (Space d)).symm.norm_map _

lemma covarianceForm_comm (m : WeightedModel d) (u v : Space d) :
    m.covarianceForm u v = m.covarianceForm v u := by
  simp only [covarianceForm, ContinuousLinearMap.bilinearComp_apply]
  exact covarianceBilinDual_comm _ _

lemma covarianceForm_eq_covariance (m : WeightedModel d)
    (hW : MemLp (fun w => w) 2 m.tilted) (u v : Space d) :
    m.covarianceForm u v = covariance (fun w => inner ℝ u w) (fun w => inner ℝ v w) m.tilted := by
  simp only [covarianceForm, ContinuousLinearMap.bilinearComp_apply]
  exact covarianceBilinDual_eq_covariance hW _ _

lemma covarianceOperator_symmetric (m : WeightedModel d) :
    (m.covarianceOperator : Space d →ₗ[ℝ] Space d).IsSymmetric := by
  intro u v
  change inner ℝ (m.covarianceOperator u) v = inner ℝ u (m.covarianceOperator v)
  calc
    _ = m.covarianceForm u v := m.covarianceOperator_inner u v
    _ = m.covarianceForm v u := m.covarianceForm_comm u v
    _ = inner ℝ (m.covarianceOperator v) u := (m.covarianceOperator_inner v u).symm
    _ = _ := real_inner_comm _ _

lemma covarianceOperator_positive (m : WeightedModel d)
    (hW : MemLp (fun w => w) 2 m.tilted) :
    (m.covarianceOperator : Space d →ₗ[ℝ] Space d).IsPositive := by
  refine ⟨m.covarianceOperator_symmetric, fun u => ?_⟩
  change 0 ≤ inner ℝ (m.covarianceOperator u) u
  rw [covarianceOperator_inner, covarianceForm_eq_covariance m hW,
    covariance_self (by fun_prop)]
  exact variance_nonneg _ _

/-- Coordinate matrix of the actual covariance Riesz operator. -/
def covarianceMatrix (m : WeightedModel d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.toEuclideanLin.symm m.covarianceOperator.toLinearMap

lemma toEuclideanLin_covarianceMatrix (m : WeightedModel d) :
    Matrix.toEuclideanLin m.covarianceMatrix = m.covarianceOperator.toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

lemma covarianceMatrix_positive (m : WeightedModel d)
    (hW : MemLp (fun w => w) 2 m.tilted) : m.covarianceMatrix.PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  rw [toEuclideanLin_covarianceMatrix]
  exact m.covarianceOperator_positive hW

lemma matrix_covarianceOperator (m : WeightedModel d) :
    GaussianIndependent.covarianceOperator m.covarianceMatrix = m.covarianceOperator := by
  apply ContinuousLinearMap.ext
  intro u
  change Matrix.toEuclideanLin m.covarianceMatrix u = m.covarianceOperator u
  rw [toEuclideanLin_covarianceMatrix]
  rfl

lemma matrix_covarianceMax (m : WeightedModel d) :
    GaussianIndependent.covarianceMax m.covarianceMatrix = m.covarianceSpectralNorm := by
  rw [GaussianIndependent.covarianceMax, matrix_covarianceOperator, covarianceOperator_norm]

/-- Largest ordinary matrix eigenvalue, defined independently of an operator
norm. Its equivalence with the covariance form norm is proved below. -/
def matrixLambdaMax (S : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sSup {ell : ℝ | Module.End.HasEigenvalue S.toEuclideanLin ell}

/-- The covariance form norm is an actual greatest eigenvalue, rather than
only an upper bound on the spectrum. -/
theorem covarianceSpectralNorm_isGreatest_eigenvalue (m : WeightedModel d)
    (hW : MemLp (fun w => w) 2 m.tilted) (hd : 1 ≤ d) :
    IsGreatest {ell : ℝ | Module.End.HasEigenvalue m.covarianceMatrix.toEuclideanLin ell}
      m.covarianceSpectralNorm := by
  have hS := m.covarianceMatrix_positive hW
  obtain ⟨v,hv,he⟩ := GaussianIndependent.covarianceMax_eigenvector_of_dimension
    m.covarianceMatrix hS hd
  rw [matrix_covarianceMax] at he
  constructor
  · apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    refine ⟨Module.End.mem_eigenspace_iff.mpr he, ?_⟩
    exact norm_ne_zero_iff.mp (by rw [hv]; norm_num)
  · intro ell hell
    obtain ⟨x,hxe,hx⟩ := hell.exists_hasEigenvector
    have hxe' : GaussianIndependent.covarianceOperator m.covarianceMatrix x = ell • x :=
      Module.End.mem_eigenspace_iff.mp hxe
    have hle := GaussianIndependent.eigenvalue_le_covarianceMax m.covarianceMatrix hS hx hxe'
    rwa [matrix_covarianceMax] at hle

theorem matrixLambdaMax_covarianceMatrix (m : WeightedModel d)
    (hW : MemLp (fun w => w) 2 m.tilted) (hd : 1 ≤ d) :
    matrixLambdaMax m.covarianceMatrix = m.covarianceSpectralNorm :=
  (m.covarianceSpectralNorm_isGreatest_eigenvalue hW hd).csSup_eq

/-- The represented matrix has exactly the ordinary coordinate covariances. -/
theorem covarianceMatrix_apply (m : WeightedModel d)
    (hW : MemLp (fun w => w) 2 m.tilted) (i j : Fin d) :
    m.covarianceMatrix i j = covariance (fun w : Space d => w i) (fun w : Space d => w j) m.tilted := by
  have he : m.covarianceMatrix i j =
      (m.covarianceOperator (EuclideanSpace.single j 1)) i := by
    have h := congrArg (fun A : Space d →ₗ[ℝ] Space d =>
      (A (EuclideanSpace.single j 1)) i) (m.toEuclideanLin_covarianceMatrix)
    change Matrix.mulVec m.covarianceMatrix (Pi.single j 1) i =
      (m.covarianceOperator (EuclideanSpace.single j 1)) i at h
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h
  calc
    _ = (m.covarianceOperator (EuclideanSpace.single j 1)) i := he
    _ = inner ℝ (m.covarianceOperator (EuclideanSpace.single j 1)) (EuclideanSpace.single i 1) := by
      simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul]
    _ = m.covarianceForm (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) :=
      m.covarianceOperator_inner _ _
    _ = m.covarianceForm (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
      m.covarianceForm_comm _ _
    _ = _ := by
      simpa only [EuclideanSpace.inner_single_left, conj_trivial, one_mul] using
        (m.covarianceForm_eq_covariance hW (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))

/-- With a constant envelope the same matrix is the covariance of the
original weight law, as required by equation (2.8). -/
theorem covarianceMatrix_apply_of_constant (m : WeightedModel d) (B : ℝ≥0)
    (hb : ∀ᵐ w ∂m.weights, m.b₀ w = B)
    (hW : MemLp (fun w => w) 2 m.weights) (i j : Fin d) :
    m.covarianceMatrix i j = covariance (fun w : Space d => w i) (fun w : Space d => w j) m.weights := by
  have ht : MemLp (fun w => w) 2 m.tilted := by
    rw [m.tilted_eq_weights_of_constant B hb]
    exact hW
  rw [m.covarianceMatrix_apply ht, m.tilted_eq_weights_of_constant B hb]

/-- A positive-length arclength Probe cannot live in zero-dimensional space. -/
lemma dimension_pos_of_probe (p : Probe d) : 1 ≤ d := by
  by_contra hd
  have hd0 : d = 0 := by omega
  subst d
  have hz : eVariationOn p.curve (Icc 0 p.length) = 0 :=
    eVariationOn.constant_on Set.subsingleton_of_subsingleton
  have hp := ENNReal.ofReal_pos.mpr p.length_pos
  rw [← p.arclength,hz] at hp
  exact (lt_irrefl (0 : ℝ≥0∞)) hp

/-- Literal constant-envelope spectral consequence of (2.7), now expressed
using the largest eigenvalue of the genuine original covariance matrix. -/
theorem expectedDensity_le_lambdaMax (hcov : WeightedCovarianceClaim (d := d))
    (m : WeightedModel d) (B : ℝ≥0) (hb : ∀ᵐ w ∂m.weights, m.b₀ w = B)
    (hW : MemLp (fun w => w) 2 m.weights) (K : ℕ) (hK : 2 ≤ K) (p : Probe d) :
    m.expectedDensity K p ≤ ((K : ℝ≥0∞) * B / ENNReal.ofReal (Real.sqrt 3)) *
      ENNReal.ofReal (Real.sqrt (matrixLambdaMax m.covarianceMatrix)) := by
  have ht : MemLp (fun w => w) 2 m.tilted := by
    rw [m.tilted_eq_weights_of_constant B hb]
    exact hW
  rw [matrixLambdaMax_covarianceMatrix m ht (dimension_pos_of_probe p)]
  have h := expectedDensity_le_spectral hcov m ht K hK p
  rwa [m.average_eq_of_constant B hb] at h

end Paper35.Source.WeightedModel
