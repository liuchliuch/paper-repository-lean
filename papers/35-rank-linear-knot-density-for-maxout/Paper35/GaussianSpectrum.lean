import Paper35.GaussianSharpness
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! Generic PSD covariance spectrum facts, separate from the independent
Gaussian model and adapter. The operator norm is identified with an actual
greatest eigenvalue, including zero covariance in every positive dimension. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace Paper35.GaussianIndependent
open Source GaussianLift GaussianMarked
variable {d : ℕ}

/-- The Euclidean Riesz covariance operator. -/
def covarianceOperator (S : Matrix (Fin d) (Fin d) ℝ) : Space d →L[ℝ] Space d :=
  (Matrix.toEuclideanLin S).toContinuousLinearMap

/-- Largest PSD eigenvalue, in its invariant operator-norm form. -/
def covarianceMax (S : Matrix (Fin d) (Fin d) ℝ) : ℝ := ‖covarianceOperator S‖

lemma rootMap_adjoint_comp (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) :
    (rootMap S).adjoint.comp (rootMap S) = covarianceOperator S := by
  rw [(rootMap_symmetric S).clm_adjoint_eq]
  apply ContinuousLinearMap.ext
  intro x
  exact rootMap_sq S hS x

lemma norm_rootMap_squared (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) :
    ‖rootMap S‖^2 = covarianceMax S := by
  have h := ContinuousLinearMap.norm_adjoint_comp_self (rootMap S)
  rw [rootMap_adjoint_comp S hS] at h
  simpa only [covarianceMax, pow_two] using h.symm

lemma norm_rootMap_eq_sqrt (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) :
    ‖rootMap S‖ = Real.sqrt (covarianceMax S) := by
  rw [← norm_rootMap_squared S hS, Real.sqrt_sq (norm_nonneg _)]

lemma covariance_quadratic (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (x : Space d) :
    (covarianceOperator S).reApplyInnerSelf x = ‖rootMap S x‖^2 := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  change inner ℝ ((covarianceOperator S) x) x = _
  rw [real_inner_comm]
  exact (norm_rootMap_sq S hS x).symm

/-- The operator-norm definition is an actual eigenvalue of the covariance,
with a unit eigenvector, whenever that eigenvalue is positive. -/
theorem covarianceMax_eigenvector (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hpos : 0 < covarianceMax S) :
    ∃ v : Space d, ‖v‖ = 1 ∧ (covarianceOperator S) v = covarianceMax S • v := by
  have hA : rootMap S ≠ 0 := by
    intro h
    have hh := norm_rootMap_squared S hS
    rw [h, norm_zero, zero_pow (by norm_num)] at hh
    linarith
  obtain ⟨v, hv, hAv⟩ := GaussianSharpness.exists_unit_norm_attaining (rootMap S) hA
  have hs : IsSelfAdjoint (covarianceOperator S) :=
    (Matrix.isHermitian_iff_isSymmetric.1 hS.1).isSelfAdjoint
  have hmax : IsMaxOn (covarianceOperator S).reApplyInnerSelf (Metric.sphere 0 ‖v‖) v := by
    intro w hw
    have hw' : ‖w‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right, hv] using hw
    change (covarianceOperator S).reApplyInnerSelf w ≤ (covarianceOperator S).reApplyInnerSelf v
    rw [covariance_quadratic S hS w, covariance_quadratic S hS v, hAv]
    have hb := (rootMap S).le_opNorm w
    rw [hw', mul_one] at hb
    nlinarith [norm_nonneg (rootMap S w), norm_nonneg (rootMap S)]
  have he := hs.eq_smul_self_of_isLocalExtrOn (Or.inr hmax.localize)
  have hr : (covarianceOperator S).rayleighQuotient v = covarianceMax S := by
    rw [ContinuousLinearMap.rayleighQuotient, covariance_quadratic S hS, hv, hAv,
      one_pow, div_one, norm_rootMap_squared S hS]
  rw [hr] at he
  exact ⟨v, hv, he⟩

/-- Every real covariance eigenvalue is at most the defined maximum. Thus the
previous eigenvector identifies it with the ordinary largest PSD eigenvalue. -/
theorem eigenvalue_le_covarianceMax (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    {ell : ℝ} {x : Space d} (hx : x ≠ 0) (he : covarianceOperator S x = ell • x) :
    ell ≤ covarianceMax S := by
  have hq : ell * ‖x‖^2 = ‖rootMap S x‖^2 := by
    have h := covariance_quadratic S hS x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply] at h
    change inner ℝ ((covarianceOperator S) x) x = _ at h
    simpa only [he, real_inner_smul_left, real_inner_self_eq_norm_sq] using h
  have hb := (rootMap S).le_opNorm x
  have hsq : ‖rootMap S x‖^2 ≤ ‖rootMap S‖^2 * ‖x‖^2 := by
    nlinarith [norm_nonneg (rootMap S x), norm_nonneg (rootMap S), norm_nonneg x]
  rw [norm_rootMap_squared S hS, ← hq] at hsq
  exact (mul_le_mul_iff_left₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx))).mp hsq

/-- Including zero covariance, the defined maximum is an eigenvalue in every
positive dimension. Together with `eigenvalue_le_covarianceMax` this is the
usual largest eigenvalue, not merely an upper bound for it. -/
theorem covarianceMax_eigenvector_of_dimension (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosSemidef) (hd : 1 ≤ d) :
    ∃ v : Space d, ‖v‖ = 1 ∧ covarianceOperator S v = covarianceMax S • v := by
  by_cases hp : 0 < covarianceMax S
  · exact covarianceMax_eigenvector S hS hp
  · have hz : covarianceMax S = 0 := le_antisymm (le_of_not_gt hp) (norm_nonneg _)
    have hzero : covarianceOperator S = 0 := norm_eq_zero.mp hz
    let i : Fin d := ⟨0, by omega⟩
    refine ⟨EuclideanSpace.single i 1, by simp, ?_⟩
    rw [hzero, hz]
    simp

lemma covarianceOperator_scalar_identity (c : ℝ) :
    covarianceOperator (c • (1 : Matrix (Fin d) (Fin d) ℝ)) =
      c • (ContinuousLinearMap.id ℝ (Space d)) := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanLin (c • (1 : Matrix (Fin d) (Fin d) ℝ)) x = c • x
  ext i
  simp [Matrix.toEuclideanLin_apply]

lemma covarianceMax_isotropic (hd : 1 ≤ d) (s : ℝ) :
    covarianceMax (s^2 • (1 : Matrix (Fin d) (Fin d) ℝ)) = s^2 := by
  letI : NeZero d := ⟨by omega⟩
  unfold covarianceMax
  rw [covarianceOperator_scalar_identity, norm_smul, ContinuousLinearMap.norm_id,
    mul_one, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s)]

end Paper35.GaussianIndependent
