import BoundaryReduction.GaussianGrow

open Real Set MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ}

/-- A centered Gaussian with symmetric positive definite covariance SigmaOp admits
exactly the precision specification used by the mixture proofs. The inverse
operator is constructed from SigmaOp, rather than assumed as extra statistical data. -/
theorem exists_precision_of_covariance
    (SigmaOp : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
    (hsymSigmaOp : ∀ u v : Space d, inner ℝ u (SigmaOp v) = inner ℝ v (SigmaOp u))
    (hposSigmaOp : ∀ v : Space d, v ≠ 0 → 0 < inner ℝ v (SigmaOp v))
    (hcovSigmaOp : ∀ u v : Space d, covariance (innerSL ℝ u) (innerSL ℝ v) Z = inner ℝ u (SigmaOp v)) :
    ∃ K : Space d →L[ℝ] Space d,
      (∀ v, SigmaOp (K v) = v) ∧ (∀ v, K (SigmaOp v) = v) ∧
      (∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u)) ∧ Function.Surjective K ∧
      (∀ v : Space d, variance (precisionForm K v) Z = inner ℝ v (K v)) := by
  have hinj : Function.Injective SigmaOp := by
    intro u v huv
    by_contra hne
    have hdiff : u-v ≠ 0 := sub_ne_zero.mpr hne
    have hp := hposSigmaOp (u-v) hdiff
    have hz : SigmaOp (u-v) = 0 := by rw [map_sub,huv,sub_self]
    rw [hz,inner_zero_right] at hp
    exact (lt_irrefl 0 hp)
  let e : Space d ≃L[ℝ] Space d :=
    (LinearEquiv.ofInjectiveEndo SigmaOp.toLinearMap hinj).toContinuousLinearEquiv
  let K : Space d →L[ℝ] Space d := e.symm.toContinuousLinearMap
  have hSigmaOpK (v : Space d) : SigmaOp (K v) = v := e.apply_symm_apply v
  have hKSigmaOp (v : Space d) : K (SigmaOp v) = v := e.symm_apply_apply v
  have hsymK (u v : Space d) : inner ℝ u (K v) = inner ℝ v (K u) := by
    calc
      _ = inner ℝ (SigmaOp (K u)) (K v) := by rw [hSigmaOpK]
      _ = inner ℝ (K v) (SigmaOp (K u)) := real_inner_comm _ _
      _ = inner ℝ (K u) (SigmaOp (K v)) := hsymSigmaOp _ _
      _ = inner ℝ v (K u) := by rw [hSigmaOpK,real_inner_comm]
  refine ⟨K,hSigmaOpK,hKSigmaOp,hsymK,e.symm.surjective,?_⟩
  intro v
  have hform : precisionForm K v = innerSL ℝ (K v) := by
    ext x
    rw [precisionForm_apply,hsymK,real_inner_comm]
    rfl
  rw [hform,← covariance_self (by fun_prop),hcovSigmaOp,hSigmaOpK,real_inner_comm]

end BoundaryReduction.Gaussian
