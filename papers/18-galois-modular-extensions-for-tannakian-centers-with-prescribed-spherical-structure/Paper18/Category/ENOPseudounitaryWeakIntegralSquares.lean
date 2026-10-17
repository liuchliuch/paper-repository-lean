import Paper18.Category.ENOPseudounitaryNumberField
import Mathlib.RingTheory.Trace.Basic

/-!
# Integral squares in a weakly integral fusion basis

This independent arithmetic consequence uses only the derived FP dimension
character of the raw fusion rules. All embeddings of its dimension field
preserve the integral global dimension. Equality in the dimension bounds
then fixes the square of each simple dimension under every embedding.
The trace expresses this fixed square as a rational number, and algebraic
integrality makes it an integer. No positive categorical pivotal structure
is assumed by this argument.
-/

noncomputable section
open Classical
open scoped BigOperators
universe u w

namespace Paper18

/-- A complex number obtained from an algebraic number by the same value
under every embedding is rational, by the finite trace formula. -/
theorem exists_rat_of_embeddings_const
    {K : Type u} [Field K] [NumberField K] (a : K) (z : ℂ)
    (h : ∀ σ : K →ₐ[ℚ] ℂ, σ a = z) : ∃ q : ℚ, z = q := by
  letI : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  let n := Fintype.card (K →ₐ[ℚ] ℂ)
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  have ht : (Algebra.trace ℚ K a : ℂ) = (n : ℂ) * z := by
    change algebraMap ℚ ℂ (Algebra.trace ℚ K a) = _
    rw [trace_eq_sum_embeddings ℂ]
    simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rfl
  refine ⟨Algebra.trace ℚ K a / (n : ℚ), ?_⟩
  push_cast
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using ht.symm

namespace FusionBasis

variable {ι : Type w} [Fintype ι] (B : FusionBasis ι)

/-- The positive numerical FP character, constructed from the derived FP
dimensions. This is numerical data and asserts no categorical pivotal
identification. -/
def fpPivotalData : PivotalData B where
  jdim i := (B.fpdim i : ℂ)
  jdim_ne_zero i := Complex.ofReal_ne_zero.mpr (ne_of_gt (B.fpdim_pos i))
  jdim_one := by simp
  jdim_tensor i j := by exact_mod_cast (B.fpdim_mul i j).symm

@[simp] lemma fpPivotalData_jdim (i : ι) :
    B.fpPivotalData.jdim i = (B.fpdim i : ℂ) := rfl

@[simp] lemma fpPivotalData_globalDimension :
    B.fpPivotalData.globalDimension = (B.totalFPdim : ℂ) := by
  simp [PivotalData.globalDimension, PivotalData.ndim, totalFPdim, pow_two]

lemma fpPivotalData_fieldConjugate_spherical
    (σ : B.fpPivotalData.dimensionField →ₐ[ℚ] ℂ) :
    (B.fpPivotalData.fieldConjugate σ).Spherical := by
  apply (B.fpPivotalData.fieldConjugate σ).spherical_iff_jdim_dual.mpr
  intro i
  change σ (B.fpPivotalData.fieldDimension i) =
    σ (B.fpPivotalData.fieldDimension (B.dual i))
  congr 1
  apply Subtype.ext
  simp

/-- Every embedding preserves the total FP dimension when it is an
integer, so the embedded character attains equality in the FP bound. -/
lemma fpPivotalData_fieldConjugate_global_eq (hB : B.WeaklyIntegral)
    (σ : B.fpPivotalData.dimensionField →ₐ[ℚ] ℂ) :
    (B.fpPivotalData.fieldConjugate σ).globalDimension.re = B.totalFPdim := by
  obtain ⟨N, hN⟩ := hB
  have hD : B.fpPivotalData.fieldGlobalDimension =
      (N : B.fpPivotalData.dimensionField) := by
    apply Subtype.ext
    simp only [PivotalData.fieldGlobalDimension_coe, fpPivotalData_globalDimension]
    change (B.totalFPdim : ℂ) = (N : ℂ)
    exact_mod_cast hN
  rw [B.fpPivotalData.fieldConjugate_globalDimension, hD, map_intCast]
  simpa using hN.symm

/-- Every field embedding fixes the square of a simple FP dimension. -/
lemma fpPivotalData_fieldDimension_sq_embeddings (hB : B.WeaklyIntegral) (i : ι)
    (σ : B.fpPivotalData.dimensionField →ₐ[ℚ] ℂ) :
    σ (B.fpPivotalData.fieldDimension i ^ 2) = ((B.fpdim i ^ 2 : ℝ) : ℂ) := by
  let D := B.fpPivotalData.fieldConjugate σ
  have him : (D.jdim i).im = 0 := D.jdim_im_eq_zero
    (B.fpPivotalData_fieldConjugate_spherical σ) i
  have hn : ‖D.jdim i‖ = B.fpdim i := D.norm_jdim_eq_fpdim_of_global_eq
    (B.fpPivotalData_fieldConjugate_global_eq hB σ) i
  have hs : (D.jdim i).re ^ 2 = B.fpdim i ^ 2 := by
    have hh := congrArg (fun t : ℝ => t ^ 2) hn
    dsimp only at hh
    rw [Complex.sq_norm] at hh
    simpa [Complex.normSq_apply, him, pow_two] using hh
  rw [map_pow]
  change (D.jdim i) ^ 2 = _
  apply Complex.ext
  · simpa [pow_two, Complex.mul_re, him] using hs
  · simp [pow_two, Complex.mul_im, him]

/-- Weak integrality forces the square of each derived simple FP
dimension to be an integer; no categorification assumption is used. -/
theorem fpdim_sq_integer_of_weakIntegral (hB : B.WeaklyIntegral) (i : ι) :
    ∃ n : ℤ, B.fpdim i ^ 2 = n := by
  obtain ⟨q, hq⟩ := exists_rat_of_embeddings_const
    (B.fpPivotalData.fieldDimension i ^ 2) ((B.fpdim i ^ 2 : ℝ) : ℂ)
    (B.fpPivotalData_fieldDimension_sq_embeddings hB i)
  have hr : B.fpdim i ^ 2 = (q : ℝ) := by
    simpa [← Complex.ofReal_pow] using congrArg Complex.re hq
  exact real_rat_integral_eq_int ⟨q, hr⟩ ((B.fpdim_isIntegral i).pow 2)

end FusionBasis
end Paper18
