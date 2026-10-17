import PsgEst.TraceExponential
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Finite-interval representation and operator concavity of the matrix logarithm

The logarithm is the actual `CFC.log`. Quadratic-form integrals are real
interval integrals on `[0,1]`; no improper or matrix-valued integral is needed.
-/

open Matrix BigOperators Real Finset Classical MeasureTheory Set
open scoped Matrix.Norms.L2Operator

namespace PsgEst

section LogBasics

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-- The actual continuous-functional-calculus logarithm in an orthogonal spectral basis. -/
theorem matrixLog_eq_spectralMap (hA : A.IsHermitian) :
    CFC.log A = spectralMap hA Real.log := by
  rw [CFC.log, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, spectralMap, Function.comp_def,
    RCLike.ofReal_real_eq_id, id_eq]

/-- The actual logarithm of a real self-adjoint matrix is self-adjoint. -/
theorem matrixLog_isHermitian (hA : A.IsHermitian) : (CFC.log A).IsHermitian := by
  rw [matrixLog_eq_spectralMap hA]
  exact spectralMap_isHermitian hA Real.log

end LogBasics

/-- A continuous finite-interval scalar logarithm kernel, including its value at zero. -/
noncomputable def logUnitKernel (s x : ℝ) : ℝ := (x - 1) / (1 + s * (x - 1))

lemma logUnitKernel_den_pos {x s : ℝ} (hx : 0 < x) (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < 1 + s * (x - 1) := by
  by_cases hs1 : s = 1
  · rw [hs1]
    linarith
  · have hslt : s < 1 := lt_of_le_of_ne hs.2 hs1
    have hsx := mul_nonneg hs.1 hx.le
    nlinarith

lemma logUnitKernel_continuousOn {x : ℝ} (hx : 0 < x) :
    ContinuousOn (fun s => logUnitKernel s x) (Icc (0 : ℝ) 1) := by
  unfold logUnitKernel
  exact continuousOn_const.div
    (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
    (fun s hs => ne_of_gt (logUnitKernel_den_pos hx hs))

lemma logUnitKernel_intervalIntegrable {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun s => logUnitKernel s x) volume 0 1 :=
  (logUnitKernel_continuousOn hx).intervalIntegrable_of_Icc (by norm_num)

/-- Scalar logarithm as a proper integral over the compact unit interval. -/
theorem real_log_unit_integral {x : ℝ} (hx : 0 < x) :
    Real.log x = ∫ s in (0 : ℝ)..1, logUnitKernel s x := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => Real.log (1 + t * (x - 1))) (logUnitKernel s x) s := by
    simpa only [logUnitKernel, zero_add, one_mul] using
      ((hasDerivAt_const s (1 : ℝ)).add ((hasDerivAt_id s).mul_const (x - 1))).log
        (ne_of_gt (logUnitKernel_den_pos hx hs))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs))
    (logUnitKernel_intervalIntegrable hx)
  have hone : 1 + (x - 1) = x := by ring
  simpa only [zero_mul, add_zero, Real.log_one, sub_zero, one_mul, hone] using hi.symm

/-- The inverse-resolvent version of the scalar kernel, away from the removable endpoint. -/
lemma neg_logUnitKernel_eq_resolvent {x s : ℝ} (hx : 0 < x)
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    -logUnitKernel s x = ((1 + s * (x - 1))⁻¹ - 1) / s := by
  have hd := logUnitKernel_den_pos hx ⟨hs.1.le, hs.2⟩
  unfold logUnitKernel
  generalize hy : 1 + s * (x - 1) = y at *
  field_simp [ne_of_gt hs.1, ne_of_gt hd]
  nlinarith only [hy]

/-- Negative logarithm as the proper resolvent integral; the value assigned at
`s=0` is immaterial because interval integrals use `(0,1]`. -/
theorem real_neg_log_unit_resolvent_integral {x : ℝ} (hx : 0 < x) :
    -Real.log x = ∫ s in (0 : ℝ)..1, ((1 + s * (x - 1))⁻¹ - 1) / s := by
  rw [real_log_unit_integral hx, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr_ae
  exact Filter.Eventually.of_forall (fun s hs => neg_logUnitKernel_eq_resolvent hx
    (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs))

/-- The scalar relative-entropy integrand has a continuous extension at zero. -/
lemma relative_entropy_unit_kernel_eq {x a s : ℝ} (hx : 0 < x) (ha : 0 < a)
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    -x * logUnitKernel s (a / x) =
      (x ^ 2 / ((1 - s) * x + s * a) - x) / s := by
  have hr := logUnitKernel_den_pos (div_pos ha hx) ⟨hs.1.le, hs.2⟩
  have hden : 0 < (1 - s) * x + s * a := by
    by_cases hs1 : s = 1
    · simpa only [hs1, sub_self, zero_mul, one_mul, zero_add] using ha
    · have hslt : s < 1 := lt_of_le_of_ne hs.2 hs1
      exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hx) (mul_nonneg hs.1.le ha.le)
  have hratio : 1 + s * (a / x - 1) = ((1 - s) * x + s * a) / x := by
    field_simp [ne_of_gt hx]
    ring
  unfold logUnitKernel
  rw [hratio]
  generalize hy : (1 - s) * x + s * a = y at *
  field_simp [ne_of_gt hx, ne_of_gt hs.1, ne_of_gt hden]
  nlinarith only [hy]

/-- Integrability of the actual scalar resolvent expression used in the
joint-convexity representation of relative entropy. -/
theorem relative_entropy_unit_intervalIntegrable {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    IntervalIntegrable (fun s => (x ^ 2 / ((1 - s) * x + s * a) - x) / s) volume 0 1 := by
  apply ((logUnitKernel_intervalIntegrable (div_pos ha hx)).const_mul (-x)).congr
  intro s hs
  apply relative_entropy_unit_kernel_eq hx ha
  simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs

/-- Relative entropy of two positive scalar weights in the exact resolvent form
needed for the Hilbert--Schmidt joint-convexity argument. -/
theorem real_relative_entropy_unit_integral {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    x * (Real.log x - Real.log a) =
      ∫ s in (0 : ℝ)..1, (x ^ 2 / ((1 - s) * x + s * a) - x) / s := by
  have hlog := real_log_unit_integral (div_pos ha hx)
  have hscalar : x * (Real.log x - Real.log a) = -x * Real.log (a / x) := by
    rw [Real.log_div (ne_of_gt ha) (ne_of_gt hx)]
    ring
  rw [hscalar, hlog, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  exact Filter.Eventually.of_forall (fun s hs => relative_entropy_unit_kernel_eq hx ha
    (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs))

end PsgEst
