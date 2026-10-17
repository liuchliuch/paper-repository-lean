import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc

/-!
# Logarithmic variation along a nonvanishing complex path

The path parameter is real. The logarithm is constructed by integrating its
logarithmic derivative, without choosing a branch of the complex logarithm.
-/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace Paper08.ComplexPathLog

/-- A nonzero continuously differentiable complex path whose logarithmic
derivative has norm at most `a` changes by `exp w` with `‖w‖ ≤ a`.
Only continuity of the derivative on the closed parameter interval is needed. -/
theorem path_log_change {P D : ℝ → ℂ} {a : ℝ}
    (hD : ContinuousOn D (Icc 0 1))
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt P (D t) t)
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, P t ≠ 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖D t / P t‖ ≤ a) :
    ∃ w : ℂ, P 1 = P 0 * Complex.exp w ∧ ‖w‖ ≤ a := by
  have hPc : ContinuousOn P (Icc (0 : ℝ) 1) := fun t ht =>
    (hP t ht).continuousAt.continuousWithinAt
  have hquot : ContinuousOn (fun t => D t/P t) (Icc (0 : ℝ) 1) := hD.div hPc hne
  let c : ℝ → ℝ := fun t => (projIcc 0 1 (by norm_num) t : ℝ)
  let g : ℝ → ℂ := fun t => D (c t)/P (c t)
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hg : Continuous g := hquot.comp_continuous hc (fun t => (projIcc 0 1 (by norm_num) t).property)
  have hgeq : ∀ t ∈ Icc (0 : ℝ) 1, g t = D t/P t := by
    intro t ht
    simp only [g,c,projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) ht]
  let H : ℝ → ℂ := fun t => ∫ v in (0 : ℝ)..t, g v
  have hH : ∀ t : ℝ, HasDerivAt H (g t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hH0 : H 0 = 0 := by simp [H]
  let F : ℝ → ℂ := fun t => P t * Complex.exp (-H t)
  have hF : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F 0 t := by
    intro t ht
    convert (hP t ht).mul ((hH t).neg.cexp) using 1
    rw [hgeq t ht]
    field_simp [hne t ht]
    <;> ring
  have hconst : F 1 = F 0 := by
    have hnorm : ‖F 1-F 0‖ ≤ 0 := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t ht => (hF t ht).hasDerivWithinAt)
      (fun _ _ => by simp)
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hnorm)
  have hident : P 1 * Complex.exp (-H 1) = P 0 := by
    simpa only [F,hH0,neg_zero,Complex.exp_zero,mul_one] using hconst
  refine ⟨H 1,?_,?_⟩
  · calc
      P 1 = (P 1 * Complex.exp (-H 1))*Complex.exp (H 1) := by
        rw [mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,mul_one]
      _ = P 0 * Complex.exp (H 1) := by rw [hident]
  · have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (f := g) (C := a) (fun t ht => by
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
          exact ⟨ht.1.le,ht.2⟩
        rw [hgeq t ht']
        exact hbound t ht')
    simpa only [H,sub_zero,abs_one,mul_one] using hnorm

end Paper08.ComplexPathLog
