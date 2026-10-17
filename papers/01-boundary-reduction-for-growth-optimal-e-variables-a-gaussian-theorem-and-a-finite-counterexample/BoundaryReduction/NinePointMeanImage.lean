import BoundaryReduction.NinePointCoordinates
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp

open Real Set BigOperators Filter
open scoped Classical
namespace BoundaryReduction.NinePoint

abbrev MeanSpace := EuclideanSpace ℝ (Fin 2)

def fromES (x : MeanSpace) : ℝ × ℝ := (x 0,x 1)

lemma toES_fromES (x : MeanSpace) : toES (fromES x) = x := by
  ext i
  fin_cases i <;> simp [toES,fromES]

lemma fromES_toES (θ : ℝ × ℝ) : fromES (toES θ) = θ := by simp [fromES,toES]

lemma continuous_fromES : Continuous fromES :=
  (EuclideanSpace.proj 0).continuous.prodMk (EuclideanSpace.proj 1).continuous

noncomputable def logPartition (x : MeanSpace) : ℝ := log (Z (fromES x))

lemma exponent_fromES (x : MeanSpace) (y : Fin 9) : dot (fromES x) (coord y) = inner ℝ (esTarget y) x := by
  rw [← inner_toES,toES_fromES,real_inner_comm]
  rfl

lemma hasFDerivAt_logPartition (x : MeanSpace) :
    HasFDerivAt logPartition (innerSL ℝ (esMean (pt (fromES x)))) x := by
  have hs : HasFDerivAt (fun z : MeanSpace => ∑ y : Fin 9, exp (inner ℝ (esTarget y) z)*p0 y)
      (∑ y : Fin 9, (exp (inner ℝ (esTarget y) x)*p0 y) • innerSL ℝ (esTarget y)) x := by
    convert HasFDerivAt.sum (u := Finset.univ) (fun y _ =>
      (((innerSL ℝ (esTarget y)).hasFDerivAt).exp.mul_const (p0 y))) using 1 <;>
      simp [smul_smul,mul_comm]
  have heq (z : MeanSpace) : (∑ y : Fin 9, exp (inner ℝ (esTarget y) z)*p0 y) = Z (fromES z) := by
    simp only [Z,un,exponent_fromES]
  simp_rw [heq] at hs
  have hl := hs.log (Z_pos (fromES x)).ne'
  convert hl using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,smul_eq_mul,innerSL_apply,
    logPartition,esMean,sum_inner,real_inner_smul_left,pt,un,esTarget,exponent_fromES]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma continuous_logPartition : Continuous logPartition :=
  continuous_iff_continuousAt.mpr (fun x => (hasFDerivAt_logPartition x).continuousAt)

/-- The closed excluded ball is contained in the actual mean image. This is
proved directly by minimizing the log-partition potential on a larger ball. -/
theorem closedBall_subset_mean_range : Metric.closedBall (0 : MeanSpace) r₀ ⊆
    Set.range (fun θ : ℝ × ℝ => esMean (pt θ)) := by
  intro μ hμ
  have hμnorm : ‖μ‖ ≤ r₀ := by simpa only [Metric.mem_closedBall,dist_zero_right] using hμ
  let f : MeanSpace → ℝ := fun x => logPartition x-inner ℝ μ x
  have hf : Continuous f := continuous_logPartition.sub (innerSL ℝ μ).continuous
  have hball : (Metric.closedBall (0 : MeanSpace) (1/10:ℝ)).Nonempty :=
    ⟨0,by simp⟩
  obtain ⟨x,hx,hmin⟩ := (isCompact_closedBall (0 : MeanSpace) (1/10:ℝ)).exists_isMinOn hball hf.continuousOn
  have hxnorm : ‖x‖ ≤ 1/10 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  have hd : HasFDerivAt f (innerSL ℝ (esMean (pt (fromES x))-μ)) x := by
    convert (hasFDerivAt_logPartition x).sub (innerSL ℝ μ).hasFDerivAt using 1
    ext v
    simp [inner_sub_left]
  have hinner : inner ℝ x (esMean (pt (fromES x))-μ) ≤ 0 := by
    have ht : -x ∈ posTangentConeAt (Metric.closedBall (0 : MeanSpace) (1/10:ℝ)) x := by
      have hsegment : segment ℝ x (0 : MeanSpace) ⊆ Metric.closedBall 0 (1/10:ℝ) :=
        (convex_closedBall (0 : MeanSpace) (1/10:ℝ)).segment_subset hx (by simp)
      have hh := sub_mem_posTangentConeAt_of_segment_subset hsegment
      simpa using hh
    have hlocalon : IsLocalMinOn f (Metric.closedBall (0 : MeanSpace) (1/10:ℝ)) x :=
      hmin.localize
    have hn := hlocalon.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt ht
    simpa only [innerSL_apply,inner_neg_right,real_inner_comm,neg_nonneg] using hn
  have hxsmall : ‖x‖ < 1/10 := by
    by_contra hn
    have heq : ‖x‖ = 1/10 := le_antisymm hxnorm (le_of_not_gt hn)
    have hsq : ‖toES (fromES x)‖^2 ≤ 1/100 := by rw [toES_fromES,heq]; norm_num
    have hl := rayMean_local_lower hsq
    rw [rayMean_inner,one_smul,toES_fromES] at hl
    have hu := (real_inner_le_norm x μ).trans (mul_le_mul_of_nonneg_left hμnorm (norm_nonneg x))
    rw [inner_sub_right] at hinner
    rw [heq] at hl
    rw [heq,r₀_eq] at hu
    norm_num at hl hu
    linarith
  have hlocal : IsLocalMin f x := hmin.isLocalMin (Filter.mem_of_superset
    (Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball (0 : MeanSpace) (1/10:ℝ) by
      simpa only [Metric.mem_ball,dist_zero_right] using hxsmall)) Metric.ball_subset_closedBall)
  have hz := hlocal.hasFDerivAt_eq_zero hd
  have heq : esMean (pt (fromES x)) = μ := by
    have hh := congrArg (fun L : MeanSpace →L[ℝ] ℝ => L (esMean (pt (fromES x))-μ)) hz
    simp only [innerSL_apply,ContinuousLinearMap.zero_apply,inner_self_eq_norm_sq_to_K] at hh
    have hhreal : ‖esMean (pt (fromES x))-μ‖^2 = 0 := by exact_mod_cast hh
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hhreal))
  exact ⟨fromES x,heq⟩

end BoundaryReduction.NinePoint
