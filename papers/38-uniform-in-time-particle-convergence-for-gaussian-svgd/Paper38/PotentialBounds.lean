import Paper38.Model
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Bounds derived from the source's exact C² and quadratic-form hypotheses. -/
noncomputable section

open Real Set

namespace Paper38.PotentialBounds
open Paper38.Model

variable {d : ℕ} {V : E d → ℝ} {α β : ℝ}

lemma hessian_symmetric (hV : AdmissiblePotential V α β) (x u v : E d) :
    (fderiv ℝ (fderiv ℝ V) x u) v = (fderiv ℝ (fderiv ℝ V) x v) u := by
  exact hV.regularity.contDiffAt.isSymmSndFDerivAt (by simp) u v

lemma hessian_cross_abs_bound (hV : AdmissiblePotential V α β) (x u v : E d) :
    |(fderiv ℝ (fderiv ℝ V) x u) v| ≤ β * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  let B := fderiv ℝ (fderiv ℝ V) x
  have hsym : B v u = B u v := hessian_symmetric hV x v u
  have hp0 : 0 ≤ B (u + v) (u + v) :=
    (mul_nonneg hV.alpha_pos.le (sq_nonneg _)).trans (hV.hessian_lower x (u + v))
  have hm0 : 0 ≤ B (u - v) (u - v) :=
    (mul_nonneg hV.alpha_pos.le (sq_nonneg _)).trans (hV.hessian_lower x (u - v))
  have hp := hV.hessian_upper x (u + v)
  have hm := hV.hessian_upper x (u - v)
  have hpol : B (u + v) (u + v) - B (u - v) (u - v) = 4 * B u v := by
    simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, hsym]
    ring
  have hpar := congrArg (fun t : ℝ => β * t) (parallelogram_law_with_norm ℝ u v)
  have hβ : 0 ≤ β := hV.alpha_pos.le.trans hV.alpha_le_beta
  have hnn : 0 ≤ β * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by positivity
  change |B u v| ≤ β * (‖u‖ ^ 2 + ‖v‖ ^ 2)
  change B (u + v) (u + v) ≤ _ at hp
  change B (u - v) (u - v) ≤ _ at hm
  apply abs_le.mpr
  constructor <;> nlinarith

/-- A uniform operator-norm bound is derived, rather than assumed.
The factor 2 is harmless for the dominated differentiation argument. -/
lemma hessian_opNorm_bound (hV : AdmissiblePotential V α β) (x : E d) :
    ‖fderiv ℝ (fderiv ℝ V) x‖ ≤ 2 * β := by
  have hβ : 0 ≤ β := hV.alpha_pos.le.trans hV.alpha_le_beta
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro u hu
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have hb := hessian_cross_abs_bound hV x u v
  simp only [hu, hv, one_pow] at hb
  change |(fderiv ℝ (fderiv ℝ V) x u) v| ≤ 2 * β
  linarith

lemma fderiv_lipschitz_bound (hV : AdmissiblePotential V α β) (x y : E d) :
    ‖fderiv ℝ V y - fderiv ℝ V x‖ ≤ (2 * β) * ‖y - x‖ := by
  have hd : ContDiff ℝ 1 (fderiv ℝ V) := hV.regularity.fderiv_right (by norm_num)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hd.differentiable (by norm_num) z)
    (fun z _ => hessian_opNorm_bound hV z) convex_univ (mem_univ x) (mem_univ y)

/-- The first growth estimate in the proof of Lemma 4.2. -/
lemma fderiv_linear_growth (hV : AdmissiblePotential V α β) (x : E d) :
    ‖fderiv ℝ V x‖ ≤ ‖fderiv ℝ V 0‖ + (2 * β) * ‖x‖ := by
  have h := fderiv_lipschitz_bound hV 0 x
  simp only [sub_zero] at h
  calc
    ‖fderiv ℝ V x‖ ≤ ‖fderiv ℝ V x - fderiv ℝ V 0‖ + ‖fderiv ℝ V 0‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ _ := by linarith

/-- A concrete quadratic envelope for the potential, derived by the mean value theorem. -/
lemma potential_quadratic_growth (hV : AdmissiblePotential V α β) (x : E d) :
    |V x| ≤ (|V 0| + ‖fderiv ℝ V 0‖ + 2 * β) * (1 + ‖x‖ ^ 2) := by
  have hβ : 0 ≤ β := hV.alpha_pos.le.trans hV.alpha_le_beta
  have hdiff : ‖V x - V 0‖ ≤ (‖fderiv ℝ V 0‖ + 2 * β * ‖x‖) * ‖x‖ := by
    have hm := Convex.norm_image_sub_le_of_norm_fderiv_le
      (s := Metric.closedBall (0 : E d) ‖x‖) (x := (0 : E d)) (y := x)
      (C := ‖fderiv ℝ V 0‖ + 2 * β * ‖x‖)
      (fun z _ => hV.regularity.differentiable (by norm_num) z)
      (fun z hz => (fderiv_linear_growth hV z).trans (by
        have hz' : ‖z‖ ≤ ‖x‖ := by simpa using hz
        nlinarith))
      (convex_closedBall (0 : E d) ‖x‖) (by simp) (by simp)
    simpa using hm
  have hn : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
  have hn' := mul_le_mul_of_nonneg_left hn (norm_nonneg (fderiv ℝ V 0))
  have hnn : 0 ≤ (|V 0| + 2 * β) * ‖x‖ ^ 2 := by positivity
  have hval := norm_le_norm_sub_add (V x) (V 0)
  simp only [Real.norm_eq_abs] at hdiff hval
  nlinarith [abs_nonneg (V 0)]

end Paper38.PotentialBounds
