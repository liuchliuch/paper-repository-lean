import Paper38.PotentialBounds
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Coercive lower bounds derived from the actual source Hessian hypothesis. -/
noncomputable section

open Real Set

namespace Paper38.PotentialLowerBound
open Paper38.Model

variable {d : ℕ} {V : E d → ℝ} {α β : ℝ}

def lineGradient (V : E d → ℝ) (x h : E d) (t : ℝ) : ℝ :=
  (fderiv ℝ V (x + t • h)) h

lemma lineGradient_hasDerivAt (hV : AdmissiblePotential V α β) (x h : E d) (t : ℝ) :
    HasDerivAt (lineGradient V x h)
      ((fderiv ℝ (fderiv ℝ V) (x + t • h) h) h) t := by
  have h₁ : ContDiff ℝ 1 (fderiv ℝ V) := hV.regularity.fderiv_right (by norm_num)
  have hp : HasDerivAt (fun t : ℝ => x + t • h) h t := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const h).const_add x
  have hd := (h₁.differentiable (by norm_num) (x + t • h)).hasFDerivAt.comp_hasDerivAt t hp
  simpa [lineGradient] using hd.clm_apply (hasDerivAt_const t h)

lemma lineGradient_lower (hV : AdmissiblePotential V α β) (x h : E d) {t : ℝ} (ht : 0 ≤ t) :
    lineGradient V x h 0 + α * ‖h‖ ^ 2 * t ≤ lineGradient V x h t := by
  have hf : Differentiable ℝ (lineGradient V x h) := fun s => (lineGradient_hasDerivAt hV x h s).differentiableAt
  have hb : ∀ s, α * ‖h‖ ^ 2 ≤ deriv (lineGradient V x h) s := by
    intro s
    rw [(lineGradient_hasDerivAt hV x h s).deriv]
    exact hV.hessian_lower (x + s • h) h
  have hm := mul_sub_le_image_sub_of_le_deriv hf hb ht
  simpa only [sub_zero] using (show lineGradient V x h 0 + α * ‖h‖ ^ 2 * (t - 0) ≤ lineGradient V x h t by linarith)

lemma taylor_lower (hV : AdmissiblePotential V α β) (x y : E d) :
    V x + (fderiv ℝ V x) (y - x) + (α / 2) * ‖y - x‖ ^ 2 ≤ V y := by
  let h := y - x
  let C := α * ‖h‖ ^ 2
  let g₀ := lineGradient V x h 0
  let f : ℝ → ℝ := fun t => V (x + t • h) - t * g₀ - C * t ^ 2 / 2
  have hd (t : ℝ) : HasDerivAt f (lineGradient V x h t - g₀ - C * t) t := by
    have hp : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const h).const_add x
    have hv := (hV.regularity.differentiable (by norm_num) (x + t • h)).hasFDerivAt.comp_hasDerivAt t hp
    convert ((hv.sub ((hasDerivAt_id t).mul_const g₀)).sub
      ((((hasDerivAt_id t).pow 2).const_mul C).div_const 2)) using 1 <;>
      simp [f, lineGradient] <;> ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t).deriv]
      have hb := lineGradient_lower hV x h (show 0 ≤ t from interior_subset ht)
      dsimp [g₀, C]
      linarith
  have h01 := hm (show (0 : ℝ) ∈ Ici 0 by simp) (show (1 : ℝ) ∈ Ici 0 by norm_num) (by norm_num)
  dsimp [f, g₀, C, h, lineGradient] at h01
  simp only [zero_smul, add_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_div,
    sub_zero, one_smul, add_sub_cancel, one_mul, one_pow] at h01
  nlinarith

/-- A global quadratic lower envelope, with a concrete finite source-dependent constant. -/
lemma potential_quadratic_lower (hV : AdmissiblePotential V α β) (x : E d) :
    V 0 - ‖fderiv ℝ V 0‖ ^ 2 / α + (α / 4) * ‖x‖ ^ 2 ≤ V x := by
  have h := taylor_lower hV 0 x
  simp only [sub_zero] at h
  have hlin : -‖fderiv ℝ V 0‖ * ‖x‖ ≤ (fderiv ℝ V 0) x := by
    have habs := (fderiv ℝ V 0).le_opNorm x
    simp only [Real.norm_eq_abs] at habs
    simpa only [neg_mul] using (abs_le.mp habs).1
  have hscaled := mul_le_mul_of_nonneg_left h hV.alpha_pos.le
  have hlinα := mul_le_mul_of_nonneg_left hlin hV.alpha_pos.le
  have hquot : α * (‖fderiv ℝ V 0‖ ^ 2 / α) = ‖fderiv ℝ V 0‖ ^ 2 := by
    field_simp [hV.alpha_pos.ne']
  apply (mul_le_mul_left hV.alpha_pos).mp
  simp only [mul_add, mul_sub, hquot]
  nlinarith [sq_nonneg (α * ‖x‖ - 2 * ‖fderiv ℝ V 0‖)]

/-- The uniform lower constant needed for the covariance-determinant barrier. -/
lemma potential_global_lower (hV : AdmissiblePotential V α β) (x : E d) :
    V 0 - ‖fderiv ℝ V 0‖ ^ 2 / α ≤ V x := by
  exact (le_add_of_nonneg_right (mul_nonneg (div_nonneg hV.alpha_pos.le (by norm_num)) (sq_nonneg _))).trans
    (potential_quadratic_lower hV x)

end Paper38.PotentialLowerBound
