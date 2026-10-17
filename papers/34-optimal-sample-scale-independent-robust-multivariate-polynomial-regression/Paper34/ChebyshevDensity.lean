import Paper34.Model
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# One-dimensional Chebyshev density

The angular pushforward is identified with the actual Lebesgue density
`1 / (π * sqrt (1-x²))` on `[-1,1]`. The proof uses mathlib's general
change-of-variables theorem for the derivative of `arccos`, and then pushes
back by `cos`. Endpoints are removed only through Lebesgue null-set equalities.
-/

open Set MeasureTheory ContinuousLinearMap
open scoped ENNReal

namespace Paper34.ChebyshevDensity

noncomputable section

/-- The real one-dimensional angular law. -/
def realAngularLaw : Measure ℝ :=
  (ENNReal.ofReal Real.pi)⁻¹ • volume.restrict (Icc 0 Real.pi)

/-- The one-dimensional density displayed in source equation (1.1). -/
def density (x : ℝ) : ENNReal :=
  (Icc (-1 : ℝ) 1).indicator
    (fun y => ENNReal.ofReal (1 / (Real.pi * Real.sqrt (1 - y ^ 2)))) x

lemma arccos_image_Ioo : Real.arccos '' Ioo (-1 : ℝ) 1 = Ioo 0 Real.pi := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Real.arccos_pos.mpr hx.2, ?_⟩
    have h := Real.strictAntiOn_arccos (a := (-1 : ℝ)) (b := x)
      ⟨le_rfl, by norm_num⟩ ⟨hx.1.le, hx.2.le⟩ hx.1
    simpa using h
  · intro hy
    refine ⟨Real.cos y, ⟨?_, ?_⟩, Real.arccos_cos hy.1.le hy.2.le⟩
    · have h := Real.cos_lt_cos_of_nonneg_of_le_pi hy.1.le le_rfl hy.2
      simpa using h
    · have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (by norm_num) hy.2.le hy.1
      simpa using h

/-- One-variable specialization of the library's proved Jacobian theorem. -/
private lemma map_withDensity_abs_deriv_eq_volume {s : Set ℝ} {f f' : ℝ → ℝ}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) :
    Measure.map f ((volume.restrict s).withDensity (fun x => ENNReal.ofReal |f' x|)) =
      volume.restrict (f '' s) := by
  simpa only [det_one_smulRight] using
    map_withDensity_abs_det_fderiv_eq_addHaar volume hs.nullMeasurableSet
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf

lemma map_arccos_withDensity :
    Measure.map Real.arccos
      ((volume.restrict (Ioo (-1 : ℝ) 1)).withDensity
        (fun x => ENNReal.ofReal (1 / Real.sqrt (1 - x ^ 2)))) =
      volume.restrict (Ioo 0 Real.pi) := by
  have hd : ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivWithinAt Real.arccos (-(1 / Real.sqrt (1 - x ^ 2))) (Ioo (-1) 1) x := by
    intro x hx
    exact (Real.hasDerivAt_arccos hx.1.ne' hx.2.ne).hasDerivWithinAt
  have h := map_withDensity_abs_deriv_eq_volume measurableSet_Ioo hd
    (Real.arccos_injOn.mono Ioo_subset_Icc_self)
  have habs : (fun x : ℝ => ENNReal.ofReal |-(1 / Real.sqrt (1 - x ^ 2))|) =
      (fun x : ℝ => ENNReal.ofReal (1 / Real.sqrt (1 - x ^ 2))) := by
    funext x
    rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt (1 - x ^ 2))]
  simpa only [habs, arccos_image_Ioo] using h

lemma map_cos_restrict_Ioo :
    Measure.map Real.cos (volume.restrict (Ioo 0 Real.pi)) =
      (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity
        (fun x => ENNReal.ofReal (1 / Real.sqrt (1 - x ^ 2))) := by
  let mu := (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity
    (fun x => ENNReal.ofReal (1 / Real.sqrt (1 - x ^ 2)))
  have hmem : ∀ᵐ x ∂mu, x ∈ Ioo (-1 : ℝ) 1 :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)
  have hinv : Measure.map (Real.cos ∘ Real.arccos) mu = mu := by
    calc
      Measure.map (Real.cos ∘ Real.arccos) mu = Measure.map id mu := by
        apply Measure.map_congr
        filter_upwards [hmem] with x hx
        exact Real.cos_arccos hx.1.le hx.2.le
      _ = mu := Measure.map_id
  have h := congrArg (Measure.map Real.cos) map_arccos_withDensity
  rw [Measure.map_map Real.continuous_cos.measurable Real.continuous_arccos.measurable] at h
  change Measure.map (Real.cos ∘ Real.arccos) mu = _ at h
  rw [hinv] at h
  exact h.symm

/-- Unnormalized angular pushforward, with endpoints handled by null sets. -/
lemma map_cos_restrict_Icc :
    Measure.map Real.cos (volume.restrict (Icc 0 Real.pi)) =
      (volume.restrict (Icc (-1 : ℝ) 1)).withDensity
        (fun x => ENNReal.ofReal (1 / Real.sqrt (1 - x ^ 2))) := by
  simpa only [restrict_Ioo_eq_restrict_Icc] using map_cos_restrict_Ioo

/-- The normalized real angular pushforward has the actual source density. -/
theorem realAngularLaw_map_cos :
    Measure.map Real.cos realAngularLaw = volume.withDensity density := by
  rw [realAngularLaw, Measure.map_smul, map_cos_restrict_Icc]
  rw [← withDensity_smul' (ENNReal.ofReal Real.pi)⁻¹
    (fun x : ℝ => ENNReal.ofReal (1 / Real.sqrt (1 - x ^ 2))) (by simp [Real.pi_pos])]
  rw [show density = (Icc (-1 : ℝ) 1).indicator
      (fun x => ENNReal.ofReal (1 / (Real.pi * Real.sqrt (1 - x ^ 2)))) by rfl,
    withDensity_indicator measurableSet_Icc]
  congr 1
  funext x
  change (ENNReal.ofReal Real.pi)⁻¹ * ENNReal.ofReal (1 / Real.sqrt (1 - x ^ 2)) = _
  rw [← ENNReal.ofReal_inv_of_pos Real.pi_pos,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr Real.pi_pos.le)]
  congr 1
  simp [one_div, mul_inv_rev, mul_comm]


/-- Evaluation at the unique coordinate transports the actual model's angular
law for `n = 1` to the real one-dimensional angular law. -/
lemma model_angularLaw_one :
    Measure.map (fun theta : Point 1 => theta 0) (angularLaw 1) = realAngularLaw := by
  let e : Point 1 ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hvolume : Measure.map e (volume : Measure (Point 1)) = volume :=
    (volume_preserving_funUnique (Fin 1) ℝ).map_eq
  have hbox : Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ => Real.pi) =
      e ⁻¹' Icc (0 : ℝ) Real.pi := by
    ext theta
    change ((∀ k, 0 ≤ theta k) ∧ (∀ k, theta k ≤ Real.pi)) ↔
      0 ≤ theta 0 ∧ theta 0 ≤ Real.pi
    simp only [Fin.forall_fin_one]
  have hrestrict : Measure.map e
      (volume.restrict (Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ => Real.pi))) =
      volume.restrict (Icc (0 : ℝ) Real.pi) := by
    rw [hbox, ← e.restrict_map, hvolume]
  change Measure.map e (angularLaw 1) = realAngularLaw
  rw [angularLaw, pow_one, Measure.map_smul, hrestrict]
  rfl

/-- Source (1.1) for the actual one-dimensional model, transported from its
`Fin 1 → ℝ` representation to `ℝ` by evaluation at the unique coordinate. -/
theorem model_chebyshevLaw_one_density :
    Measure.map (fun x : Point 1 => x 0) (chebyshevLaw 1) = volume.withDensity density := by
  have hcos : Continuous (fun theta : Point 1 => fun k => Real.cos (theta k)) :=
    continuous_pi (fun k => Real.continuous_cos.comp (continuous_apply k))
  calc
    Measure.map (fun x : Point 1 => x 0) (chebyshevLaw 1) =
        Measure.map Real.cos (Measure.map (fun theta : Point 1 => theta 0) (angularLaw 1)) := by
      rw [chebyshevLaw,
        Measure.map_map (measurable_pi_apply 0) hcos.measurable,
        Measure.map_map Real.continuous_cos.measurable (measurable_pi_apply 0)]
      rfl
    _ = volume.withDensity density := by
      rw [model_angularLaw_one, realAngularLaw_map_cos]

end

end Paper34.ChebyshevDensity
