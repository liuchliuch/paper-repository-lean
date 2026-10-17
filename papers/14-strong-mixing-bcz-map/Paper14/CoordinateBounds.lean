import Paper14.FareyCoordinates
import Paper14.SelfInductionConvergence
import Paper14.BoundedProductLimits

open MeasureTheory Set Function Filter
open scoped ENNReal
namespace Paper14
noncomputable section

lemma farey_density_mass :
    (∫⁻ c in Ici (1 : ℝ), ENNReal.ofReal (2*c⁻¹^3)) = 1 := by
  have hh := lintegral_farey_coordinates (fun _ => (1 : ℝ≥0∞)) measurable_const
  simpa only [lintegral_one,measure_univ,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero,ENNReal.ofReal_one,mul_one] using hh.symm

/-- A uniform conditional theta expectation bound integrates with no
extra density factor under the actual BCZ probability measure. -/
theorem integral_farey_of_uniform_conditional_bound (f : ℝ × ℝ → ℝ)
    (hf : Measurable f) (h0 : ∀ z, 0 ≤ f z) (B : ℝ) (hB : ∀ z, ‖f z‖ ≤ B)
    {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ c : ℝ, 1 ≤ c → (∫ θ in Ioc (0 : ℝ) 1, f (c,θ)) ≤ C) :
    (∫ x, f (cOf x,thetaOf x) ∂m) ≤ C := by
  have hcoord : Measurable (fun x : ℝ × ℝ => (cOf x,thetaOf x)) := by
    unfold cOf thetaOf
    fun_prop
  have hfi : Integrable (fun x => f (cOf x,thetaOf x)) m :=
    integrable_of_measurable_bound (hf.comp hcoord) B (fun x => hB _)
  have hi (c : ℝ) : IntegrableOn (fun θ => f (c,θ)) (Ioc (0 : ℝ) 1) := by
    letI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
    exact integrable_of_measurable_bound (hf.comp (measurable_const.prodMk measurable_id)) B (fun θ => hB _)
  have hl := lintegral_farey_coordinates (fun z => ENNReal.ofReal (f z))
    (ENNReal.continuous_ofReal.measurable.comp hf)
  have hleft := ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall (fun x => h0 _))
  have hENN : ENNReal.ofReal (∫ x, f (cOf x,thetaOf x) ∂m) ≤ ENNReal.ofReal C := by
    rw [hleft,hl]
    calc
      _ ≤ ∫⁻ c in Ici (1 : ℝ), ENNReal.ofReal (2*c⁻¹^3)*ENNReal.ofReal C := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ici] with c hc
        apply mul_le_mul_left'
        rw [← ofReal_integral_eq_lintegral_ofReal (hi c) (Eventually.of_forall (fun θ => h0 _))]
        exact ENNReal.ofReal_le_ofReal (hmean c hc)
      _ = ENNReal.ofReal C := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,farey_density_mass,one_mul]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun x => h0 _)),ENNReal.toReal_ofReal hC] using hh

end
end Paper14
