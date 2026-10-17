import Paper14.FractionalSlice
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory Function Set Filter
open scoped ENNReal
namespace Paper14
noncomputable section

/-- Exact slicing formula for the actual (c,theta) coordinates, before
inverting the first coordinate. -/
theorem lintegral_farey_coordinates_slices (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F (cOf x,thetaOf x) ∂m) =
      2 * ∫⁻ a in Ioc (0 : ℝ) 1, ENNReal.ofReal a * ∫⁻ θ in Ioc (0 : ℝ) 1, F (a⁻¹,θ) := by
  have hcoord : Measurable (fun x : ℝ × ℝ => (cOf x,thetaOf x)) := by
    unfold cOf thetaOf
    fun_prop
  have hmeas : Measurable (Omega.indicator (fun x => F (cOf x,thetaOf x))) :=
    (hF.comp hcoord).indicator measurableSet_Omega
  rw [m,lintegral_smul_measure,← lintegral_indicator measurableSet_Omega]
  change 2*(∫⁻ x : ℝ × ℝ, Omega.indicator (fun x => F (cOf x,thetaOf x)) x ∂volume.prod volume) = _
  rw [lintegral_prod _ hmeas.aemeasurable]
  have hs : (fun a : ℝ => ∫⁻ b : ℝ, Omega.indicator (fun x => F (cOf x,thetaOf x)) (a,b)) =
      (Ioc (0 : ℝ) 1).indicator (fun a => ENNReal.ofReal a * ∫⁻ θ in Ioc (0 : ℝ) 1, F (a⁻¹,θ)) := by
    funext a
    by_cases ha : a ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem ha]
      have heq : (fun b : ℝ => Omega.indicator (fun x => F (cOf x,thetaOf x)) (a,b)) =
          (Ioc (1-a) 1).indicator (fun b => F (a⁻¹,Int.fract (b/a))) := by
        funext b
        have hmem : (a,b) ∈ Omega ↔ b ∈ Ioc (1-a) 1 := by
          rw [mem_Omega_iff]
          exact ⟨fun h => ⟨h.2.2.1,h.2.2.2⟩,fun h => ⟨ha.1,ha.2,h.1,h.2⟩⟩
        by_cases hb : b ∈ Ioc (1-a) 1
        · rw [indicator_of_mem (hmem.mpr hb),indicator_of_mem hb]
          rfl
        · rw [indicator_of_notMem (fun hx => hb (hmem.mp hx)),indicator_of_notMem hb]
      rw [heq,lintegral_indicator measurableSet_Ioc]
      exact lintegral_farey_fractional_slice (fun θ => F (a⁻¹,θ)) ha.1
    · rw [indicator_of_notMem ha]
      have heq : (fun b : ℝ => Omega.indicator (fun x => F (cOf x,thetaOf x)) (a,b)) = (fun _ => (0 : ℝ≥0∞)) := by
        funext b
        have hx : (a,b) ∉ Omega := fun hx => ha ⟨hx.1,hx.2.1⟩
        simp only [indicator_of_notMem hx]
      rw [heq,lintegral_zero]
  rw [hs,lintegral_indicator measurableSet_Ioc]

lemma inv_image_Ici_one : (fun c : ℝ => c⁻¹) '' Ici (1 : ℝ) = Ioc (0 : ℝ) 1 := by
  ext a
  constructor
  · rintro ⟨c,hc,rfl⟩
    have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
    exact ⟨inv_pos.mpr hc0,(inv_le_one₀ hc0).mpr hc⟩
  · intro ha
    refine ⟨a⁻¹,(one_le_inv₀ ha.1).mpr ha.2,inv_inv a⟩

/-- The inversion Jacobian gives the exact c^{-3} density. -/
theorem lintegral_invert_weighted (H : ℝ → ℝ≥0∞) :
    (∫⁻ a in Ioc (0 : ℝ) 1, ENNReal.ofReal a * H a⁻¹) =
      ∫⁻ c in Ici (1 : ℝ), ENNReal.ofReal (c⁻¹^3)*H c := by
  have hd (c : ℝ) (hc : c ∈ Ici (1 : ℝ)) :
      HasDerivWithinAt (fun c : ℝ => c⁻¹) (-(c^2)⁻¹) (Ici (1 : ℝ)) c := by
    exact (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le zero_lt_one hc))).hasDerivWithinAt
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ici hd
    (fun c hc d hd h => inv_injective h) (fun a => ENNReal.ofReal a * H a⁻¹)
  rw [inv_image_Ici_one] at hj
  rw [hj]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with c hc
  simp only [inv_inv]
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  rw [abs_neg,abs_of_pos (inv_pos.mpr (sq_pos_of_pos hc0)),← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg c))]
  have heq : (c^2)⁻¹*c⁻¹ = c⁻¹^3 := by field_simp
  rw [heq]

/-- Full original coordinate density (13), as an exact nonnegative
integral identity on the original normalized BCZ section. -/
theorem lintegral_farey_coordinates (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F (cOf x,thetaOf x) ∂m) =
      ∫⁻ c in Ici (1 : ℝ), ENNReal.ofReal (2*c⁻¹^3)* ∫⁻ θ in Ioc (0 : ℝ) 1, F (c,θ) := by
  rw [lintegral_farey_coordinates_slices F hF,
    lintegral_invert_weighted (fun c => ∫⁻ θ in Ioc (0 : ℝ) 1, F (c,θ))]
  rw [← lintegral_const_mul' 2 _ (by norm_num)]
  apply lintegral_congr
  intro c
  simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat,mul_assoc]

end
end Paper14
