import Paper14.MeasureOmega
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.JacobianOneDim

open MeasureTheory Function Set Filter
open scoped ENNReal
namespace Paper14
noncomputable section

/-- The distribution of a real fractional coordinate is uniform on every
unit interval, without a regularity premise on its nonnegative test. -/
lemma lintegral_fract_period (F : ℝ → ℝ≥0∞) (t : ℝ) :
    (∫⁻ u in Ioc t (t+1), F (Int.fract u)) = ∫⁻ u in Ioc (0 : ℝ) 1, F u := by
  let f : ℝ → ℝ≥0∞ := fun u => F (Int.fract u)
  have hp : Periodic f 1 := fun u => congrArg F (Int.fract_add_one u)
  let g : UnitAddCircle → ℝ≥0∞ := hp.lift
  have ht := AddCircle.lintegral_preimage 1 t g
  have h0 := AddCircle.lintegral_preimage 1 0 g
  simp only [zero_add] at h0
  have heq : (∫⁻ u in Ioc t (t+1), f u) = ∫⁻ u in Ioc (0 : ℝ) 1, f u := ht.trans h0.symm
  apply heq.trans
  apply lintegral_congr_ae
  have hne : ∀ᵐ u : ℝ ∂volume.restrict (Ioc (0 : ℝ) 1), u ≠ 1 :=
    ae_restrict_of_ae ((Set.countable_singleton (1 : ℝ)).ae_notMem volume)
  filter_upwards [ae_restrict_mem measurableSet_Ioc,hne] with u hu hune
  change F (Int.fract u) = F u
  rw [Int.fract_eq_self.mpr ⟨hu.1.le,lt_of_le_of_ne hu.2 hune⟩]

/-- Scaling the true vertical slice of the Farey triangle produces the
uniform fractional coordinate, with the exact Jacobian a. -/
lemma lintegral_farey_fractional_slice (F : ℝ → ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    (∫⁻ b in Ioc (1-a) 1, F (Int.fract (b/a))) =
      ENNReal.ofReal a * ∫⁻ θ in Ioc (0 : ℝ) 1, F θ := by
  let L : ℝ := (1-a)/a
  have him : (fun u : ℝ => a*u) '' Ioc L (L+1) = Ioc (1-a) 1 := by
    ext b
    constructor
    · rintro ⟨u,hu,rfl⟩
      have h1 : a*L = 1-a := by dsimp [L]; field_simp
      have h2 : a*(L+1) = 1 := by rw [mul_add,h1]; ring
      exact ⟨by nlinarith [mul_lt_mul_of_pos_left hu.1 ha],by nlinarith [mul_le_mul_of_nonneg_left hu.2 ha.le]⟩
    · intro hb
      refine ⟨b/a,?_,by field_simp⟩
      constructor
      · exact (div_lt_div_iff_of_pos_right ha).mpr hb.1
      · have h2 : L+1 = 1/a := by dsimp [L]; field_simp; ring
        rw [h2]
        exact (div_le_div_iff_of_pos_right ha).mpr hb.2
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioc L (L+1))
    measurableSet_Ioc (fun u hu => ((hasDerivAt_id u).const_mul a).hasDerivWithinAt)
    (fun u hu v hv h => (mul_left_cancel₀ ha.ne' h))
    (fun b => F (Int.fract (b/a)))
  simp only [id_eq,mul_one] at hj
  rw [him] at hj
  simp only [mul_one,abs_of_pos ha,mul_div_cancel_left₀ _ ha.ne'] at hj
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_fract_period] at hj
  exact hj

end
end Paper14
