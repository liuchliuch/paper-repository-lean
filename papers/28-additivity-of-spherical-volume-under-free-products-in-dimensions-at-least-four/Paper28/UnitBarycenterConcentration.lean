import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! The second-moment concentration argument in (16): a probability on
unit vectors with unit barycenter is concentrated at that barycenter. This
is proved for actual Bochner integrals in any real Hilbert space. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open MeasureTheory
open scoped InnerProductSpace
variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem unit_barycenter_concentration (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → H) (hf : Integrable f μ) (u : H) (hu : ‖u‖ = 1)
    (hUnit : ∀ᵐ x ∂μ, ‖f x‖ = 1) (hMean : ∫ x, f x ∂μ = u) :
    ∀ᵐ x ∂μ, f x = u := by
  have hEq : (fun x => ‖f x-u‖^2) =ᵐ[μ] (fun x => 2-2*inner ℝ (f x) u) := by
    filter_upwards [hUnit] with x hx
    rw [norm_sub_sq_real,hx,hu]
    ring
  have hInt : Integrable (fun x => 2-2*inner ℝ (f x) u) μ :=
    (integrable_const (2 : ℝ)).sub ((hf.inner_const u).const_mul 2)
  have hSqInt : Integrable (fun x => ‖f x-u‖^2) μ := hInt.congr hEq.symm
  have hInnerMean : ∫ x, inner ℝ (f x) u ∂μ = 1 := by
    calc
      _ = inner ℝ u (∫ x, f x ∂μ) := by
        simpa only [real_inner_comm] using integral_inner hf u
      _ = 1 := by rw [hMean,real_inner_self_eq_norm_sq,hu]; norm_num
  have hZero : ∫ x, ‖f x-u‖^2 ∂μ = 0 := by
    rw [integral_congr_ae hEq,integral_sub (integrable_const (2 : ℝ)) ((hf.inner_const u).const_mul 2),
      integral_const_mul]
    rw [hInnerMean]
    simp
  have hAe := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖f x-u‖) hSqInt).mp hZero
  filter_upwards [hAe] with x hx
  have hn : ‖f x-u‖ = 0 := (sq_eq_zero_iff).mp hx
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end Paper28
