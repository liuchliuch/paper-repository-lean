import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Paper35.Source.CrossingFubini

/-- Tonelli separates a visibility mark in the remaining candidates from a
Jacobian-density factor in the selected weights, at their common path/height
parameter. No integrability or finiteness of the resulting integral is needed. -/
theorem lintegral_factor_three {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (τ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite τ]
    {V : A × C → ℝ≥0∞} {R : B × C → ℝ≥0∞}
    (hV : Measurable V) (hR : Measurable R) :
    (∫⁻ a, ∫⁻ b, ∫⁻ c, V (a,c) * R (b,c) ∂τ ∂ν ∂μ) =
      ∫⁻ c, (∫⁻ a, V (a,c) ∂μ) * (∫⁻ b, R (b,c) ∂ν) ∂τ := by
  have hf : Measurable (fun z : (A × B) × C => V (z.1.1,z.2) * R (z.1.2,z.2)) :=
    (hV.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hR.comp (measurable_fst.snd.prodMk measurable_snd))
  calc
    _ = ∫⁻ ab, ∫⁻ c, V (ab.1,c) * R (ab.2,c) ∂τ ∂μ.prod ν :=
      (lintegral_prod _ hf.lintegral_prod_right'.aemeasurable).symm
    _ = ∫⁻ c, ∫⁻ ab, V (ab.1,c) * R (ab.2,c) ∂μ.prod ν ∂τ :=
      lintegral_lintegral_swap hf.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro c
      have hVc : Measurable (fun a => V (a,c)) := hV.comp (measurable_id.prodMk measurable_const)
      have hRc : Measurable (fun b => R (b,c)) := hR.comp (measurable_id.prodMk measurable_const)
      have hprod : Measurable (fun ab : A × B => V (ab.1,c) * R (ab.2,c)) :=
        (hVc.comp measurable_fst).mul (hRc.comp measurable_snd)
      rw [lintegral_prod _ hprod.aemeasurable]
      simp_rw [lintegral_const_mul _ hRc]
      exact lintegral_mul_const _ hVc

end Paper35.Source.CrossingFubini
