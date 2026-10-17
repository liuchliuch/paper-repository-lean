import Paper14.MixingL2
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace Paper14
noncomputable section

/-- Complex-valued L2 correlations, without a conjugation convention. -/
def StrongMixingComplexL2 {A : Type*} [MeasurableSpace A] (T : A → A) (μ : Measure A) : Prop :=
  ∀ f g : A → ℂ,MemLp f 2 μ → MemLp g 2 μ →
    Tendsto (fun n : ℕ => ∫ x,f x*g (T^[n] x) ∂μ) atTop
      (𝓝 ((∫ x,f x ∂μ)*(∫ x,g x ∂μ)))

/-- The source L2 correlation conclusion holds for complex as well as real functions. -/
theorem strongMixing_complexL2 {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    {T : A → A} (hT : MeasurePreserving T μ μ) (hS : StrongMixing T μ) : StrongMixingComplexL2 T μ := by
  intro f g hf hg
  have hL := (strongMixing_iff_L2 hT).mp hS
  have hfR : MemLp (fun x => (f x).re) 2 μ := hf.continuousLinearMap_comp Complex.reCLM
  have hfI : MemLp (fun x => (f x).im) 2 μ := hf.continuousLinearMap_comp Complex.imCLM
  have hgR : MemLp (fun x => (g x).re) 2 μ := hg.continuousLinearMap_comp Complex.reCLM
  have hgI : MemLp (fun x => (g x).im) 2 μ := hg.continuousLinearMap_comp Complex.imCLM
  have hp (n : ℕ) : Integrable (fun x => f x*g (T^[n] x)) μ :=
    memLp_one_iff_integrable.mp ((hg.comp_measurePreserving (hT.iterate n)).mul' hf)
  have hRe (n : ℕ) : (∫ x,f x*g (T^[n] x) ∂μ).re=
      (∫ x,(f x).re*(g (T^[n] x)).re ∂μ)-(∫ x,(f x).im*(g (T^[n] x)).im ∂μ) := by
    have hpart := integral_re (hp n)
    simp only [RCLike.re_eq_complex_re] at hpart
    rw [← hpart]
    change (∫ x,(f x*g (T^[n] x)).re ∂μ)=_
    simp_rw [Complex.mul_re]
    exact integral_sub (integrable_mul_iterate hT hfR hgR n) (integrable_mul_iterate hT hfI hgI n)
  have hIm (n : ℕ) : (∫ x,f x*g (T^[n] x) ∂μ).im=
      (∫ x,(f x).re*(g (T^[n] x)).im ∂μ)+(∫ x,(f x).im*(g (T^[n] x)).re ∂μ) := by
    have hpart := integral_im (hp n)
    simp only [RCLike.im_eq_complex_im] at hpart
    rw [← hpart]
    change (∫ x,(f x*g (T^[n] x)).im ∂μ)=_
    simp_rw [Complex.mul_im]
    exact integral_add (integrable_mul_iterate hT hfR hgI n) (integrable_mul_iterate hT hfI hgR n)
  have hfInt := hf.integrable (by norm_num : (1 : ℝ≥0∞)≤2)
  have hgInt := hg.integrable (by norm_num : (1 : ℝ≥0∞)≤2)
  have hfr : (∫ x,(f x).re ∂μ)=(∫ x,f x ∂μ).re := by
    simpa only [RCLike.re_eq_complex_re] using integral_re hfInt
  have hfi : (∫ x,(f x).im ∂μ)=(∫ x,f x ∂μ).im := by
    simpa only [RCLike.im_eq_complex_im] using integral_im hfInt
  have hgr : (∫ x,(g x).re ∂μ)=(∫ x,g x ∂μ).re := by
    simpa only [RCLike.re_eq_complex_re] using integral_re hgInt
  have hgi : (∫ x,(g x).im ∂μ)=(∫ x,g x ∂μ).im := by
    simpa only [RCLike.im_eq_complex_im] using integral_im hgInt
  have hR : Tendsto (fun n : ℕ => (∫ x,f x*g (T^[n] x) ∂μ).re) atTop
      (𝓝 (((∫ x,f x ∂μ)*(∫ x,g x ∂μ)).re)) := by
    simpa only [hRe,Complex.mul_re,← hfr,← hfi,← hgr,← hgi] using
        (hL _ _ hfR hgR).sub (hL _ _ hfI hgI)
  have hI : Tendsto (fun n : ℕ => (∫ x,f x*g (T^[n] x) ∂μ).im) atTop
      (𝓝 (((∫ x,f x ∂μ)*(∫ x,g x ∂μ)).im)) := by
    simpa only [hIm,Complex.mul_im,← hfr,← hfi,← hgr,← hgi] using
        (hL _ _ hfR hgI).add (hL _ _ hfI hgR)
  have ht := (Complex.equivRealProdCLM.symm.continuous.tendsto _).comp (hR.prodMk_nhds hI)
  simpa only [Complex.equivRealProdCLM_symm_apply,Complex.re_add_im] using ht

end
end Paper14
