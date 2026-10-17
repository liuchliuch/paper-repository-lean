import GeometricMedianCoresets.RealFeatureMap
import Mathlib.MeasureTheory.Integral.Prod

/-! Squared-Hilbert representation of integrable real functions by subgraph indicators. -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace GeometricMedianCoresets.L1Feature

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [SFinite ν]

/-- Signed subgraph indicator, anchored at zero. -/
def step (f : Ω → ℝ) (p : Ω × ℝ) : ℝ := RealFeature.step (f p.1) p.2

lemma measurable_step {f : Ω → ℝ} (hf : Measurable f) : Measurable (step f) := by
  have heq : step f = fun p =>
      (if p.2 ≤ f p.1 then (1:ℝ) else 0) - (if p.2 ≤ 0 then (1:ℝ) else 0) := by
    funext p
    exact RealFeature.step_halfline _ _
  rw [heq]
  exact (measurable_const.ite (measurableSet_le measurable_snd (hf.comp measurable_fst))
    measurable_const).sub (measurable_const.ite (measurableSet_le measurable_snd measurable_const)
      measurable_const)

lemma integral_step_sub_sq (a b : ℝ) :
    (∫ t, (RealFeature.step a t - RealFeature.step b t) ^ 2) = |a - b| := by
  simp_rw [RealFeature.step_sub_sq]
  rw [integral_indicator measurableSet_uIoc, setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  rcases le_total a b with hab | hba
  · rw [uIoc_of_le hab, Real.volume_real_Ioc_of_le hab, abs_of_nonpos (sub_nonpos.2 hab)]
    ring
  · rw [uIoc_of_ge hba, Real.volume_real_Ioc_of_le hba, abs_of_nonneg (sub_nonneg.2 hba)]

lemma integrable_step_sub_sq {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable (f - g) ν) :
    Integrable (fun p => (step f p - step g p) ^ 2) (ν.prod (volume : Measure ℝ)) := by
  apply (integrable_prod_iff
    (((measurable_step hf).sub (measurable_step hg)).pow_const 2).aestronglyMeasurable).2
  constructor
  · apply Filter.Eventually.of_forall
    intro ω
    exact (memLp_two_iff_integrable_sq
      (((RealFeature.step_memLp (f ω)).sub (RealFeature.step_memLp (g ω))).1)).1
      ((RealFeature.step_memLp (f ω)).sub (RealFeature.step_memLp (g ω)))
  · have heq : (fun ω => ∫ t, ‖(step f (ω,t) - step g (ω,t)) ^ 2‖) =
        fun ω => |f ω - g ω| := by
      funext ω
      simp only [step, Real.norm_eq_abs, abs_pow, sq_abs]
      exact integral_step_sub_sq _ _
    rw [heq]
    exact hi.abs

lemma step_memLp {f : Ω → ℝ} (hf : Measurable f) (hi : Integrable f ν) :
    MemLp (step f) 2 (ν.prod (volume : Measure ℝ)) := by
  apply (memLp_two_iff_integrable_sq (measurable_step hf).aestronglyMeasurable).2
  have hzero : step (fun _ : Ω => (0:ℝ)) = 0 := by
    funext p
    simp [step, RealFeature.step]
  have hh := integrable_step_sub_sq (ν := ν) hf (measurable_const (a := (0:ℝ)))
    (hi.sub (integrable_zero Ω ℝ ν))
  simpa only [hzero, Pi.zero_apply, sub_zero] using hh

/-- A real L2 feature for an actual integrable real function. -/
def feature (f : Ω → ℝ) (hf : Measurable f) (hi : Integrable f ν) :
    Lp ℝ 2 (ν.prod (volume : Measure ℝ)) := (step_memLp (ν := ν) hf hi).toLp (step f)

/-- The norm identity follows from Tonelli/Fubini and the interval length formula. -/
theorem norm_sub_sq {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable f ν) (hj : Integrable g ν) :
    ‖feature f hf hi - feature g hg hj‖ ^ 2 = ∫ ω, |f ω - g ω| ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have heq : (fun p => ⟪(feature f hf hi - feature g hg hj) p,
      (feature f hf hi - feature g hg hj) p⟫) =ᵐ[ν.prod (volume : Measure ℝ)]
      fun p => (step f p - step g p) ^ 2 := by
    filter_upwards [Lp.coeFn_sub (feature f hf hi) (feature g hg hj),
      (step_memLp hf hi).coeFn_toLp, (step_memLp hg hj).coeFn_toLp] with p hs ha hb
    rw [hs]
    change (feature f hf hi) p = step f p at ha
    change (feature g hg hj) p = step g p at hb
    change ((feature f hf hi) p - (feature g hg hj) p) *
      ((feature f hf hi) p - (feature g hg hj) p) = _
    rw [ha, hb, ← pow_two]
  rw [integral_congr_ae heq, integral_prod _ (integrable_step_sub_sq hf hg (hi.sub hj))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => integral_step_sub_sq (f ω) (g ω)

end GeometricMedianCoresets.L1Feature
