import Paper26.AdaptiveModel
import Mathlib.MeasureTheory.Integral.Pi

/-!
# A common product outcome for finitely many actual quantum steps

Each original step has a fixed probability reference.  The lifted step reads
only its own coordinate of the finite product; the other coordinates are
parameter-independent auxiliary randomness.  The complete projected Born
kernel, and hence every measurable event and nonnegative error integral, is
preserved.  No law or statistical guarantee is assumed.
-/
noncomputable section

namespace Paper26.ProductOutcomeStep

open MeasureTheory ProbabilityTheory QuantumModel AdaptiveModel
open scoped ENNReal ComplexOrder

variable {I Γ H : Type*} [Fintype I]
  [Fintype Γ] [DecidableEq Γ] [MeasurableSpace H]
  {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)]
  (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
  (M : ∀ i, OneCopyStep Γ H (Ω i))
  (href : ∀ i, (M i).reference = Kernel.const H (μ i))

/-- An actual step on a common finite product outcome.  Only the selected
coordinate enters the effect; all references are the same probability kernel. -/
def lift (i : I) : OneCopyStep Γ H (∀ j, Ω j) where
  reference := Kernel.const H (Measure.pi μ)
  reference_sfinite := inferInstance
  effect h y := (M i).effect h (y i)
  entry_measurable a b := ((M i).entry_measurable a b).comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  positive_ae h := by
    apply ae_of_ae_map (μ := Measure.pi μ) (f := Function.eval i)
      (p := fun y => ((M i).effect h y).PosSemidef)
      (measurable_pi_apply i).aemeasurable
    rw [(measurePreserving_eval μ i).map_eq]
    simpa only [href i, Kernel.const_apply] using (M i).positive_ae h
  entry_integrable h a b := by
    change Integrable (fun y => (M i).effect h (y i) a b) (Measure.pi μ)
    apply integrable_comp_eval (μ := μ) (i := i)
      (f := fun y => (M i).effect h y a b)
    simpa only [href i, Kernel.const_apply] using (M i).entry_integrable h a b
  total h a b := by
    change (∫ y, (M i).effect h (y i) a b ∂Measure.pi μ) = _
    have hi : Integrable (fun y => (M i).effect h y a b) (μ i) := by
      simpa only [href i, Kernel.const_apply] using (M i).entry_integrable h a b
    rw [integral_comp_eval (μ := μ) (i := i) hi.aestronglyMeasurable]
    simpa only [href i, Kernel.const_apply] using (M i).total h a b

@[simp] theorem lift_reference (i : I) :
    (lift μ M href i).reference = Kernel.const H (Measure.pi μ) := rfl

@[simp] theorem lift_effect (i : I) (h : H) (y : ∀ j, Ω j) :
    (lift μ M href i).effect h y = (M i).effect h (y i) := rfl

@[simp] theorem lift_born (i : I) (ρ : Density Γ) (h : H) (y : ∀ j, Ω j) :
    (lift μ M href i).born ρ h y = (M i).born ρ h (y i) := rfl

/-- Every measurable nonnegative error is preserved under decoding the
selected coordinate, with no integrability or finiteness assumption. -/
theorem lintegral_comp_eval_lift (i : I) (ρ : Density Γ) (h : H)
    (f : Ω i → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, f (y i) ∂(lift μ M href i).bornKernel ρ h) =
      ∫⁻ y, f y ∂(M i).bornKernel ρ h := by
  rw [(lift μ M href i).bornKernel_lintegral ρ h (f := fun y => f (y i))
      (hf.comp (measurable_pi_apply i)),
    (M i).bornKernel_lintegral ρ h hf]
  change (∫⁻ y, ENNReal.ofReal ((M i).born ρ h (y i)) * f (y i)
    ∂Measure.pi μ) = _
  have hm : Measurable (fun y => ENNReal.ofReal ((M i).born ρ h y) * f y) :=
    ((M i).born_measurable ρ h).ennreal_ofReal.mul hf
  rw [← lintegral_map hm (measurable_pi_apply i), (measurePreserving_eval μ i).map_eq]
  rw [href i]
  rfl

/-- Exact event probability under the actual lifted Born law. -/
theorem event_lift (i : I) (ρ : Density Γ) (h : H)
    (s : Set (Ω i)) (hs : MeasurableSet s) :
    (lift μ M href i).bornKernel ρ h (Function.eval i ⁻¹' s) =
      (M i).bornKernel ρ h s := by
  classical
  have he := lintegral_comp_eval_lift μ M href i ρ h
    (s.indicator 1) (measurable_const.indicator hs)
  have hi : (fun y : ∀ j, Ω j => s.indicator (1 : Ω i → ℝ≥0∞) (y i)) =
      (Function.eval i ⁻¹' s).indicator 1 := by
    ext y
    rfl
  rw [hi, lintegral_indicator_one (hs.preimage (measurable_pi_apply i)),
    lintegral_indicator_one hs] at he
  exact he

/-- Decoding the selected coordinate recovers the whole original Born measure. -/
theorem bornKernel_map_eval_apply (i : I) (ρ : Density Γ) (h : H) :
    ((lift μ M href i).bornKernel ρ h).map (Function.eval i) =
      (M i).bornKernel ρ h := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  exact event_lift μ M href i ρ h s hs

/-- Equality of actual kernels, not only equality of one selected risk. -/
theorem bornKernel_map_eval (i : I) (ρ : Density Γ) :
    ((lift μ M href i).bornKernel ρ).map (Function.eval i) = (M i).bornKernel ρ := by
  apply Kernel.ext
  intro h
  rw [Kernel.map_apply _ (measurable_pi_apply i)]
  exact bornKernel_map_eval_apply μ M href i ρ h

/-- Real-valued measurable errors also have identical expectations.  This
uses the ordinary Bochner integral, with its standard nonintegrable convention. -/
theorem integral_comp_eval_lift (i : I) (ρ : Density Γ) (h : H)
    (f : Ω i → ℝ) (hf : Measurable f) :
    (∫ y, f (y i) ∂(lift μ M href i).bornKernel ρ h) =
      ∫ y, f y ∂(M i).bornKernel ρ h := by
  rw [← bornKernel_map_eval_apply μ M href i ρ h]
  exact (integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable).symm

/-- The history-dependent success event can be lifted without changing its
conditional probability at any history. -/
theorem joint_event_lift (i : I) (ρ : Density Γ) (h : H)
    (s : Set (H × Ω i)) (hs : MeasurableSet s) :
    (lift μ M href i).bornKernel ρ h {y | (h, y i) ∈ s} =
      (M i).bornKernel ρ h {y | (h, y) ∈ s} := by
  exact event_lift μ M href i ρ h (Prod.mk h ⁻¹' s)
    (hs.preimage measurable_prodMk_left)

end Paper26.ProductOutcomeStep
