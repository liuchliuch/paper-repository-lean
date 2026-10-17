import Paper35.VisibleCrossing
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Heterogeneous conditional slope slices

This is the genuine pushforward of the conditional bias-density slices.  Its
double integral is the weight-space Jacobian integral appearing after the
two-candidate area formula.  All integrals are nonnegative and extended-valued.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Paper35.Source.CrossingSlice
open WeightedModel Paper35.VisibleCrossing

variable {d : ℕ}

lemma slopeSlice_finite (m : WeightedModel d) (x u : Space d) (y : ℝ) :
    IsFiniteMeasure (m.slopeSlice x u y) := by
  haveI := m.probability
  haveI : IsFiniteMeasure (m.weights.withDensity (fun w => m.g w (y - inner ℝ w x))) :=
    isFiniteMeasure_withDensity
      (ne_top_of_le_ne_top m.average_finite.ne (scoreDensity_le_average m x y))
  exact Measure.isFiniteMeasure_map _ _

/-- The slope law is the pushforward of the actual conditional density slice. -/
theorem lintegral_slopeSlice (m : WeightedModel d) (x u : Space d) (y : ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ a, f a ∂m.slopeSlice x u y) =
      ∫⁻ w, m.g w (y - inner ℝ w x) * f (inner ℝ w u) ∂m.weights := by
  have hA : Measurable (fun w : Space d => inner ℝ w u) := by fun_prop
  have hg : Measurable (fun w : Space d => m.g w (y - inner ℝ w x)) :=
    m.measurable_g.comp (measurable_id.prodMk (measurable_const.sub (by fun_prop)))
  unfold slopeSlice
  rw [lintegral_map hf hA]
  exact lintegral_withDensity_eq_lintegral_mul _ hg (show Measurable
    (fun w : Space d => f (inner ℝ w u)) from hf.comp hA)

/-- The crossing kernel for two possibly different candidate laws. -/
def mixedKernel (m₁ m₂ : WeightedModel d) (x u : Space d) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ a, ∫⁻ a', ENNReal.ofReal |a - a'| ∂m₂.slopeSlice x u y ∂m₁.slopeSlice x u y

@[simp] theorem mixedKernel_self (m : WeightedModel d) (x u : Space d) (y : ℝ) :
    mixedKernel m m x u y = m.crossingKernel x u y := rfl

/-- Expanding both genuine slope pushforwards gives the actual two-weight
Jacobian kernel, including the two conditional bias densities. -/
theorem mixedKernel_eq_weights (m₁ m₂ : WeightedModel d) (x u : Space d) (y : ℝ) :
    mixedKernel m₁ m₂ x u y =
      ∫⁻ w₁, ∫⁻ w₂, ENNReal.ofReal |inner ℝ (w₁ - w₂) u| *
        m₁.g w₁ (y - inner ℝ w₁ x) * m₂.g w₂ (y - inner ℝ w₂ x)
          ∂m₂.weights ∂m₁.weights := by
  haveI := m₁.probability
  haveI := m₂.probability
  haveI := slopeSlice_finite m₂ x u y
  have hf : Measurable (fun a : ℝ =>
      ∫⁻ a', ENNReal.ofReal |a-a'| ∂m₂.slopeSlice x u y) :=
    ((measurable_fst.sub measurable_snd).abs.ennreal_ofReal).lintegral_prod_right'
  unfold mixedKernel
  rw [lintegral_slopeSlice m₁ x u y hf]
  apply lintegral_congr
  intro w₁
  have hinner := lintegral_slopeSlice m₂ x u y
    (show Measurable (fun a' : ℝ => ENNReal.ofReal |inner ℝ w₁ u - a'|) from
      (measurable_const.sub measurable_id).abs.ennreal_ofReal)
  rw [hinner, ← lintegral_const_mul _ (show Measurable (fun w₂ : Space d =>
      m₂.g w₂ (y-inner ℝ w₂ x) * ENNReal.ofReal |inner ℝ w₁ u-inner ℝ w₂ u|) from
    (m₂.measurable_g.comp (measurable_id.prodMk (measurable_const.sub (by fun_prop)))).mul
      ((measurable_const.sub (by fun_prop)).abs.ennreal_ofReal))]
  apply lintegral_congr
  intro w₂
  rw [inner_sub_left]
  ac_rfl

/-- The density-weighted Jacobian integrand is jointly measurable in the
spatial point, tangent, height, and both weights. -/
theorem measurable_mixedIntegrand (m₁ m₂ : WeightedModel d) :
    Measurable (fun z : ((Space d × Space d) × ℝ) × (Space d × Space d) =>
      ENNReal.ofReal |inner ℝ (z.2.1 - z.2.2) z.1.1.2| *
        m₁.g z.2.1 (z.1.2 - inner ℝ z.2.1 z.1.1.1) *
        m₂.g z.2.2 (z.1.2 - inner ℝ z.2.2 z.1.1.1)) := by
  have h₁ : Measurable (fun z : ((Space d × Space d) × ℝ) × (Space d × Space d) =>
      m₁.g z.2.1 (z.1.2 - inner ℝ z.2.1 z.1.1.1)) :=
    m₁.measurable_g.comp (measurable_snd.fst.prodMk (measurable_fst.snd.sub (by fun_prop)))
  have h₂ : Measurable (fun z : ((Space d × Space d) × ℝ) × (Space d × Space d) =>
      m₂.g z.2.2 (z.1.2 - inner ℝ z.2.2 z.1.1.1)) :=
    m₂.measurable_g.comp (measurable_snd.snd.prodMk (measurable_fst.snd.sub (by fun_prop)))
  exact ((by fun_prop : Measurable (fun z : ((Space d × Space d) × ℝ) ×
    (Space d × Space d) => inner ℝ (z.2.1-z.2.2) z.1.1.2)).abs.ennreal_ofReal.mul h₁).mul h₂

/-- No continuity or moment assumption is needed for joint kernel measurability. -/
theorem measurable_mixedKernel (m₁ m₂ : WeightedModel d) :
    Measurable (fun z : (Space d × Space d) × ℝ => mixedKernel m₁ m₂ z.1.1 z.1.2 z.2) := by
  haveI := m₁.probability
  haveI := m₂.probability
  have hm := (measurable_mixedIntegrand m₁ m₂).lintegral_prod_right'
    (ν := m₁.weights.prod m₂.weights)
  convert hm using 1
  funext z
  rw [mixedKernel_eq_weights]
  exact (lintegral_prod _ ((measurable_mixedIntegrand m₁ m₂).comp
    (measurable_const.prodMk measurable_id)).aemeasurable).symm

theorem measurable_crossingKernel (m : WeightedModel d) :
    Measurable (fun z : (Space d × Space d) × ℝ => m.crossingKernel z.1.1 z.1.2 z.2) :=
  measurable_mixedKernel m m

end Paper35.Source.CrossingSlice
