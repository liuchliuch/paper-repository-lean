import Paper06.Divergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Real BigOperators MeasureTheory
open scoped Classical

namespace Paper06.FinProb

variable {α Ω : Type*} [Fintype α] [MeasurableSpace Ω]

/-- The usual topology on the finite probability simplex, induced by its weights. -/
instance : TopologicalSpace (FinProb α) :=
  TopologicalSpace.induced (fun p : FinProb α => p.w) inferInstance

/-- Mixture measures use the Borel sigma algebra of the finite probability simplex. -/
instance : MeasurableSpace (FinProb α) := borel (FinProb α)

instance : BorelSpace (FinProb α) := ⟨rfl⟩

theorem continuous_weight (x : α) : Continuous (fun p : FinProb α => p.w x) :=
  (continuous_apply x).comp continuous_induced_dom

theorem measurable_weight (x : α) : Measurable (fun p : FinProb α => p.w x) :=
  (continuous_weight x).measurable

/-- Each atom of a probability mass function is at most one. -/
theorem atom_le_one (p : FinProb α) (x : α) : p.w x ≤ 1 := by
  rw [← p.sum_eq_one]
  exact Finset.single_le_sum (fun y _ => p.nonneg y) (Finset.mem_univ x)

theorem integrable_weight (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω → FinProb α) (hm : ∀ x, Measurable (fun ω => (q ω).w x)) (x : α) :
    Integrable (fun ω => (q ω).w x) μ := by
  apply (integrable_const (1 : ℝ)).mono' (hm x).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg ((q ω).nonneg x)]
    exact atom_le_one (q ω) x)

/-- An arbitrary probability mixture, without a finite-support restriction on μ. -/
noncomputable def integralMixture (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω → FinProb α) (hm : ∀ x, Measurable (fun ω => (q ω).w x)) : FinProb α where
  w x := ∫ ω, (q ω).w x ∂μ
  nonneg x := integral_nonneg (fun ω => (q ω).nonneg x)
  sum_eq_one := by
    rw [← integral_finset_sum _ (fun x _ => integrable_weight μ q hm x)]
    simp only [(q _).sum_eq_one]
    simp

/-- Event probability, computed from the finite probability law. -/
noncomputable def event (p : FinProb α) (E : α → Prop) : ℝ :=
  ∑ x, if E x then p.w x else 0

theorem event_nonneg (p : FinProb α) (E : α → Prop) : 0 ≤ event p E := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact p.nonneg x
  · exact le_rfl

theorem event_le_one (p : FinProb α) (E : α → Prop) : event p E ≤ 1 := by
  rw [← p.sum_eq_one]
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · exact le_rfl
  · exact p.nonneg x

theorem integralMixture_event (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω → FinProb α) (hm : ∀ x, Measurable (fun ω => (q ω).w x))
    (E : α → Prop) :
    event (integralMixture μ q hm) E = ∫ ω, event (q ω) E ∂μ := by
  unfold event integralMixture
  have hi (x : α) : Integrable (fun ω => if E x then (q ω).w x else 0) μ := by
    by_cases hx : E x
    · simpa [hx] using integrable_weight μ q hm x
    · simp [hx]
  rw [integral_finset_sum _ (fun x _ => hi x)]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x <;> simp [hx]

/-- Uniform pointwise event bounds survive arbitrary measurable probability mixtures. -/
theorem integralMixture_event_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω → FinProb α) (hm : ∀ x, Measurable (fun ω => (q ω).w x))
    (E : α → Prop) (C : ℝ) (hC : ∀ ω, event (q ω) E ≤ C) :
    event (integralMixture μ q hm) E ≤ C := by
  rw [integralMixture_event]
  have hi : Integrable (fun ω => event (q ω) E) μ := by
    exact integrable_finset_sum _ (fun x _ => by
      by_cases hx : E x
      · simpa [hx] using integrable_weight μ q hm x
      · simp [hx])
  have hb := integral_mono hi (integrable_const C) hC
  simpa using hb

/-- The mass of a product law is measurable whenever every one-site mass is measurable. -/
theorem measurable_product_weight (q : Ω → FinProb α)
    (hm : ∀ x, Measurable (fun ω => (q ω).w x)) (k : ℕ) (z : Fin k → α) :
    Measurable (fun ω => (productFinProb k (q ω)).w z) := by
  change Measurable (fun ω => ∏ i : Fin k, (q ω).w (z i))
  exact Finset.measurable_prod _ (fun i _ => hm (z i))

/-- The paper's M_{k,μ}, for any measurable probability mixture. -/
noncomputable def integralProductMixture (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω → FinProb α) (hm : ∀ x, Measurable (fun ω => (q ω).w x)) (k : ℕ) :
    FinProb (Fin k → α) :=
  integralMixture μ (fun ω => productFinProb k (q ω))
    (fun z => measurable_product_weight q hm k z)

/-- The original paper's product mixture for any Borel probability measure on any slice. -/
noncomputable def feasibleProductMixture (F : Set (FinProb α)) (μ : Measure F)
    [IsProbabilityMeasure μ] (k : ℕ) : FinProb (Fin k → α) :=
  integralProductMixture μ (fun q => q.val)
    (fun x => (measurable_weight x).comp measurable_subtype_coe) k

@[simp] theorem feasibleProductMixture_w (F : Set (FinProb α)) (μ : Measure F)
    [IsProbabilityMeasure μ] (k : ℕ) (z : Fin k → α) :
    (feasibleProductMixture F μ k).w z = ∫ q : F, ∏ i, q.val.w (z i) ∂μ := rfl

/-- Any bound valid for every feasible product component is also valid for
all Borel mixing measures, with no bound on their number of components. -/
theorem feasibleProductMixture_event_le (F : Set (FinProb α)) (μ : Measure F)
    [IsProbabilityMeasure μ] (k : ℕ) (E : (Fin k → α) → Prop) (C : ℝ)
    (hC : ∀ q : F, event (productFinProb k q.val) E ≤ C) :
    event (feasibleProductMixture F μ k) E ≤ C :=
  integralMixture_event_le μ (fun q : F => productFinProb k q.val)
    (fun z => measurable_product_weight (fun q : F => q.val)
      (fun x => (measurable_weight x).comp measurable_subtype_coe) k z) E C hC

section Atomic
variable {ι : Type*} [Fintype ι]

/-- A finite list of feasible components defines a genuine Borel mixing measure. -/
noncomputable def atomicMixingMeasure (F : Set (FinProb α)) (w : FinProb ι)
    (q : ι → F) : Measure F :=
  ∑ j, ENNReal.ofReal (w.w j) • Measure.dirac (q j)

instance atomicMixingMeasure_probability (F : Set (FinProb α)) (w : FinProb ι)
    (q : ι → F) : IsProbabilityMeasure (atomicMixingMeasure F w q) := by
  constructor
  simp only [atomicMixingMeasure, Measure.finset_sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => w.nonneg j), w.sum_eq_one,
    ENNReal.ofReal_one]

theorem integral_atomicMixingMeasure (F : Set (FinProb α)) (w : FinProb ι)
    (q : ι → F) (f : F → ℝ) (hf : Measurable f) :
    (∫ p, f p ∂atomicMixingMeasure F w q) = ∑ j, w.w j * f (q j) := by
  unfold atomicMixingMeasure
  rw [integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_smul_measure, integral_dirac' f (q j) hf.stronglyMeasurable,
      ENNReal.toReal_ofReal (w.nonneg j), smul_eq_mul]
  · intro j _
    exact (integrable_dirac' hf.stronglyMeasurable (by finiteness)).smul_measure
      ENNReal.ofReal_ne_top

/-- Finite-mixture existence results yield the same mixtures in the original
Borel-measure formulation, without changing any component. -/
theorem feasibleProductMixture_atomic (F : Set (FinProb α)) (w : FinProb ι)
    (q : ι → F) (k : ℕ) :
    feasibleProductMixture F (atomicMixingMeasure F w q) k =
      mixtureProduct k w.w w.nonneg w.sum_eq_one (fun j => (q j).val) := by
  apply ext
  intro z
  rw [feasibleProductMixture_w]
  exact integral_atomicMixingMeasure F w q (fun p => ∏ i, p.val.w (z i))
    (Finset.measurable_prod _ (fun i _ =>
      (measurable_weight (z i)).comp measurable_subtype_coe))

end Atomic

end Paper06.FinProb
