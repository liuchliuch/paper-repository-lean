import Paper38.Transport
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableLIntegral

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Paper38.Transport

noncomputable section

variable {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E] [BorelSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E] [Nonempty E]

namespace Coupling

instance probability {μ ν : Measure E} [IsProbabilityMeasure μ] (π : Coupling μ ν) :
    IsProbabilityMeasure π.measure := by
  letI : IsProbabilityMeasure (π.measure.map Prod.fst) := by
    rw [π.fst_eq]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

/-- Exchange the two coordinates of an actual joint measure. -/
def swap {μ ν : Measure E} (π : Coupling μ ν) : Coupling ν μ where
  measure := π.measure.map Prod.swap
  fst_eq := by
    rw [Measure.map_map measurable_fst measurable_swap]
    exact π.snd_eq
  snd_eq := by
    rw [Measure.map_map measurable_snd measurable_swap]
    exact π.fst_eq

lemma quadraticCost_swap {μ ν : Measure E} (π : Coupling μ ν) :
    quadraticCost π.swap.measure = quadraticCost π.measure := by
  rw [quadraticCost, swap, lintegral_map (by fun_prop) measurable_swap]
  change (∫⁻ p, edist p.2 p.1 ^ 2 ∂π.measure) = quadraticCost π.measure
  simp only [edist_comm]
  rfl

variable {μ ν ξ : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The usual gluing measure: first sample (x,y) from the first coupling,
then sample z from the second coupling conditional on y. -/
def gluingJoint (π : Coupling μ ν) (τ : Coupling ν ξ) : Measure ((E × E) × E) :=
  π.measure ⊗ₘ (τ.measure.condKernel.comap Prod.snd measurable_snd)

lemma gluingJoint_fst (π : Coupling μ ν) (τ : Coupling ν ξ) :
    (gluingJoint π τ).map Prod.fst = π.measure :=
  Measure.fst_compProd _ _

lemma gluingJoint_snd (π : Coupling μ ν) (τ : Coupling ν ξ) :
    (gluingJoint π τ).map Prod.snd = ξ := by
  have hd : ν ⊗ₘ τ.measure.condKernel = τ.measure := by
    have hf : τ.measure.fst = ν := τ.fst_eq
    simpa only [hf] using τ.measure.disintegrate τ.measure.condKernel
  ext S hS
  calc
    (gluingJoint π τ).map Prod.snd S =
        ∫⁻ p, τ.measure.condKernel p.2 S ∂π.measure := by
      rw [Measure.map_apply measurable_snd hS]
      rw [gluingJoint, Measure.compProd_apply (measurable_snd hS)]
      rfl
    _ = ∫⁻ y, τ.measure.condKernel y S ∂ν := by
      have hm := lintegral_map (μ := π.measure)
        (τ.measure.condKernel.measurable_coe hS) measurable_snd
      simpa only [π.snd_eq] using hm.symm
    _ = (ν ⊗ₘ τ.measure.condKernel).snd S := by
      rw [Measure.snd_apply hS, Measure.compProd_apply (measurable_snd hS)]
      rfl
    _ = ξ S := by rw [hd]; exact congrArg (fun m : Measure E => m S) τ.snd_eq

/-- Joining the outside coordinates of the gluing measure is a genuine coupling. -/
def glue (π : Coupling μ ν) (τ : Coupling ν ξ) : Coupling μ ξ where
  measure := (gluingJoint π τ).map (fun p => (p.1.1, p.2))
  fst_eq := by
    rw [Measure.map_map measurable_fst (by fun_prop)]
    change (gluingJoint π τ).map (Prod.fst ∘ Prod.fst) = μ
    rw [← Measure.map_map measurable_fst measurable_fst, gluingJoint_fst, π.fst_eq]
  snd_eq := by
    rw [Measure.map_map measurable_snd (by fun_prop)]
    exact gluingJoint_snd π τ

lemma gluing_cost_left (π : Coupling μ ν) (τ : Coupling ν ξ) :
    (∫⁻ p, edist p.1.1 p.1.2 ^ 2 ∂gluingJoint π τ) = quadraticCost π.measure := by
  unfold gluingJoint
  rw [Measure.lintegral_compProd (by fun_prop)]
  simp [quadraticCost]

lemma gluing_cost_right (π : Coupling μ ν) (τ : Coupling ν ξ) :
    (∫⁻ p, edist p.1.2 p.2 ^ 2 ∂gluingJoint π τ) = quadraticCost τ.measure := by
  have hd : ν ⊗ₘ τ.measure.condKernel = τ.measure := by
    have hf : τ.measure.fst = ν := τ.fst_eq
    simpa only [hf] using τ.measure.disintegrate τ.measure.condKernel
  have hm : Measurable (fun y => ∫⁻ z, edist y z ^ 2 ∂τ.measure.condKernel y) :=
    (show Measurable (fun p : E × E => edist p.1 p.2 ^ 2) by fun_prop).lintegral_kernel_prod_right'
  calc
    (∫⁻ p, edist p.1.2 p.2 ^ 2 ∂gluingJoint π τ) =
        ∫⁻ p, ∫⁻ z, edist p.2 z ^ 2 ∂τ.measure.condKernel p.2 ∂π.measure := by
      rw [gluingJoint, Measure.lintegral_compProd (by fun_prop)]
      rfl
    _ = ∫⁻ y, ∫⁻ z, edist y z ^ 2 ∂τ.measure.condKernel y ∂ν := by
      have hmap := lintegral_map (μ := π.measure) hm measurable_snd
      simpa only [π.snd_eq] using hmap.symm
    _ = quadraticCost (ν ⊗ₘ τ.measure.condKernel) := by
      rw [quadraticCost, Measure.lintegral_compProd (by fun_prop)]
    _ = quadraticCost τ.measure := by rw [hd]

end Coupling

/-- Symmetry follows by exchanging the two marginal coordinates. -/
theorem w2sq_comm (μ ν : Measure E) : w2sq μ ν = w2sq ν μ := by
  have hle (μ ν : Measure E) : w2sq μ ν ≤ w2sq ν μ := by
    apply le_iInf
    intro π
    exact (w2sq_le_cost π.swap).trans_eq (Coupling.quadraticCost_swap π)
  exact le_antisymm (hle μ ν) (hle ν μ)

@[simp] theorem w2sq_self (μ : Measure E) : w2sq μ μ = 0 := by
  have hu := w2sq_map_map_le μ id id measurable_id measurable_id
  simpa using le_antisymm (by simpa using hu) (zero_le (w2sq μ μ))

lemma edist_sq_triangle (x y z : E) :
    edist x z ^ 2 ≤ 2 * edist x y ^ 2 + 2 * edist y z ^ 2 := by
  have ht := dist_triangle x y z
  have hn : dist x z ^ 2 ≤ 2 * dist x y ^ 2 + 2 * dist y z ^ 2 := by
    nlinarith [dist_nonneg (x := x) (y := z), dist_nonneg (x := x) (y := y),
      dist_nonneg (x := y) (y := z), sq_nonneg (dist x y - dist y z)]
  have he := ENNReal.ofReal_le_ofReal hn
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_pow (dist_nonneg (x := x) (y := z)),
    ENNReal.ofReal_pow (dist_nonneg (x := x) (y := y)),
    ENNReal.ofReal_pow (dist_nonneg (x := y) (y := z))] at he
  simpa only [edist_dist, ENNReal.ofReal_ofNat] using he

/-- Quadratic-cost gluing bound, with both marginal constraints proved. -/
theorem quadraticCost_glue_le {μ ν ξ : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Coupling μ ν) (τ : Coupling ν ξ) :
    quadraticCost (π.glue τ).measure ≤
      2 * quadraticCost π.measure + 2 * quadraticCost τ.measure := by
  calc
    quadraticCost (π.glue τ).measure =
        ∫⁻ p, edist p.1.1 p.2 ^ 2 ∂Coupling.gluingJoint π τ := by
      unfold quadraticCost Coupling.glue
      rw [lintegral_map (by fun_prop) (by fun_prop)]
    _ ≤ ∫⁻ p, 2 * edist p.1.1 p.1.2 ^ 2 + 2 * edist p.1.2 p.2 ^ 2
        ∂Coupling.gluingJoint π τ :=
      lintegral_mono (fun p => edist_sq_triangle p.1.1 p.1.2 p.2)
    _ = _ := by
      rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
        lintegral_const_mul _ (by fun_prop), Coupling.gluing_cost_left,
        Coupling.gluing_cost_right]

/-- Gluing also preserves every verified scalar two-leg quadratic estimate. -/
theorem quadraticCost_glue_le_of_distortion {μ ν ξ : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Coupling μ ν) (τ : Coupling ν ξ) (a b : ℝ≥0)
    (h : ∀ x y z : E, edist x z ^ 2 ≤
      (a : ℝ≥0∞) * edist x y ^ 2 + (b : ℝ≥0∞) * edist y z ^ 2) :
    quadraticCost (π.glue τ).measure ≤
      (a : ℝ≥0∞) * quadraticCost π.measure +
      (b : ℝ≥0∞) * quadraticCost τ.measure := by
  calc
    quadraticCost (π.glue τ).measure =
        ∫⁻ p, edist p.1.1 p.2 ^ 2 ∂Coupling.gluingJoint π τ := by
      unfold quadraticCost Coupling.glue
      rw [lintegral_map (by fun_prop) (by fun_prop)]
    _ ≤ ∫⁻ p, (a : ℝ≥0∞) * edist p.1.1 p.1.2 ^ 2 +
        (b : ℝ≥0∞) * edist p.1.2 p.2 ^ 2 ∂Coupling.gluingJoint π τ :=
      lintegral_mono (fun p => h p.1.1 p.1.2 p.2)
    _ = _ := by
      rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
        lintegral_const_mul _ (by fun_prop), Coupling.gluing_cost_left,
        Coupling.gluing_cost_right]

theorem w2sq_triangle_of_distortion (μ ν ξ : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    (a b : ℝ≥0)
    (h : ∀ x y z : E, edist x z ^ 2 ≤
      (a : ℝ≥0∞) * edist x y ^ 2 + (b : ℝ≥0∞) * edist y z ^ 2) :
    w2sq μ ξ ≤ (a : ℝ≥0∞) * w2sq μ ν + (b : ℝ≥0∞) * w2sq ν ξ := by
  letI : Nonempty (Coupling μ ν) := ⟨Coupling.independent μ ν⟩
  letI : Nonempty (Coupling ν ξ) := ⟨Coupling.independent ν ξ⟩
  change w2sq μ ξ ≤ (a : ℝ≥0∞) * (⨅ π : Coupling μ ν, quadraticCost π.measure) +
    (b : ℝ≥0∞) * (⨅ τ : Coupling ν ξ, quadraticCost τ.measure)
  rw [ENNReal.mul_iInf (by simp), ENNReal.mul_iInf (by simp)]
  apply ENNReal.le_iInf_add_iInf
  intro π τ
  exact (w2sq_le_cost (π.glue τ)).trans (quadraticCost_glue_le_of_distortion π τ a b h)

/-- Weighted squared triangle bound, useful for continuity at a nonzero
transport cost as the cost of one leg tends to zero. -/
theorem w2sq_triangle_weighted (μ ν ξ : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    (ε : ℝ≥0) (hε : ε ≠ 0) :
    w2sq μ ξ ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) * w2sq μ ν +
      ((1 + ε⁻¹ : ℝ≥0) : ℝ≥0∞) * w2sq ν ξ := by
  apply w2sq_triangle_of_distortion μ ν ξ (1 + ε) (1 + ε⁻¹)
  intro x y z
  have hεreal : (0 : ℝ) < ε := by exact_mod_cast pos_iff_ne_zero.mpr hε
  have hscalar : (dist x y + dist y z) ^ 2 ≤
      (1 + (ε : ℝ)) * dist x y ^ 2 + (1 + (ε : ℝ)⁻¹) * dist y z ^ 2 := by
    have heq : (1 + (ε : ℝ)) * dist x y ^ 2 + (1 + (ε : ℝ)⁻¹) * dist y z ^ 2 -
        (dist x y + dist y z) ^ 2 = ((ε : ℝ) * dist x y - dist y z) ^ 2 / ε := by
      field_simp [ne_of_gt hεreal]
      <;> ring
    have hp : 0 ≤ ((ε : ℝ) * dist x y - dist y z) ^ 2 / ε := by positivity
    linarith
  have hdist : dist x z ^ 2 ≤ (dist x y + dist y z) ^ 2 := by
    exact pow_le_pow_left₀ dist_nonneg (dist_triangle x y z) _
  have he := ENNReal.ofReal_le_ofReal (hdist.trans hscalar)
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (dist_nonneg (x := x) (y := z)),
    ENNReal.ofReal_pow (dist_nonneg (x := x) (y := y)),
    ENNReal.ofReal_pow (dist_nonneg (x := y) (y := z))] at he
  have hc1 : ENNReal.ofReal (1 + (ε : ℝ)) = ((1 + ε : ℝ≥0) : ℝ≥0∞) := by
    simpa only [NNReal.coe_add, NNReal.coe_one] using (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (((1 + ε : ℝ≥0) : ℝ)) = ((1 + ε : ℝ≥0) : ℝ≥0∞))
  have hc2 : ENNReal.ofReal (1 + (ε : ℝ)⁻¹) = ((1 + ε⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    simpa only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_inv] using
      (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (((1 + ε⁻¹ : ℝ≥0) : ℝ)) = ((1 + ε⁻¹ : ℝ≥0) : ℝ≥0∞))
  rw [hc1, hc2] at he
  simpa only [edist_dist] using he

/-- The squared Wasserstein triangle estimate used in the paper. -/
theorem w2sq_triangle (μ ν ξ : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    w2sq μ ξ ≤ 2 * w2sq μ ν + 2 * w2sq ν ξ := by
  letI : Nonempty (Coupling μ ν) := ⟨Coupling.independent μ ν⟩
  letI : Nonempty (Coupling ν ξ) := ⟨Coupling.independent ν ξ⟩
  change w2sq μ ξ ≤ 2 * (⨅ π : Coupling μ ν, quadraticCost π.measure) +
    2 * (⨅ τ : Coupling ν ξ, quadraticCost τ.measure)
  rw [ENNReal.mul_iInf (by simp), ENNReal.mul_iInf (by simp)]
  apply ENNReal.le_iInf_add_iInf
  intro π τ
  exact (w2sq_le_cost (π.glue τ)).trans (quadraticCost_glue_le π τ)

end

end Paper38.Transport
