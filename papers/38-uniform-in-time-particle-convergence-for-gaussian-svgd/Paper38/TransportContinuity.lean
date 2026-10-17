import Paper38.TransportGluing

/-! Continuity of the actual quadratic coupling infimum, proved from the
weighted gluing inequality rather than asserted as a Wasserstein oracle. -/
noncomputable section
namespace Paper38.Transport

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E] [BorelSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E] [Nonempty E]

lemma w2sq_perturbation_bounds (μ ν μ' ν' : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    (ε : ℝ≥0) (hε : ε ≠ 0) :
    let k : ℝ≥0∞ := (1 + ε : ℝ≥0)
    let j : ℝ≥0∞ := (1 + ε⁻¹ : ℝ≥0)
    (w2sq μ' ν' ≤ k ^ 2 * w2sq μ ν +
      (k * j * w2sq μ' μ + j * w2sq ν' ν)) ∧
    (w2sq μ ν ≤ k ^ 2 * w2sq μ' ν' +
      (k * j * w2sq μ' μ + j * w2sq ν' ν)) := by
  let k : ℝ≥0∞ := (1 + ε : ℝ≥0)
  let j : ℝ≥0∞ := (1 + ε⁻¹ : ℝ≥0)
  have hfirst := w2sq_triangle_weighted μ' ν ν' ε hε
  have hsecond := w2sq_triangle_weighted ν μ μ' ε hε
  have hsecond' : w2sq μ' ν ≤ k * w2sq μ ν + j * w2sq μ' μ := by
    simpa only [w2sq_comm ν μ', w2sq_comm ν μ, w2sq_comm μ μ', k, j] using hsecond
  have hreverse1 := w2sq_triangle_weighted μ ν' ν ε hε
  have hreverse2 := w2sq_triangle_weighted ν' μ' μ ε hε
  have hreverse2' : w2sq μ ν' ≤ k * w2sq μ' ν' + j * w2sq μ' μ := by
    simpa only [w2sq_comm ν' μ, w2sq_comm ν' μ', k, j] using hreverse2
  constructor
  · calc
      w2sq μ' ν' ≤ k * w2sq μ' ν + j * w2sq ν' ν := by
        simpa only [k, j, w2sq_comm ν ν'] using hfirst
      _ ≤ k * (k * w2sq μ ν + j * w2sq μ' μ) + j * w2sq ν' ν :=
        add_le_add_right (mul_le_mul_left' hsecond' k) _
      _ = _ := by ring
  · calc
      w2sq μ ν ≤ k * w2sq μ ν' + j * w2sq ν' ν := hreverse1
      _ ≤ k * (k * w2sq μ' ν' + j * w2sq μ' μ) + j * w2sq ν' ν :=
        add_le_add_right (mul_le_mul_left' hreverse2' k) _
      _ = _ := by ring

private lemma small_weight_exists {a b : ℝ≥0∞} (hab : a < b) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ 2 * a < b := by
  have hcont : Continuous (fun ε : ℝ≥0 => ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ 2) := by
    exact (ENNReal.continuous_pow 2).comp
      (ENNReal.continuous_coe.comp (continuous_const.add continuous_id))
  have ht : Tendsto (fun ε : ℝ≥0 => ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ 2 * a)
      (𝓝[>] 0) (𝓝 a) := by
    have h := ENNReal.Tendsto.mul_const (b := a) (hcont.tendsto 0) (Or.inl (by norm_num))
    simpa using h.mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hεlt, hεpos⟩ :=
    ((ht.eventually_lt_const hab).and self_mem_nhdsWithin).exists
  exact ⟨ε, hεpos, hεlt⟩

/-- If both marginal laws converge in quadratic transport, their mutual
quadratic costs converge, including a possibly infinite limiting cost. -/
theorem w2sq_tendsto_of_perturbations {ι : Type*} {f : Filter ι}
    (μ ν : Measure E) (μi νi : ι → Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [∀ i, IsProbabilityMeasure (μi i)] [∀ i, IsProbabilityMeasure (νi i)]
    (hμ : Tendsto (fun i => w2sq (μi i) μ) f (𝓝 0))
    (hν : Tendsto (fun i => w2sq (νi i) ν) f (𝓝 0)) :
    Tendsto (fun i => w2sq (μi i) (νi i)) f (𝓝 (w2sq μ ν)) := by
  have herr (ε : ℝ≥0) : Tendsto (fun i =>
      ((1 + ε : ℝ≥0) : ℝ≥0∞) * ((1 + ε⁻¹ : ℝ≥0) : ℝ≥0∞) * w2sq (μi i) μ +
      ((1 + ε⁻¹ : ℝ≥0) : ℝ≥0∞) * w2sq (νi i) ν) f (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul
      (a := ((1 + ε : ℝ≥0) : ℝ≥0∞) * ((1 + ε⁻¹ : ℝ≥0) : ℝ≥0∞)) hμ
      (Or.inr (ENNReal.mul_ne_top (by simp) (by simp)))
    have h2 := ENNReal.Tendsto.const_mul
      (a := ((1 + ε⁻¹ : ℝ≥0) : ℝ≥0∞)) hν (Or.inr (by simp))
    simpa only [mul_zero, add_zero] using h1.add h2
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨ε, hε, hsmall⟩ := small_weight_exists ha
    have hlim := (tendsto_const_nhds (x := ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ 2 * a)).add (herr ε)
    simp only [add_zero] at hlim
    have hevent := hlim.eventually_lt_const hsmall
    filter_upwards [hevent] with i hi
    by_contra hnot
    have hib : w2sq (μi i) (νi i) ≤ a := le_of_not_gt hnot
    have hp := (w2sq_perturbation_bounds μ ν (μi i) (νi i) ε hε.ne').2
    exact (not_lt_of_ge (hp.trans (add_le_add_right (mul_le_mul_left' hib _) _))) hi
  · intro b hb
    obtain ⟨ε, hε, hsmall⟩ := small_weight_exists hb
    have hlim := (tendsto_const_nhds (x := ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ 2 * w2sq μ ν)).add (herr ε)
    simp only [add_zero] at hlim
    have hevent := hlim.eventually_lt_const hsmall
    filter_upwards [hevent] with i hi
    exact ((w2sq_perturbation_bounds μ ν (μi i) (νi i) ε hε.ne').1).trans_lt hi

end Paper38.Transport
