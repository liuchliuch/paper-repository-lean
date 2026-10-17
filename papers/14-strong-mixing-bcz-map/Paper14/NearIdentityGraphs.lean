import Paper14.BoundedProductLimits
import Paper14.GraphMeasures
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Topology.UniformSpace.HeineCantor

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Paper14
noncomputable section

/-- Bounded convergence in probability implies convergence of integrals. -/
theorem integral_tendsto_zero_of_inMeasure_bounded {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] {f : ℕ → A → ℝ}
    (hf : ∀ n, Measurable (f n)) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ n x, ‖f n x‖ ≤ K)
    (hlim : TendstoInMeasure μ f atTop (fun _ => 0)) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 0) := by
  have hui : UnifIntegrable f 1 μ := by
    intro ε hε
    obtain ⟨δ,hδ,hδε⟩ := (unifIntegrable_const (ι := ℕ) (g := fun _ : A => K)
      (by norm_num : (1 : ℝ≥0∞) ≤ 1) (by norm_num) (memLp_const (μ := μ) K)) hε
    refine ⟨δ,hδ,fun n s hs hμs => ?_⟩
    apply le_trans ?_ (hδε n s hs hμs)
    apply eLpNorm_mono_ae
    exact Eventually.of_forall (fun x => by
      by_cases hx : x ∈ s
      · simpa only [indicator_of_mem hx,Real.norm_of_nonneg hK] using hb n x
      · simp [indicator_of_notMem hx,norm_zero])
  have hlp := tendsto_Lp_finite_of_tendstoInMeasure (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    (by norm_num) (fun n => (hf n).aestronglyMeasurable) (MemLp.zero' : MemLp (fun _ : A => (0 : ℝ)) 1 μ) hui hlim
  have hi : ∀ᶠ n in atTop, Integrable (f n) μ := Eventually.of_forall
    (fun n => integrable_of_measurable_bound (hf n) K (hb n))
  simpa only [integral_zero] using tendsto_integral_of_L1' (fun _ : A => (0 : ℝ)) (integrable_zero A ℝ μ) hi hlp

/-- The continuous graph-test error in paper Ex27 tends to zero, using
only the fixed graph marginals and convergence in measure of the conjugacy. -/
theorem near_identity_graph_integral_times {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {T : E → E}
    (hT : MeasurePreserving T μ μ) (φ : ℕ → E → E)
    (hφ : ∀ n, Measurable (φ n)) (hlim : TendstoInMeasure μ φ atTop id)
    (F : (E × E) →ᵇ ℝ) (a : ℕ → ℕ) :
    Tendsto (fun n => ∫ x, F (φ n x,φ n (T^[a n] x)) - F (x,T^[a n] x) ∂μ)
      atTop (𝓝 0) := by
  let e : ℕ → E → ℝ := fun n x => F (φ n x,φ n (T^[a n] x)) - F (x,T^[a n] x)
  have he : ∀ n, Measurable (e n) := by
    intro n
    exact (F.continuous.measurable.comp ((hφ n).prodMk ((hφ n).comp (hT.measurable.iterate (a n))))).sub
      (F.continuous.measurable.comp (measurable_id.prodMk (hT.measurable.iterate (a n))))
  have hb : ∀ n x, ‖e n x‖ ≤ 2*‖F‖ := by
    intro n x
    dsimp [e]
    calc _ ≤ ‖F (φ n x,φ n (T^[a n] x))‖ + ‖F (x,T^[a n] x)‖ := norm_sub_le _ _
         _ ≤ 2*‖F‖ := by nlinarith [F.norm_coe_le_norm (φ n x,φ n (T^[a n] x)),F.norm_coe_le_norm (x,T^[a n] x)]
  have hm : TendstoInMeasure μ e atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    obtain ⟨δ,hδ,hδε⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous F.continuous) ε hε
    let A : ℕ → Set E := fun n => {x | δ ≤ dist (φ n x) x}
    have hA (n : ℕ) : MeasurableSet (A n) :=
      measurableSet_le measurable_const ((hφ n).dist measurable_id)
    have hsmall : Tendsto (fun n => μ (A n)) atTop (𝓝 0) :=
      tendstoInMeasure_iff_dist.mp hlim δ hδ
    have hsub (n : ℕ) : {x | ε ≤ dist (e n x) 0} ⊆ A n ∪ (T^[a n]) ⁻¹' A n := by
      intro x hx
      by_contra hbad
      have ha : dist (φ n x) x < δ := by simpa only [mem_union,mem_preimage,mem_setOf_eq,not_or,not_le,A] using (not_or.mp hbad).1
      have hb : dist (φ n (T^[a n] x)) (T^[a n] x) < δ := by
        exact lt_of_not_ge (not_or.mp hbad).2
      have hp : dist (φ n x,φ n (T^[a n] x)) (x,T^[a n] x) < δ := by
        rw [Prod.dist_eq]; exact max_lt ha hb
      have hh := hδε hp
      have hdist : dist (e n x) 0 = dist (F (φ n x,φ n (T^[a n] x))) (F (x,T^[a n] x)) := by
        simp only [e,Real.dist_eq,sub_zero]
      have hxx : ε ≤ dist (e n x) 0 := hx
      apply (not_lt_of_ge hxx)
      rw [hdist]
      exact hh
    have hbound (n : ℕ) : μ {x | ε ≤ dist (e n x) 0} ≤ μ (A n) + μ (A n) := by
      apply (measure_mono (hsub n)).trans
      apply (measure_union_le _ _).trans
      rw [(hT.iterate (a n)).measure_preimage (hA n).nullMeasurableSet]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => μ (A n)+μ (A n)) atTop (𝓝 0) by simpa using hsmall.add hsmall)
      (fun _ => zero_le _) hbound
  exact integral_tendsto_zero_of_inMeasure_bounded he (by positivity) hb hm

theorem near_identity_graph_integral {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {T : E → E}
    (hT : MeasurePreserving T μ μ) (φ : ℕ → E → E)
    (hφ : ∀ n, Measurable (φ n)) (hlim : TendstoInMeasure μ φ atTop id)
    (F : (E × E) →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, F (φ n x,φ n (T^[n] x)) - F (x,T^[n] x) ∂μ)
      atTop (𝓝 0) := near_identity_graph_integral_times hT φ hφ hlim F id

end
end Paper14
