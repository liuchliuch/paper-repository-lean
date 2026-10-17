import Paper14.FixedLimitDominance
import Paper14.GraphMixing

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

/-- Every graph subsequential limit is the product under the original
excess-return assumptions. The same fixed limit is used for every alpha. -/
theorem graph_limit_eq_product_of_excess {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E] [Nonempty E]
    {μ : Measure E} [IsProbabilityMeasure μ] {T : E → E} (hweak : WeakMixing T μ)
    (Y : ℕ → ℝ → Set E) (φ : ℕ → ℝ → E → E) (ρ : ℕ → ℝ → ℝ)
    (hsections : ∀ α : ℝ, 0 < α → ∀ᶠ n : ℕ in atTop,
      MeasurableSet (Y n α) ∧ 0 < μ (Y n α) ∧ ρ n α = (μ (Y n α)).toReal)
    (hconj : ConjNearId T μ Y φ) (hmoment : ExcessMomentBound ρ)
    (hzero : ZeroExcessSmall T μ Y ρ)
    (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (ν : FiniteMeasure (E × E))
    (hgraph : Tendsto (fun n => graphFinite (T^[a n]) μ) atTop (𝓝 ν)) :
    (ν : Measure (E × E)) = μ.prod μ := by
  have hνmass : ν.mass = 1 := by
    have hh := hgraph.mass
    simp only [graphFinite_mass_one (hweak.1.measurable.iterate _)] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  letI : IsProbabilityMeasure (ν : Measure (E × E)) := ⟨by rw [← FiniteMeasure.ennreal_mass,hνmass,ENNReal.coe_one]⟩
  apply probability_eq_of_approx_product_dom (μ.prod μ) (ν : Measure (E × E))
  intro ε hε
  obtain ⟨α0,hα0⟩ := hzero ε hε
  let α := max α0 0+1
  have hα : 0 < α := by dsimp [α]; linarith [le_max_right α0 0]
  have hαbig : α0 < α := by dsimp [α]; linarith [le_max_left α0 0]
  obtain ⟨Nz,hNz⟩ := hα0 α hαbig
  obtain ⟨hρ,Cr,hCr⟩ := hmoment α hα
  obtain ⟨hΦ,hnear⟩ := hconj α hα
  have hsect := hsections α hα
  have hρm : Tendsto (fun n => μ.real (Y n α)) atTop (𝓝 1) := by
    apply (tendsto_congr' ?_).mpr hρ
    filter_upwards [hsect] with n hn
    exact hn.2.2.symm
  let C : ℝ≥0 := ⟨max Cr 0,le_max_right Cr 0⟩
  have hCrC : Cr ≤ (C : ℝ) := le_max_left Cr 0
  have hmean : ∀ᶠ n : ℕ in atTop, (n : ℝ)*((μ (Y n α)).toReal⁻¹-1) ≤ C := by
    filter_upwards [hsect,hCr] with n hn hcn
    rw [← hn.2.2]
    exact hcn.trans hCrC
  have hrec := reciprocalSectionMass_tendsto μ (fun n => Y n α) hρm
  have hrec2 : ∀ᶠ n in atTop, reciprocalSectionMass μ (Y n α) ≤ 2 :=
    (hrec.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ≥0) < 2))).mono (fun _ hn => hn.le)
  have hz : ∀ᶠ n in atTop, normalizedRestriction μ (Y n α)
      {x ∈ Y n α | Rn T (Y n α) n x = n} ≤ ENNReal.ofReal ε :=
    (eventually_ge_atTop Nz).mono (fun n hn => hNz n hn)
  let Good : ℕ → Prop := fun n =>
    MeasurableSet (Y n α) ∧ 0 < μ (Y n α) ∧
    MeasurePreserving (φ n α) μ (normalizedRestriction μ (Y n α)) ∧
    (∀ᵐ x ∂μ, inducedMap T (Y n α) (φ n α x) = φ n α (T x)) ∧
    (μ (Y n α))⁻¹ ≤ (2 : ℝ≥0∞) ∧
    (n : ℝ)*((μ (Y n α)).toReal⁻¹-1) ≤ C ∧
    normalizedRestriction μ (Y n α) {x ∈ Y n α | Rn T (Y n α) n x = n} ≤ ENNReal.ofReal ε
  have hall : ∀ᶠ n in atTop, Good n := by
    filter_upwards [hsect,hΦ,hmean,hrec2,hz] with n hn hφn hcn hrn hzn
    refine ⟨hn.1,hn.2.1,hφn.1,hφn.2.2,?_,hcn,hzn⟩
    rw [← reciprocalSectionMass_coe hn.2.1]
    exact ENNReal.coe_le_coe.mpr hrn
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (ha.eventually hall)
  let b : ℕ → ℕ := fun n => a (n+N)
  let Yb := fun n => Y (b n) α
  let φb := fun n => φ (b n) α
  have hb (n : ℕ) : Good (b n) := hN (n+N) (by omega)
  have hbt : Tendsto b atTop atTop := ha.comp (tendsto_add_atTop_nat N)
  have hnearb : TendstoInMeasure μ φb atTop id := fun δ hδ => (hnear δ hδ).comp hbt
  exact graph_limit_product_lower hweak Yb φb (fun n => (hb n).1) (fun n => (hb n).2.1)
    (fun n => (hb n).2.2.1) (fun n => (hb n).2.2.2.1) (hρm.comp hbt) hnearb b 2 C
    (fun n => (hb n).2.2.2.2.1) (fun n => (hb n).2.2.2.2.2.1) hε
    (Eventually.of_forall (fun n => (hb n).2.2.2.2.2.2)) (hgraph.comp (tendsto_add_atTop_nat N))

/-- The complete original Theorem 4, with no added mathematical premise. -/
theorem Theorem4 {E : Type*} [MeasurableSpace E] [MetricSpace E] [CompactSpace E] [BorelSpace E]
    (T : E → E) (μ : Measure E) (Y : ℕ → ℝ → Set E)
    (φ : ℕ → ℝ → E → E) (ρ : ℕ → ℝ → ℝ) : Theorem4Statement T μ Y φ ρ := by
  intro hprob hinv hT hweak hsections hconj hmoment hzero
  letI : IsProbabilityMeasure μ := hprob
  cases isEmpty_or_nonempty E with
  | inl he =>
    letI : IsEmpty E := he
    have h0 : μ univ = 0 := (congrArg μ (Set.univ_eq_empty_iff.mpr he)).trans (measure_empty)
    exact False.elim (one_ne_zero ((measure_univ (μ := μ)).symm.trans h0))
  | inr he =>
    letI : Nonempty E := he
    apply strongMixing_of_graph_limits hT
    intro a ha ν hgraph
    exact graph_limit_eq_product_of_excess hweak Y φ ρ hsections hconj hmoment hzero a ha ν hgraph

end
end Paper14
