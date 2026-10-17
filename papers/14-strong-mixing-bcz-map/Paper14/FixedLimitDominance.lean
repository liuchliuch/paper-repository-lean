import Paper14.ExcessDecomposition
import Paper14.ProductDominance

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

lemma excessLevel_zero_measure {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasure μ] {T : E → E} (hT : MeasurePreserving T μ μ)
    {Y : Set E} (hY : MeasurableSet Y)
    (hTY : MeasurePreserving (inducedMap T Y) (normalizedRestriction μ Y) (normalizedRestriction μ Y)) (n : ℕ) :
    normalizedRestriction μ Y (excessLevel T Y n 0) =
      normalizedRestriction μ Y {x ∈ Y | Rn T Y n x = n} := by
  apply measure_congr
  filter_upwards [ae_Rn_ge hT hY hTY n] with x hx
  apply propext
  change (x ∈ Y ∧ excessDn T Y n x = 0) ↔ (x ∈ Y ∧ Rn T Y n x = n)
  rw [excessDn_iff_Rn_eq_add T Y n 0 x hx,Nat.add_zero]

/-- A fixed graph limit dominates the product up to the actual zero-excess
probability. Components are constructed by simultaneous subsequences in
this theorem, rather than supplied as a decomposition certificate. -/
theorem graph_limit_product_lower {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E] [Nonempty E]
    {μ : Measure E} [IsProbabilityMeasure μ] {T : E → E} (hweak : WeakMixing T μ)
    (Y : ℕ → Set E) (φ : ℕ → E → E)
    (hY : ∀ n, MeasurableSet (Y n)) (hp : ∀ n, 0 < μ (Y n))
    (hφ : ∀ n, MeasurePreserving (φ n) μ (normalizedRestriction μ (Y n)))
    (hc : ∀ n, ∀ᵐ x ∂μ, inducedMap T (Y n) (φ n x) = φ n (T x))
    (hρ : Tendsto (fun n => μ.real (Y n)) atTop (𝓝 1))
    (hnear : TendstoInMeasure μ φ atTop id)
    (a : ℕ → ℕ) (B C : ℝ≥0)
    (hB : ∀ n, (μ (Y n))⁻¹ ≤ (B : ℝ≥0∞))
    (hC : ∀ n, (a n : ℝ)*((μ (Y n)).toReal⁻¹-1) ≤ C)
    {ε : ℝ} (hε : 0 < ε)
    (hzero : ∀ᶠ n in atTop, normalizedRestriction μ (Y n)
      {x ∈ Y n | Rn T (Y n) (a n) x = a n} ≤ ENNReal.ofReal ε)
    {ν : FiniteMeasure (E × E)}
    (hgraph : Tendsto (fun n => graphFinite (T^[a n]) μ) atTop (𝓝 ν)) :
    ENNReal.ofReal (1-ε) • μ.prod μ ≤ (ν : Measure (E × E)) := by
  have hT : Ergodic T μ := ⟨hweak.1,
    (measurePreserving_fst (μ := μ) (ν := μ)).preErgodic_of_preErgodic_conjugate
      hweak.2.toPreErgodic (fun p => rfl)⟩
  have hνmass : ν.mass = 1 := by
    have hh := hgraph.mass
    simp only [graphFinite_mass_one (hT.measurable.iterate _)] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  letI : IsProbabilityMeasure (ν : Measure (E × E)) := ⟨by rw [← FiniteMeasure.ennreal_mass,hνmass,ENNReal.coe_one]⟩
  let κ : ℕ → ℕ → FiniteMeasure (E × E) := fun n j => excessGraphFinite T μ (Y n) (a n) j
  obtain ⟨η,s,hs,hη,_⟩ := finiteMeasure_simultaneous_subsequence κ 1
    (fun n j => excessGraphFinite_mass_le_one hT.measurable μ _ _ j)
  let Ys := fun n => Y (s n)
  let φs := fun n => φ (s n)
  let a_s := fun n => a (s n)
  have hnears : TendstoInMeasure μ φs atTop id := fun δ hδ => (hnear δ hδ).comp hs.tendsto_atTop
  have hd := excess_decomposition_from_limits hT Ys φs (fun n => hY _) (fun n => hp _)
    (fun n => hφ _) (fun n => hc _) (hρ.comp hs.tendsto_atTop) hnears a_s B C
    (fun n => hB _) (fun n => hC _) (hgraph.comp hs.tendsto_atTop) hη
  obtain ⟨hsum,hshift,hmoment,hV,hmarg⟩ := hd
  let ηm : ℕ → Measure (E × E) := fun j => η j
  letI : IsFiniteMeasure (Measure.sum ηm) := by change IsFiniteMeasure (Measure.sum (fun j => (η j : Measure (E × E)))); rw [hsum]; infer_instance
  have hpos : ∀ j, 0 < j → ηm j = ηm j univ • μ.prod μ :=
    positive_components_of_invariant_decomposition hweak ηm (hsum.trans hshift.symm)
      (hmoment.trans_lt ENNReal.coe_lt_top) hV (fun j => (hmarg j).1) (fun j => (hmarg j).2)
  have hlower := product_lower_of_components ηm hsum hpos
  have hplim : Tendsto (fun n => ((κ (s n) 0).mass : ℝ≥0∞)) atTop (𝓝 ((η 0).mass : ℝ≥0∞)) :=
    ENNReal.continuous_coe.continuousAt.tendsto.comp (hη 0).mass
  have hp0 : (η 0 : Measure (E × E)) univ ≤ ENNReal.ofReal ε := by
    apply le_of_tendsto (by simpa only [FiniteMeasure.ennreal_mass] using hplim)
    filter_upwards [hs.tendsto_atTop.eventually hzero] with n hn
    rw [← FiniteMeasure.ennreal_mass]
    rw [show ((κ (s n) 0).mass : ℝ≥0∞) = normalizedRestriction μ (Y (s n))
      (excessLevel T (Y (s n)) (a (s n)) 0) from excessGraph_mass hT.measurable μ _ _ 0]
    rw [excessLevel_zero_measure hT.toMeasurePreserving (hY _)
      (induced_preserves_of_conjugacy hT.toMeasurePreserving (hY _) (hφ _) (hc _))]
    exact hn
  have hcoef : ENNReal.ofReal (1-ε) ≤ 1-(η 0 : Measure (E × E)) univ := by
    rw [ENNReal.ofReal_sub 1 hε.le,ENNReal.ofReal_one]
    exact tsub_le_tsub_left hp0 1
  apply le_trans ?_ hlower
  apply Measure.le_iff.mpr
  intro A hA
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul_right' hcoef (μ.prod μ A)

end
end Paper14
