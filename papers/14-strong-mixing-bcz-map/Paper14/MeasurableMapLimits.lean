import Paper14.GraphLimits
import Paper14.BoundedProductLimits

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Paper14
noncomputable section

lemma map_prod_marginals_le {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {η : Measure (E × E)} {C : ℝ≥0}
    {S T : E → E} (hS : MeasurePreserving S μ μ) (hT : MeasurePreserving T μ μ)
    (hf : η.fst ≤ C • μ) (hg : η.snd ≤ C • μ) :
    (Measure.map (Prod.map S T) η).fst ≤ C • μ ∧
    (Measure.map (Prod.map S T) η).snd ≤ C • μ := by
  constructor
  · calc _ = Measure.map S η.fst := by
           rw [Measure.fst,Measure.map_map measurable_fst (hS.measurable.prodMap hT.measurable),
             Measure.fst,Measure.map_map hS.measurable measurable_fst]
           rfl
         _ ≤ Measure.map S (C • μ) := Measure.map_mono hf hS.measurable
         _ = C • μ := by rw [Measure.map_smul,hS.map_eq]
  · calc _ = Measure.map T η.snd := by
           rw [Measure.snd,Measure.map_map measurable_snd (hS.measurable.prodMap hT.measurable),
             Measure.snd,Measure.map_map hT.measurable measurable_snd]
           rfl
         _ ≤ Measure.map T (C • μ) := Measure.map_mono hg hT.measurable
         _ = C • μ := by rw [Measure.map_smul,hT.map_eq]

lemma weak_limit_marginals_le_const {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E] [Nonempty E]
    (μ : FiniteMeasure E) {ηn : ℕ → FiniteMeasure (E × E)} {η : FiniteMeasure (E × E)}
    (hlim : Tendsto ηn atTop (𝓝 η)) (C : ℝ≥0)
    (hfst : ∀ n, (ηn n : Measure (E × E)).fst ≤ C • (μ : Measure E))
    (hsnd : ∀ n, (ηn n : Measure (E × E)).snd ≤ C • (μ : Measure E)) :
    (η : Measure (E × E)).fst ≤ C • (μ : Measure E) ∧
    (η : Measure (E × E)).snd ≤ C • (μ : Measure E) := by
  exact weak_limit_marginals_le (C • μ) hlim
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ≥0)) atTop (𝓝 1)) 1
    (fun _ => le_rfl) (fun n => by simpa only [one_smul] using hfst n)
    (fun n => by simpa only [one_smul] using hsnd n)

/-- Measurable, measure-preserving coordinate maps pass through joint weak
limits when their marginals are uniformly dominated. No continuity of the
dynamical maps is assumed. -/
theorem weak_limit_map_prod {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E] [Nonempty E]
    (μ : FiniteMeasure E) {ηn : ℕ → FiniteMeasure (E × E)} {η : FiniteMeasure (E × E)}
    (hlim : Tendsto ηn atTop (𝓝 η)) (C : ℝ≥0)
    (hfstn : ∀ n, (ηn n : Measure (E × E)).fst ≤ C • (μ : Measure E))
    (hsndn : ∀ n, (ηn n : Measure (E × E)).snd ≤ C • (μ : Measure E))
    {S T : E → E} (hS : MeasurePreserving S (μ : Measure E) μ)
    (hT : MeasurePreserving T (μ : Measure E) μ) :
    Tendsto (fun n => (ηn n).map (Prod.map S T)) atTop (𝓝 (η.map (Prod.map S T))) := by
  let F := Prod.map S T
  have hF : Measurable F := hS.measurable.prodMap hT.measurable
  obtain ⟨hηf,hηg⟩ := weak_limit_marginals_le_const μ hlim C hfstn hsndn
  obtain ⟨hηFf,hηFg⟩ := map_prod_marginals_le hS hT hηf hηg
  have hmass (n : ℕ) : (ηn n).mass ≤ (C • μ).mass := by
    apply ENNReal.coe_le_coe.mp
    rw [FiniteMeasure.ennreal_mass,FiniteMeasure.ennreal_mass]
    calc (ηn n : Measure (E × E)) univ = (ηn n : Measure (E × E)).fst univ := Measure.fst_univ.symm
         _ ≤ (C • (μ : Measure E)) univ := hfstn n univ
  apply tendsto_of_subseq_tendsto
  intro a ha
  have hb : ∀ (n : ℕ) (j : Unit),
      (((ηn (a n)).map F)).mass ≤ (C • μ).mass := by
    intro n j
    change ((ηn (a n)).map F) univ ≤ (C • μ).mass
    rw [FiniteMeasure.map_apply _ hF MeasurableSet.univ,preimage_univ]
    exact hmass _
  obtain ⟨ζ,s,hs,hζ,_⟩ := finiteMeasure_simultaneous_subsequence
    (fun n (_ : Unit) => (ηn (a n)).map F) (C • μ).mass hb
  have hζlim := hζ ()
  have hsource : Tendsto (fun n => ηn (a (s n))) atTop (𝓝 η) :=
    hlim.comp (ha.comp hs.tendsto_atTop)
  have hζf : ∀ n, (((ηn (a (s n))).map F) : Measure (E × E)).fst ≤ C • (μ : Measure E) :=
    fun n => (map_prod_marginals_le hS hT (hfstn _) (hsndn _)).1
  have hζg : ∀ n, (((ηn (a (s n))).map F) : Measure (E × E)).snd ≤ C • (μ : Measure E) :=
    fun n => (map_prod_marginals_le hS hT (hfstn _) (hsndn _)).2
  obtain ⟨hζf',hζg'⟩ := weak_limit_marginals_le_const μ hζlim C hζf hζg
  have heq : ζ () = η.map F := by
    apply finiteMeasure_eq_of_continuous_products (ζ ()) (η.map F) C hζf' hζg' hηFf hηFg
    intro f0 g0
    let F0 : (E × E) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
      ⟨fun z => f0 z.1*g0 z.2,by fun_prop⟩
    have hleft := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hζlim F0
    have hright := weak_limit_bounded_product hsource C
      (fun n => hfstn _) (fun n => hsndn _) hηf hηg
      (f0.continuous.measurable.comp hS.measurable) (g0.continuous.measurable.comp hT.measurable)
      (norm_nonneg f0) (norm_nonneg g0)
      (fun x => f0.norm_coe_le_norm (S x)) (fun x => g0.norm_coe_le_norm (T x))
    have hrewrite (κ : FiniteMeasure (E × E)) :
        (∫ z, F0 z ∂(κ.map F : Measure (E × E))) =
          ∫ z, f0 (S z.1)*g0 (T z.2) ∂(κ : Measure (E × E)) := by
      rw [FiniteMeasure.toMeasure_map,integral_map hF.aemeasurable F0.continuous.measurable.aestronglyMeasurable]
      rfl
    simp only [hrewrite] at hleft
    have hh := tendsto_nhds_unique hleft hright
    change (∫ z, F0 z ∂(ζ () : Measure (E × E))) = ∫ z, F0 z ∂(η.map F : Measure (E × E))
    rw [hrewrite]
    exact hh
  refine ⟨s,?_⟩
  simpa only [heq] using hζlim

end
end Paper14
