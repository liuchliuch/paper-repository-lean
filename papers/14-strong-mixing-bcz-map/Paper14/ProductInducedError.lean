import Paper14.BoundedComposition
import Paper14.DominatedProductLimits
import Paper14.GraphMeasures

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

/-- A product-invariant bounded function has vanishing moving-section induced-iterate error. -/
theorem product_induced_invariant_error {E : Type*} [MeasurableSpace E] [MetricSpace E]
    [CompactSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
    {T : E → E} (hT : MeasurePreserving T μ μ) (Y : ℕ → Set E) (φ : ℕ → E → E)
    (hY : ∀ n,MeasurableSet (Y n))
    (hφ : ∀ n,MeasurePreserving (φ n) μ (normalizedRestriction μ (Y n)))
    (hc : ∀ n,∀ᵐ x ∂μ,inducedMap T (Y n) (φ n x)=φ n (T x))
    (hpoint : ∀ᵐ x ∂μ,Tendsto (fun n => φ n x) atTop (𝓝 x))
    (B : ℝ≥0) (hdom : ∀ n,normalizedRestriction μ (Y n)≤B • μ)
    (a : ℕ → ℕ) {F : E × E → ℝ} (hF : Measurable F) (hb : ∀ p,‖F p‖≤1)
    (hinv : ∀ p : E × E,F (T p.1,T p.2)=F p) :
    Tendsto (fun n => ∫ p,‖F ((inducedMap T (Y n))^[a n] p.1,(inducedMap T (Y n))^[a n] p.2)-F p‖
      ∂(normalizedRestriction μ (Y n)).prod (normalizedRestriction μ (Y n))) atTop (𝓝 0) := by
  let ν := fun n => normalizedRestriction μ (Y n)
  let Φ : ℕ → E × E → E × E := fun n => Prod.map (φ n) (φ n)
  let e : ℕ → E × E → ℝ := fun n p => ‖F (Φ n p)-F p‖
  let D : ℕ → E × E → ℝ := fun n p =>
    ‖F ((inducedMap T (Y n))^[a n] p.1,(inducedMap T (Y n))^[a n] p.2)-F p‖
  letI (n : ℕ) : IsFiniteMeasure (ν n) := isFiniteMeasure_of_le _ (hdom n)
  have hΦ (n : ℕ) : MeasurePreserving (Φ n) (μ.prod μ) ((ν n).prod (ν n)) := (hφ n).prod (hφ n)
  have hΦpoint : ∀ᵐ p ∂μ.prod μ,Tendsto (fun n => Φ n p) atTop (𝓝 p) := by
    filter_upwards [(measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hpoint,
      (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hpoint] with p hp hq
    exact hp.prodMk_nhds hq
  have hΦdom (n : ℕ) : Measure.map (Φ n) (μ.prod μ)≤(B*B) • μ.prod μ := by
    rw [(hΦ n).map_eq]
    exact product_domination (hdom n) (hdom n)
  have helim : Tendsto (fun n => ∫ p,e n p ∂μ.prod μ) atTop (𝓝 0) :=
    bounded_composition_L1_error Φ (fun n => (hΦ n).measurable) hΦpoint (B*B) hΦdom hF hb
  have hemeas (n : ℕ) : Measurable (e n) := ((hF.comp (hΦ n).measurable).sub hF).norm
  have heb (n : ℕ) (p : E × E) : ‖e n p‖≤2 := by
    change ‖‖F (Φ n p)-F p‖‖≤2
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by nlinarith [hb (Φ n p),hb p])
  have heI (n : ℕ) : Integrable (e n) (μ.prod μ) := integrable_of_measurable_bound (hemeas n) 2 (heb n)
  have hDmeas (n : ℕ) : Measurable (D n) :=
    ((hF.comp (((measurable_inducedMap hT.measurable (hY n)).iterate (a n)).prodMap
      ((measurable_inducedMap hT.measurable (hY n)).iterate (a n)))).sub hF).norm
  have hDb (n : ℕ) (p : E × E) : ‖D n p‖≤2 := by
    change ‖‖F ((inducedMap T (Y n))^[a n] p.1,(inducedMap T (Y n))^[a n] p.2)-F p‖‖≤2
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by nlinarith [hb ((inducedMap T (Y n))^[a n] p.1,(inducedMap T (Y n))^[a n] p.2),hb p])
  have hFiter (k : ℕ) (p : E × E) : F (T^[k] p.1,T^[k] p.2)=F p := by
    induction k with
    | zero => rfl
    | succ k ih => rw [iterate_succ_apply',iterate_succ_apply',hinv (T^[k] p.1,T^[k] p.2),ih]
  have hupper (n : ℕ) : (∫ p,D n p ∂(ν n).prod (ν n))≤2*(∫ p,e n p ∂μ.prod μ) := by
    let V := Prod.map (T^[a n]) (T^[a n])
    have hV : MeasurePreserving V (μ.prod μ) (μ.prod μ) := (hT.iterate (a n)).prod (hT.iterate (a n))
    have hleftI : Integrable (fun p => D n (Φ n p)) (μ.prod μ) :=
      integrable_of_measurable_bound ((hDmeas n).comp (hΦ n).measurable) 2 (fun p => hDb n _)
    have hecompI : Integrable (fun p => e n (V p)) (μ.prod μ) :=
      integrable_of_measurable_bound ((hemeas n).comp hV.measurable) 2 (fun p => heb n _)
    have hmap := integral_map (μ := μ.prod μ) (hΦ n).measurable.aemeasurable (hDmeas n).aestronglyMeasurable
    rw [(hΦ n).map_eq] at hmap
    rw [hmap]
    have hle : (∫ p,D n (Φ n p) ∂μ.prod μ)≤∫ p,e n (V p)+e n p ∂μ.prod μ := by
      apply integral_mono_ae hleftI (hecompI.add (heI n))
      have hcn := ae_conjugacy_iterate hT (hc n) (a n)
      filter_upwards [(measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hcn,
        (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hcn] with p hp hq
      change ‖F ((inducedMap T (Y n))^[a n] (φ n p.1),(inducedMap T (Y n))^[a n] (φ n p.2))-F (Φ n p)‖≤e n (V p)+e n p
      rw [hp,hq]
      have hh := norm_sub_le_norm_sub_add_norm_sub
        (F (φ n (T^[a n] p.1),φ n (T^[a n] p.2))) (F (T^[a n] p.1,T^[a n] p.2)) (F (Φ n p))
      rw [hFiter,norm_sub_rev (F p)] at hh
      simpa only [e,V,Φ,Prod.map,hFiter] using hh
    rw [integral_add hecompI (heI n)] at hle
    have hvmap := integral_map (μ := μ.prod μ) hV.measurable.aemeasurable (hemeas n).aestronglyMeasurable
    rw [hV.map_eq] at hvmap
    rw [← hvmap] at hle
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using helim.const_mul 2)
    (fun n => integral_nonneg (fun p => norm_nonneg _)) hupper

end
end Paper14
