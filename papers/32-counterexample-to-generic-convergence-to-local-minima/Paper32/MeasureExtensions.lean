import Paper32.Avoidance

open MeasureTheory ProbabilityTheory Set Filter
open scoped MeasureTheory ENNReal

namespace Paper32

/-- Nullity is preserved by every invertible scalar affine update in a finite
dimensional real vector space equipped with its actual Haar/Lebesgue measure. -/
theorem addHaar_affine_preimage_null
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ρ : Measure E) [Measure.IsAddHaarMeasure ρ]
    (b : E) {a : ℝ} (ha : a ≠ 0) {s : Set E} (hs : ρ s = 0) :
    ρ ((fun u : E => b - a • u) ⁻¹' s) = 0 := by
  have hsmul : Measure.QuasiMeasurePreserving (fun u : E => (-a) • u) ρ ρ :=
    Measure.quasiMeasurePreserving_smul ρ (neg_ne_zero.mpr ha)
  have hadd := (measurePreserving_add_left ρ b).quasiMeasurePreserving
  convert (hadd.comp hsmul).preimage_null hs using 1;
    simp [Function.comp_def, sub_eq_add_neg, neg_smul]

/-- The conditional-noise argument applies to any actual measurable Lebesgue-null
set, including the extra-coordinate hyperplanes in the separable embedding. -/
theorem ae_affine_avoidance_nullSet_of_condDistrib
    {Ω History E : Type*} [MeasurableSpace Ω] [MeasurableSpace History]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ρ : Measure E) [Measure.IsAddHaarMeasure ρ]
    (s : Set E) (hs : MeasurableSet s) (hs0 : ρ s = 0)
    (H : Ω → History) (noise : Ω → E) (z w : History → E) (a : ℝ)
    (hH : Measurable H) (hnoise : Measurable noise)
    (hz : Measurable z) (hw : Measurable w) (ha : a ≠ 0)
    (hac : ∀ᵐ ω ∂μ, condDistrib noise H μ (H ω) ≪ ρ) :
    ∀ᵐ ω ∂μ, z (H ω) - a • (w (H ω) + noise ω) ∉ s := by
  have hm : Measurable (fun p : History × E => z p.1 - a • (w p.1 + p.2)) := by fun_prop
  have hmeas := Kernel.measurable_kernel_prodMk_left (κ := condDistrib noise H μ) (hs.preimage hm)
  have hnull : ∀ᵐ h ∂μ.map H,
      condDistrib noise H μ h ((fun u : E => z h - a • (w h + u)) ⁻¹' s) = 0 := by
    apply (ae_map_iff hH.aemeasurable ((measurableSet_singleton (0 : ℝ≥0∞)).preimage hmeas)).mpr
    filter_upwards [hac] with ω hω
    apply hω
    have heq : (fun u : E => z (H ω) - a • (w (H ω) + u)) =
        (fun u : E => (z (H ω) - a • w (H ω)) - a • u) := by
      funext u
      rw [smul_add, sub_add_eq_sub_sub]
    change ρ ((fun u : E => z (H ω) - a • (w (H ω) + u)) ⁻¹' s) = 0
    rw [heq]
    exact addHaar_affine_preimage_null ρ _ ha hs0
  have hfiber : ∀ᵐ h ∂μ.map H, ∀ᵐ u ∂condDistrib noise H μ h,
      z h - a • (w h + u) ∉ s := by
    filter_upwards [hnull] with h hh
    exact measure_eq_zero_iff_ae_notMem.mp hh
  have hjoint : ∀ᵐ p ∂(μ.map H ⊗ₘ condDistrib noise H μ),
      z p.1 - a • (w p.1 + p.2) ∉ s :=
    Measure.ae_compProd_of_ae_ae (hs.preimage hm).compl hfiber
  rw [compProd_map_condDistrib hnoise.aemeasurable] at hjoint
  exact (ae_map_iff (hH.prodMk hnoise).aemeasurable (hs.preimage hm).compl).mp hjoint

/-- Countable positive-time avoidance of a genuine null set for an adapted recursion
in arbitrary finite dimension. -/
theorem ae_forall_positive_avoidance_nullSet_adapted
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ρ : Measure E) [Measure.IsAddHaarMeasure ρ]
    (s : Set E) (hs : MeasurableSet s) (hs0 : ρ s = 0)
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ k, m k ≤ mΩ)
    (z w noise : ℕ → Ω → E) (a : ℕ → ℝ)
    (hz : ∀ k, Measurable[m k] (z k)) (hw : ∀ k, Measurable[m k] (w k))
    (hnoise : ∀ k, Measurable (noise k)) (ha : ∀ k, a k ≠ 0)
    (hac : ∀ k, ∀ᵐ ω ∂μ,
      condDistrib (noise k) (preNoiseObservation (m k)) μ
        (preNoiseObservation (m k) ω) ≪ ρ)
    (hrec : ∀ k, ∀ᵐ ω ∂μ, z (k + 1) ω = z k ω - a k • (w k ω + noise k ω)) :
    ∀ᵐ ω ∂μ, ∀ k ≥ 1, z k ω ∉ s := by
  have hk (k : ℕ) : ∀ᵐ ω ∂μ, z (k + 1) ω ∉ s := by
    have hv : @Measurable (PreNoiseView Ω (m k)) Ω _ (m k)
        PreNoiseView.outcome := Measurable.of_comap_le le_rfl
    have hav := ae_affine_avoidance_nullSet_of_condDistrib μ ρ s hs hs0
      (preNoiseObservation (m k)) (noise k)
      (z k ∘ PreNoiseView.outcome) (w k ∘ PreNoiseView.outcome) (a k)
      (measurable_preNoiseObservation (m k) (hm k)) (hnoise k)
      ((hz k).comp hv) ((hw k).comp hv) (ha k) (hac k)
    filter_upwards [hrec k, hav] with ω hr hω
    rwa [hr]
  filter_upwards [ae_all_iff.mpr hk] with ω hω
  intro k hpos
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hpos))
  exact hω j

/-- Full singular arrangement in the separable embedding: the planar arrangement
and the zero hyperplane of each extra coordinate. -/
def embeddedSingularArrangement (ι : Type*) : Set ((ℝ × ℝ) × (ι → ℝ)) :=
  {z | z.1 ∈ singularArrangement ∨ ∃ i, z.2 i = 0}

theorem measurableSet_embeddedSingularArrangement (ι : Type*) [Fintype ι] :
    MeasurableSet (embeddedSingularArrangement ι) := by
  have hcoord : MeasurableSet {z : (ℝ × ℝ) × (ι → ℝ) | ∃ i, z.2 i = 0} := by
    simp only [show {z : (ℝ × ℝ) × (ι → ℝ) | ∃ i, z.2 i = 0} =
      ⋃ i, {z | z.2 i = 0} by ext; simp]
    apply MeasurableSet.iUnion
    intro i
    exact measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_snd) measurable_const
  exact (measurableSet_singularArrangement.preimage measurable_fst).union hcoord

theorem volume_embeddedCoordinateHyperplane (ι : Type*) [Fintype ι] (i : ι) :
    (volume : Measure ((ℝ × ℝ) × (ι → ℝ))) {z | z.2 i = 0} = 0 := by
  change ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ι → ℝ))) {z | z.2 i = 0} = 0
  apply (Measure.measure_prod_null
    (measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_snd) measurable_const)).mpr
  filter_upwards [] with x
  exact Measure.pi_eval_preimage_null (fun _ : ι => (volume : Measure ℝ)) (measure_singleton (0 : ℝ))

theorem volume_embeddedSingularArrangement (ι : Type*) [Fintype ι] :
    (volume : Measure ((ℝ × ℝ) × (ι → ℝ))) (embeddedSingularArrangement ι) = 0 := by
  have hfirst : (volume : Measure ((ℝ × ℝ) × (ι → ℝ)))
      {z | z.1 ∈ singularArrangement} = 0 := by
    change ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ι → ℝ)))
      (Prod.fst ⁻¹' singularArrangement) = 0
    rw [show (Prod.fst : (ℝ × ℝ) × (ι → ℝ) → ℝ × ℝ) ⁻¹' singularArrangement =
      singularArrangement ×ˢ univ by ext; simp]
    apply le_antisymm _ (zero_le _)
    simpa only [volume_singularArrangement, zero_mul] using
      (Measure.prod_prod_le (μ := (volume : Measure (ℝ × ℝ)))
        (ν := (volume : Measure (ι → ℝ))) singularArrangement univ)
  have hrest : (volume : Measure ((ℝ × ℝ) × (ι → ℝ)))
      {z | ∃ i, z.2 i = 0} = 0 := by
    rw [show {z : (ℝ × ℝ) × (ι → ℝ) | ∃ i, z.2 i = 0} =
      ⋃ i, {z | z.2 i = 0} by ext; simp]
    exact measure_iUnion_null_iff.mpr (volume_embeddedCoordinateHyperplane ι)
  exact measure_union_null hfirst hrest

/-- The exact full-dimensional avoidance event required by Corollary 7.2. -/
theorem ae_forall_positive_embedded_avoidance_adapted
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ k, m k ≤ mΩ)
    (z w noise : ℕ → Ω → (ℝ × ℝ) × (ι → ℝ)) (a : ℕ → ℝ)
    (hz : ∀ k, Measurable[m k] (z k)) (hw : ∀ k, Measurable[m k] (w k))
    (hnoise : ∀ k, Measurable (noise k)) (ha : ∀ k, a k ≠ 0)
    (hac : ∀ k, ∀ᵐ ω ∂μ,
      condDistrib (noise k) (preNoiseObservation (m k)) μ
        (preNoiseObservation (m k) ω) ≪ (volume : Measure ((ℝ × ℝ) × (ι → ℝ))))
    (hrec : ∀ k, ∀ᵐ ω ∂μ, z (k + 1) ω = z k ω - a k • (w k ω + noise k ω)) :
    ∀ᵐ ω ∂μ, ∀ k ≥ 1, (z k ω).1 ∉ singularArrangement ∧ ∀ i, (z k ω).2 i ≠ 0 := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) := by
    change Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure ℝ))
    infer_instance
  letI : Measure.IsAddHaarMeasure (volume : Measure ((ℝ × ℝ) × (ι → ℝ))) := by
    change Measure.IsAddHaarMeasure
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ι → ℝ)))
    infer_instance
  have hav := ae_forall_positive_avoidance_nullSet_adapted μ volume
    (embeddedSingularArrangement ι) (measurableSet_embeddedSingularArrangement ι)
    (volume_embeddedSingularArrangement ι) m hm z w noise a hz hw hnoise ha hac hrec
  filter_upwards [hav] with ω hω
  intro k hk
  simpa only [embeddedSingularArrangement, mem_setOf_eq, not_or, not_exists] using hω k hk

/-- Actual iid uniform perturbations in any standard Borel space have an absolutely
continuous conditional law given the complete natural finite past.  The support set
may be the full-dimensional Euclidean ball; no coordinate independence is assumed. -/
theorem iid_uniform_conditional_absolutelyContinuous
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [StandardBorelSpace E] [Nonempty E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ρ : Measure E)
    (noise : ℕ → Ω → E) (hnoise : ∀ k, Measurable (noise k))
    (hiid : iIndepFun noise μ) (s : Set E)
    (huniform : ∀ k, pdf.IsUniform (noise k) s μ ρ) :
    ∀ k, ∀ᵐ ω ∂μ,
      condDistrib (noise k) (preNoiseObservation (noisePastSigma noise k)) μ
        (preNoiseObservation (noisePastSigma noise k) ω) ≪ ρ := by
  intro k
  have hobs := measurable_preNoiseObservation (noisePastSigma noise k)
    (measurable_noisePast noise hnoise k).comap_le
  have hi := indepFun_preNoiseObservation_of_indep μ (noisePast noise k) (noise k)
    (indepFun_noisePast_current μ noise hnoise hiid k)
  have hcond : ∀ᵐ h ∂μ.map (preNoiseObservation (noisePastSigma noise k)),
      condDistrib (noise k) (preNoiseObservation (noisePastSigma noise k)) μ h ≪ ρ := by
    filter_upwards [condDistrib_ae_eq_const_of_indep μ
      (preNoiseObservation (noisePastSigma noise k)) (noise k) hobs (hnoise k) hi] with h hh
    simpa only [hh, Kernel.const_apply] using (huniform k).absolutelyContinuous
  exact ae_of_ae_map hobs.aemeasurable hcond

/-- The closed Euclidean ball in the paper's separable coordinates.  The displayed
sum of squares is the genuine Euclidean radius, independently of the product norm. -/
def embeddedEuclideanBall (ι : Type*) [Fintype ι] (r : ℝ) : Set ((ℝ × ℝ) × (ι → ℝ)) :=
  {z | z.1.1 ^ 2 + z.1.2 ^ 2 + ∑ i, z.2 i ^ 2 ≤ r ^ 2}

theorem measurableSet_embeddedEuclideanBall (ι : Type*) [Fintype ι] (r : ℝ) :
    MeasurableSet (embeddedEuclideanBall ι r) := by
  exact (isClosed_le (by fun_prop) continuous_const).measurableSet

theorem embeddedEuclideanBall_coordinate_bounds {ι : Type*} [Fintype ι]
    {r : ℝ} (hr : 0 ≤ r) {z : (ℝ × ℝ) × (ι → ℝ)} (hz : z ∈ embeddedEuclideanBall ι r) :
    (|z.1.1| ≤ r ∧ |z.1.2| ≤ r) ∧ ∀ i, |z.2 i| ≤ r := by
  have hsum : 0 ≤ ∑ i, z.2 i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbound (x : ℝ) (hx : x ^ 2 ≤ r ^ 2) : |x| ≤ r := by
    apply (sq_le_sq₀ (abs_nonneg x) hr).mp
    simpa only [sq_abs] using hx
  refine ⟨⟨hbound _ ?_, hbound _ ?_⟩, ?_⟩
  · change z.1.1 ^ 2 + z.1.2 ^ 2 + ∑ i, z.2 i ^ 2 ≤ r ^ 2 at hz
    linarith [sq_nonneg z.1.2]
  · change z.1.1 ^ 2 + z.1.2 ^ 2 + ∑ i, z.2 i ^ 2 ≤ r ^ 2 at hz
    linarith [sq_nonneg z.1.1]
  · intro i
    apply hbound
    have hi : z.2 i ^ 2 ≤ ∑ j, z.2 j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (z.2 j)) (Finset.mem_univ i)
    change z.1.1 ^ 2 + z.1.2 ^ 2 + ∑ i, z.2 i ^ 2 ≤ r ^ 2 at hz
    linarith [sq_nonneg z.1.1, sq_nonneg z.1.2]

/-- Actual uniform full-dimensional Euclidean-ball noise has all coordinate support
bounds used by the embedded dynamics. -/
theorem ae_coordinate_bounds_of_uniform_embeddedEuclideanBall
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (noise : Ω → (ℝ × ℝ) × (ι → ℝ)) (hnoise : Measurable noise)
    {r : ℝ} (hr : 0 ≤ r)
    (huniform : pdf.IsUniform noise (embeddedEuclideanBall ι r) μ volume) :
    ∀ᵐ ω ∂μ, (|(noise ω).1.1| ≤ r ∧ |(noise ω).1.2| ≤ r) ∧
      ∀ i, |(noise ω).2 i| ≤ r := by
  have hmem : ∀ᵐ u ∂μ.map noise, u ∈ embeddedEuclideanBall ι r := by
    rw [huniform]
    exact ae_cond_mem (measurableSet_embeddedEuclideanBall ι r)
  filter_upwards [ae_of_ae_map hnoise.aemeasurable hmem] with ω hω
  exact embeddedEuclideanBall_coordinate_bounds hr hω

end Paper32
