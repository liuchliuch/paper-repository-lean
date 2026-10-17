import Paper32.Avoidance
import Mathlib.Probability.ConditionalExpectation

open MeasureTheory ProbabilityTheory Set Filter
open scoped MeasureTheory ENNReal

namespace Paper32

/-- The weaker direct conditional-hit assumption from Remark 4.3 yields one-step
avoidance by disintegration of the actual next-state conditional law. -/
theorem ae_avoidance_of_condDistrib_null
    {Ω History : Type*} [MeasurableSpace Ω] [MeasurableSpace History]
    (μ : Measure Ω) [IsFiniteMeasure μ] (H : Ω → History) (X : Ω → ℝ × ℝ)
    (hH : Measurable H) (hX : Measurable X)
    (hnull : ∀ᵐ ω ∂μ, condDistrib X H μ (H ω) singularArrangement = 0) :
    ∀ᵐ ω ∂μ, X ω ∉ singularArrangement := by
  have hmap : ∀ᵐ h ∂μ.map H, condDistrib X H μ h singularArrangement = 0 := by
    exact (ae_map_iff hH.aemeasurable ((measurableSet_singleton (0 : ℝ≥0∞)).preimage
      (Kernel.measurable_coe _ measurableSet_singularArrangement))).mpr hnull
  have hfiber : ∀ᵐ h ∂μ.map H, ∀ᵐ u ∂condDistrib X H μ h, u ∉ singularArrangement := by
    filter_upwards [hmap] with h hh
    exact measure_eq_zero_iff_ae_notMem.mp hh
  have hjoint : ∀ᵐ p ∂(μ.map H ⊗ₘ condDistrib X H μ), p.2 ∉ singularArrangement :=
    Measure.ae_compProd_of_ae_ae (measurableSet_singularArrangement.preimage measurable_snd).compl hfiber
  rw [compProd_map_condDistrib hX.aemeasurable] at hjoint
  exact (ae_map_iff (hH.prodMk hX).aemeasurable
    (measurableSet_singularArrangement.preimage measurable_snd).compl).mp hjoint

/-- The full countable direct conditional-hit version of Remark 4.3. -/
theorem ae_forall_positive_avoidance_of_conditional_hit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ k, m k ≤ mΩ)
    (z : ℕ → Ω → ℝ × ℝ) (hz : ∀ k, Measurable (z k))
    (hnull : ∀ k, ∀ᵐ ω ∂μ,
      condDistrib (z (k+1)) (preNoiseObservation (m k)) μ
        (preNoiseObservation (m k) ω) singularArrangement = 0) :
    ∀ᵐ ω ∂μ, ∀ k ≥ 1, z k ω ∉ singularArrangement := by
  have hk (k : ℕ) : ∀ᵐ ω ∂μ, z (k+1) ω ∉ singularArrangement :=
    ae_avoidance_of_condDistrib_null μ (preNoiseObservation (m k)) (z (k+1))
      (measurable_preNoiseObservation (m k) (hm k)) (hz (k+1)) (hnull k)
  filter_upwards [ae_all_iff.mpr hk] with ω hω
  intro k hpos
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hpos))
  exact hω j

/-- Uniform Euclidean-disk measure is invariant under reflection through the origin. -/
theorem uniformDiskLaw_preserving_neg (r : ℝ) :
    MeasurePreserving (fun u : ℝ × ℝ => -u) (uniformDiskLaw r) (uniformDiskLaw r) := by
  have hpre : (fun u : ℝ × ℝ => -u) ⁻¹' euclideanDisk r = euclideanDisk r := by
    ext u
    simp [euclideanDisk]
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) := by
    change Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure ℝ))
    infer_instance
  have hmap := Measure.map_addHaar_smul (volume : Measure (ℝ × ℝ))
    (r := (-1 : ℝ)) (by norm_num)
  have hneg : MeasurePreserving (fun u : ℝ × ℝ => -u) volume volume :=
    ⟨measurable_neg, by simpa [abs_pow] using hmap⟩
  have h := hneg.restrict_preimage (measurableSet_euclideanDisk r)
  rw [hpre] at h
  exact h.smul_measure ((volume (euclideanDisk r))⁻¹)

/-- Centering of the actual uniform disk measure, derived from its reflection symmetry. -/
theorem uniformDiskLaw_integral_id_zero (r : ℝ) :
    (∫ u : ℝ × ℝ, u ∂uniformDiskLaw r) = 0 := by
  have hmap := (uniformDiskLaw_preserving_neg r).map_eq
  have h := integral_map (μ := uniformDiskLaw r) measurable_neg.aemeasurable
    (f := fun u : ℝ × ℝ => u) measurable_id.aestronglyMeasurable
  rw [hmap, integral_neg] at h
  have hzero : (2 : ℝ) • (∫ u : ℝ × ℝ, u ∂uniformDiskLaw r) = 0 := by
    simpa only [two_smul] using (eq_neg_iff_add_eq_zero.mp h)
  exact (smul_eq_zero.mp hzero).resolve_left (by norm_num)

/-- The fourth power of the Euclidean norm in the paper's Cartesian coordinates. -/
def euclideanFourth (u : ℝ × ℝ) : ℝ := (u.1 ^ 2 + u.2 ^ 2) ^ 2

theorem euclideanFourth_nonneg (u : ℝ × ℝ) : 0 ≤ euclideanFourth u := sq_nonneg _

theorem euclideanFourth_le_of_disk {r : ℝ} {u : ℝ × ℝ} (hu : u ∈ euclideanDisk r) :
    euclideanFourth u ≤ r ^ 4 := by
  have h := (sq_le_sq₀ (add_nonneg (sq_nonneg u.1) (sq_nonneg u.2)) (sq_nonneg r)).mpr hu
  calc
    euclideanFourth u ≤ (r ^ 2) ^ 2 := h
    _ = r ^ 4 := by ring

/-- Every actual uniform disk random variable is centered. -/
theorem integral_uniformDisk_noise_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (noise : Ω → ℝ × ℝ)
    (hnoise : Measurable noise) {r : ℝ}
    (huniform : pdf.IsUniform noise (euclideanDisk r) μ volume) :
    (∫ ω, noise ω ∂μ) = 0 := by
  have h := integral_map (μ := μ) hnoise.aemeasurable
    (f := fun u : ℝ × ℝ => u) measurable_id.aestronglyMeasurable
  change μ.map noise = uniformDiskLaw r at huniform
  rw [huniform, uniformDiskLaw_integral_id_zero] at h
  exact h.symm

/-- Independence from the pre-noise history gives the genuine martingale-difference
conditional expectation, not merely unconditional centering. -/
theorem condExp_uniformDisk_noise_zero
    {Ω History : Type*} [mΩ : MeasurableSpace Ω] [mH : MeasurableSpace History]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : Ω → History) (noise : Ω → ℝ × ℝ)
    (hH : Measurable H) (hnoise : Measurable noise) (hindep : IndepFun H noise μ)
    {r : ℝ} (huniform : pdf.IsUniform noise (euclideanDisk r) μ volume) :
    μ[noise | mH.comap H] =ᵐ[μ] fun _ => 0 := by
  have hn : StronglyMeasurable[(inferInstance : MeasurableSpace (ℝ × ℝ)).comap noise] noise :=
    (Measurable.of_comap_le le_rfl).stronglyMeasurable
  have hi := (IndepFun_iff_Indep H noise μ).mp hindep
  have h := condExp_indep_eq hnoise.comap_le hH.comap_le hn hi.symm
  simpa only [integral_uniformDisk_noise_zero μ noise hnoise huniform] using h

/-- Uniform disk perturbations have a bounded fourth Euclidean moment. -/
theorem integrable_euclideanFourth_uniformDisk_noise
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (noise : Ω → ℝ × ℝ) (hnoise : Measurable noise) {r : ℝ}
    (huniform : pdf.IsUniform noise (euclideanDisk r) μ volume) :
    Integrable (fun ω => euclideanFourth (noise ω)) μ := by
  have hmem : ∀ᵐ u ∂μ.map noise, u ∈ euclideanDisk r := by
    rw [huniform]
    exact ae_cond_mem (measurableSet_euclideanDisk r)
  apply (integrable_const (r ^ 4)).mono' (by
    have hf : Measurable (fun ω => euclideanFourth (noise ω)) := by unfold euclideanFourth; fun_prop
    exact hf.aestronglyMeasurable)
  filter_upwards [ae_of_ae_map hnoise.aemeasurable hmem] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (euclideanFourth_nonneg _)] using
    euclideanFourth_le_of_disk hω

/-- The conditional fourth-moment bound holds for any pre-noise sigma field;
independence is unnecessary for this bounded-support consequence. -/
theorem condExp_euclideanFourth_uniformDisk_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (noise : Ω → ℝ × ℝ) (hnoise : Measurable noise) {r : ℝ}
    (huniform : pdf.IsUniform noise (euclideanDisk r) μ volume)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    ∀ᵐ ω ∂μ, (μ[fun ω => euclideanFourth (noise ω) | m]) ω ≤ r ^ 4 := by
  letI : MeasurableSpace Ω := mΩ
  have hmem : ∀ᵐ u ∂μ.map noise, u ∈ euclideanDisk r := by
    rw [huniform]
    exact ae_cond_mem (measurableSet_euclideanDisk r)
  have hbound : (fun ω => euclideanFourth (noise ω)) ≤ᵐ[μ] fun _ => r ^ 4 := by
    filter_upwards [ae_of_ae_map hnoise.aemeasurable hmem] with ω hω
    exact euclideanFourth_le_of_disk hω
  have h := condExp_mono (m := m)
    (integrable_euclideanFourth_uniformDisk_noise μ noise hnoise huniform) (integrable_const _) hbound
  simpa only [condExp_const hm] using h

/-- Bounded disk support gives genuine vector integrability. -/
theorem integrable_uniformDisk_noise
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (noise : Ω → ℝ × ℝ) (hnoise : Measurable noise) {r : ℝ} (hr : 0 ≤ r)
    (huniform : pdf.IsUniform noise (euclideanDisk r) μ volume) : Integrable noise μ := by
  apply (integrable_const r).mono' hnoise.aestronglyMeasurable
  filter_upwards [ae_coordinate_bounds_of_uniformDisk μ noise hnoise hr huniform] with ω hω
  simpa only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] using hω

/-- Centering conditioned on the complete natural pre-noise history follows from
actual mutual independence and uniform disk laws. -/
theorem iid_uniformDisk_condExp_noise_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (noise : ℕ → Ω → ℝ × ℝ) (hnoise : ∀ k, Measurable (noise k))
    (hiid : iIndepFun noise μ) {r : ℝ}
    (huniform : ∀ k, pdf.IsUniform (noise k) (euclideanDisk r) μ volume) :
    ∀ k, μ[noise k | noisePastSigma noise k] =ᵐ[μ] fun _ => 0 := by
  intro k
  exact condExp_uniformDisk_noise_zero μ (noisePast noise k) (noise k)
    (measurable_noisePast noise hnoise k) (hnoise k)
    (indepFun_noisePast_current μ noise hnoise hiid k) (huniform k)

/-- The exact bounded conditional-moment content used for DDJ Assumption E3 at
radius `10⁻²`.  The constant choice `q(x)=1` is bounded on every bounded set. -/
theorem iid_small_uniformDisk_conditional_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (noise : ℕ → Ω → ℝ × ℝ) (hnoise : ∀ k, Measurable (noise k))
    (hiid : iIndepFun noise μ)
    (huniform : ∀ k, pdf.IsUniform (noise k) (euclideanDisk (1/100)) μ volume) :
    (∀ k, Integrable (noise k) μ) ∧
    (∀ k, μ[noise k | noisePastSigma noise k] =ᵐ[μ] fun _ => 0) ∧
    ∀ k, ∀ᵐ ω ∂μ,
      (μ[fun ω => euclideanFourth (noise k ω) | noisePastSigma noise k]) ω < 1 := by
  refine ⟨fun k => integrable_uniformDisk_noise μ (noise k) (hnoise k) (by norm_num) (huniform k),
    iid_uniformDisk_condExp_noise_zero μ noise hnoise hiid huniform, ?_⟩
  intro k
  have h := condExp_euclideanFourth_uniformDisk_le μ (noise k) (hnoise k) (huniform k)
    (noisePastSigma noise k) (measurable_noisePast noise hnoise k).comap_le
  filter_upwards [h] with ω hω
  exact lt_of_le_of_lt hω (by norm_num)

end Paper32
