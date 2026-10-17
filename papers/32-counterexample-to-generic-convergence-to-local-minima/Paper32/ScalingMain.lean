import Paper32.IidRecursion
import Paper32.Extensions
import Paper32.ScalingCalculus

/-! # Corollary 7.1 for the actual selected stochastic recursion

The singular arrangement is avoided using the original radius-R noise and the
actual steps `α/C`. The genuine Clarke scaling theorem then converts each
realized update to the already proved trapping recursion.
-/

open Set Filter Topology MeasureTheory ProbabilityTheory

namespace Paper32

/-- The scaled schedule satisfies the literal target-framework comparison, including c₁ ≤ c₂. -/
theorem scaled_powerStep_target_order {γ C : ℝ} (hγ : 0 ≤ γ) (hC : 0 < C) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ k : ℕ, c₁ * ((k : ℝ) + 1) ^ (-γ) ≤ powerStep γ k / C ∧
        powerStep γ k / C ≤ c₂ * ((k : ℝ) + 1) ^ (-γ) := by
  have hzero := scaled_powerStep_sandwich hγ hC 0
  refine ⟨(8 : ℝ) ^ (-γ) / C, 1 / C, hzero.1, ?_, ?_⟩
  · simpa [powerStep] using hzero.2.2.2
  · intro k
    exact (scaled_powerStep_sandwich hγ hC k).2.2

/-- The scaled objective retains the genuine criticality gap and its nonminimum. -/
theorem scaled_objective_properties {C : ℝ} (hC : 0 < C) {v : Point} (hv : U v) :
    (∀ z, 0 ≤ scaledObjective C z - lin (C • v) z) ∧
    Tendsto (fun z => scaledObjective C z - lin (C • v) z) (cocompact Point) atTop ∧
    (0 : Point) ∈ clarkeSubdiff (fun z => scaledObjective C z - lin (C • v) z) 0 ∧
    (0 : Point) ∉ limitingSubdiff (fun z => scaledObjective C z - lin (C • v) z) 0 ∧
    ¬ IsLocalMin (fun z => scaledObjective C z - lin (C • v) z) 0 := by
  have hg := criticality_gap hv
  have hs := criticality_gap_scale hC hg.1 hg.2.1
  exact ⟨scaledTilt_nonneg hC hv, scaledTilt_coercive hC hv,
    by simpa only [scaledObjective_tilt] using hs.1,
    by simpa only [scaledObjective_tilt] using hs.2,
    not_localMin_scaledTilt hC hv⟩

/-- A Borel Clarke selection for Fᵥ supplies a concrete Borel selection for the scaled tilt. -/
theorem scaled_selection {v : Point} (C : ℝ) (selection : Point → Point)
    (hs : Measurable selection)
    (hselection : ∀ x, selection x ∈ clarkeSubdiff (tilt v) x) :
    Measurable (fun x => C • selection x) ∧
    ∀ x, C • selection x ∈ clarkeSubdiff
      (fun q => scaledObjective C q - lin (C • v) q) x := by
  refine ⟨hs.const_smul C,?_⟩
  intro x
  simpa only [scaledObjective_tilt] using clarke_scale_mem C (hselection x)

/-- Scaling the true Clarke oracle, noise and step gives the exact original trap. -/
theorem pathwise_scaled_trapping {v : Point} {γ R C : ℝ} (hv : U v)
    (hγlo : (1 / 2 : ℝ) < γ) (hγhi : γ < 1) (hR : 0 < R) (hCbound : 100 * R ≤ C)
    (z W ν : ℕ → Point) (hinit : Dstar (z 0))
    (hW : ∀ k, W k ∈ clarkeSubdiff (fun q => scaledObjective C q - lin (C • v) q) (z k))
    (hν : ∀ k, |(ν k).1| ≤ R ∧ |(ν k).2| ≤ R)
    (hrec : ∀ k, z (k + 1) = z k - (powerStep γ k / C) • (W k + ν k))
    (havoid : ∀ k ≥ 1, z k ∉ singularArrangement) :
    (∀ k, |(z (k + 1)).1| ≤ (36 / 5) * powerStep γ k ∧
      |(z (k + 1)).2| ≤ (39 / 10) * powerStep γ k) ∧
    Tendsto z atTop (𝓝 0) := by
  have hC : 0 < C := (scaled_noise_radius hR hCbound).1
  apply pathwise_coercive_trapping hv hγlo hγhi z
    (fun k => C⁻¹ • W k) (fun k => C⁻¹ • ν k) hinit
  · intro k
    apply (clarke_scale_iff hC.ne').mp
    simpa only [scaledObjective_tilt] using hW k
  · intro k
    constructor
    · simpa only [Prod.smul_fst, smul_eq_mul, div_eq_mul_inv, mul_comm] using
        scaled_coordinate_noise hR hCbound (hν k).1
    · simpa only [Prod.smul_snd, smul_eq_mul, div_eq_mul_inv, mul_comm] using
        scaled_coordinate_noise hR hCbound (hν k).2
  · intro k
    rw [hrec k]
    exact scaled_vector_update (z k) (W k) (ν k) (powerStep γ k) C
  · exact havoid

/-- Corollary 7.1 with every stated quantifier: arbitrary finite R, every
allowed C and tilt, every Borel Clarke selection, and every basin initialization. -/
theorem iid_uniformDisk_scaled_selected_trapping_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {v : Point} {γ R C : ℝ} (hv : U v) (hγlo : (1 / 2 : ℝ) < γ) (hγhi : γ < 1)
    (hR : 0 < R) (hCbound : 100 * R ≤ C)
    (x0 : Point) (hx0 : Dstar x0) (selection : Point → Point)
    (hs : Measurable selection)
    (hselection : ∀ x, selection x ∈ clarkeSubdiff
      (fun q => scaledObjective C q - lin (C • v) q) x)
    (noise : ℕ → Ω → Point) (hnoise : ∀ k, Measurable (noise k))
    (hiid : iIndepFun noise μ)
    (huniform : ∀ k, pdf.IsUniform (noise k) (euclideanDisk R) μ volume) :
    let z := noisyRecursion x0 (fun k => powerStep γ k / C) selection noise
    (∀ᵐ ω ∂μ, (∀ k, |(z (k + 1) ω).1| ≤ (36 / 5) * powerStep γ k ∧
      |(z (k + 1) ω).2| ≤ (39 / 10) * powerStep γ k) ∧
      Tendsto (fun k => z k ω) atTop (𝓝 0)) ∧
    μ (boundedOrbitEvent z \ localMinLimitEvent
      (fun q => scaledObjective C q - lin (C • v) q) z) = 1 := by
  have hC : 0 < C := (scaled_noise_radius hR hCbound).1
  let z := noisyRecursion x0 (fun k => powerStep γ k / C) selection noise
  have havoid := iid_uniformDisk_selected_avoidance_ae μ x0
    (fun k => powerStep γ k / C) (fun k => div_ne_zero (powerStep_pos γ k).ne' hC.ne')
    selection hs noise hnoise hiid huniform
  have hνall := ae_forall_uniformDisk_coordinate_bounds μ noise hnoise hR.le huniform
  have hall : ∀ᵐ ω ∂μ, (∀ k, |(z (k + 1) ω).1| ≤ (36 / 5) * powerStep γ k ∧
      |(z (k + 1) ω).2| ≤ (39 / 10) * powerStep γ k) ∧
      Tendsto (fun k => z k ω) atTop (𝓝 0) := by
    filter_upwards [havoid,hνall] with ω hωavoid hων
    exact pathwise_scaled_trapping hv hγlo hγhi hR hCbound (fun k => z k ω)
      (fun k => selection (z k ω)) (fun k => noise k ω) hx0
      (fun k => hselection (z k ω)) hων (fun k => rfl) hωavoid
  exact ⟨hall,measure_bad_limit_eq_one μ (not_localMin_scaledTilt hC hv) (hall.mono fun _ h => h.2)⟩

/-- An explicit iid product probability space gives the scaled counterexample. -/
theorem canonical_iid_uniformDisk_scaled_selected_trapping
    {v : Point} {γ R C : ℝ} (hv : U v) (hγlo : (1 / 2 : ℝ) < γ) (hγhi : γ < 1)
    (hR : 0 < R) (hCbound : 100 * R ≤ C)
    (x0 : Point) (hx0 : Dstar x0) (selection : Point → Point)
    (hs : Measurable selection)
    (hselection : ∀ x, selection x ∈ clarkeSubdiff
      (fun q => scaledObjective C q - lin (C • v) q) x) :
    let μ := iidUniformDiskMeasure R hR
    let z := noisyRecursion x0 (fun k => powerStep γ k / C) selection
      (fun k (ω : ℕ → Point) => ω k)
    (∀ᵐ ω ∂μ, (∀ k, |(z (k + 1) ω).1| ≤ (36 / 5) * powerStep γ k ∧
      |(z (k + 1) ω).2| ≤ (39 / 10) * powerStep γ k) ∧
      Tendsto (fun k => z k ω) atTop (𝓝 0)) ∧
    μ (boundedOrbitEvent z \ localMinLimitEvent
      (fun q => scaledObjective C q - lin (C • v) q) z) = 1 := by
  letI := iidUniformDiskMeasure_isProbability R hR
  exact iid_uniformDisk_scaled_selected_trapping_ae (iidUniformDiskMeasure R hR)
    hv hγlo hγhi hR hCbound x0 hx0 selection hs hselection
    (fun k (ω : ℕ → Point) => ω k) (fun k => measurable_pi_apply k)
    (iidUniformDiskMeasure_independent R hR) (iidUniformDiskMeasure_uniform R hR)

end Paper32
