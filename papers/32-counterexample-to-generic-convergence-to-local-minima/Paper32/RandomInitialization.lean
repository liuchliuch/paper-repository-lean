import Paper32.IidRecursion
import Paper32.TiltMeasure

open Set Filter Topology MeasureTheory ProbabilityTheory

namespace Paper32

/-- Joint measurability of a finite selected recursion in both the initial point
and all previously sampled noises. -/
theorem measurable_finitePastRecursion_joint
    (a : ℕ → ℝ) (selection : Point → Point) (hs : Measurable selection) (k : ℕ) :
    Measurable (fun p : Point × (Fin k → Point) => finitePastRecursion p.1 a selection k p.2) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    have hr : Measurable (fun p : Point × (Fin (k+1) → Point) =>
        (p.1, fun i : Fin k => p.2 i.castSucc)) := by fun_prop
    have hx := ih.comp hr
    exact hx.sub (((hs.comp hx).add
      ((measurable_pi_apply (Fin.last k)).comp measurable_snd)).const_smul (a k))

/-- The selected recursion when the first independent coordinate is the random
initialization and subsequent coordinates are the successive perturbations. -/
noncomputable def randomInitRecursion {Ω : Type*} (observations : ℕ → Ω → Point)
    (a : ℕ → ℝ) (selection : Point → Point) (k : ℕ) (ω : Ω) : Point :=
  noisyRecursion (observations 0 ω) a selection (fun j => observations (j+1)) k ω

theorem measurable_randomInitRecursion_adapted {Ω : Type*}
    (observations : ℕ → Ω → Point) (a : ℕ → ℝ)
    (selection : Point → Point) (hs : Measurable selection) (k : ℕ) :
    Measurable[noisePastSigma observations (k+1)]
      (randomInitRecursion observations a selection k) := by
  have hH : Measurable[noisePastSigma observations (k+1)] (noisePast observations (k+1)) :=
    Measurable.of_comap_le le_rfl
  have hp : Measurable (fun u : Fin (k+1) → Point =>
      (u ⟨0, Nat.zero_lt_succ k⟩, fun i : Fin k => u i.succ)) := by fun_prop
  have h := (measurable_finitePastRecursion_joint a selection hs k).comp (hp.comp hH)
  convert h using 1
  funext ω
  exact noisyRecursion_eq_finitePast (observations 0 ω) a selection
    (fun j => observations (j+1)) k ω

/-- The random-initialization version in Corollary 2.5, with genuine independence
of the initialization and every finite collection of current/past noises. -/
theorem random_uniform_initialization_selected_trapping_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {v : Point} {γ : ℝ} (hv : U v) (hγlo : (1/2 : ℝ) < γ) (hγhi : γ < 1)
    (selection : Point → Point) (hs : Measurable selection)
    (hselection : ∀ x, selection x ∈ clarkeSubdiff (tilt v) x)
    (observations : ℕ → Ω → Point) (hmeas : ∀ k, Measurable (observations k))
    (hindep : iIndepFun observations μ)
    (hinitlaw : pdf.IsUniform (observations 0) initialRectangle μ volume)
    (hnoiselaw : ∀ k, pdf.IsUniform (observations (k+1)) (euclideanDisk (1/100)) μ volume) :
    let z := randomInitRecursion observations (powerStep γ) selection
    (∀ᵐ ω ∂μ, (∀ k, |(z (k+1) ω).1| ≤ (36/5)*powerStep γ k ∧
      |(z (k+1) ω).2| ≤ (39/10)*powerStep γ k) ∧
      Tendsto (fun k => z k ω) atTop (𝓝 0)) ∧
    μ (boundedOrbitEvent z \ localMinLimitEvent (tilt v) z) = 1 := by
  let m := fun k => noisePastSigma observations (k+1)
  let z := randomInitRecursion observations (powerStep γ) selection
  have hm (k : ℕ) : m k ≤ ‹MeasurableSpace Ω› :=
    (measurable_noisePast observations hmeas (k+1)).comap_le
  apply coercive_trapping_ae μ m hm hv hγlo hγhi z
    (fun k ω => selection (z k ω)) (fun k => observations (k+1))
  · exact measurable_randomInitRecursion_adapted observations (powerStep γ) selection hs
  · intro k
    exact hs.comp (measurable_randomInitRecursion_adapted observations (powerStep γ) selection hs k)
  · exact fun k => hmeas (k+1)
  · have hmem : ∀ᵐ u ∂μ.map (observations 0), u ∈ initialRectangle := by
      rw [hinitlaw]
      exact ae_cond_mem (isOpen_Ioo.measurableSet.prod isOpen_Ioo.measurableSet)
    filter_upwards [ae_of_ae_map (hmeas 0).aemeasurable hmem] with ω hω
    exact (mem_initialRectangle _).mp hω
  · exact fun k => Eventually.of_forall (fun ω => hselection (z k ω))
  · intro k
    exact ae_coordinate_bounds_of_uniformDisk μ (observations (k+1)) (hmeas (k+1))
      (by norm_num) (hnoiselaw k)
  · intro k
    have hobs := measurable_preNoiseObservation (m k) (hm k)
    have hi := indepFun_preNoiseObservation_of_indep μ (noisePast observations (k+1))
      (observations (k+1)) (indepFun_noisePast_current μ observations hmeas hindep (k+1))
    have hcond := condDistrib_absolutelyContinuous_of_indep_uniformDisk μ
      (preNoiseObservation (m k)) (observations (k+1)) hobs (hmeas (k+1)) hi (hnoiselaw k)
    exact ae_of_ae_map hobs.aemeasurable hcond
  · exact fun k => Eventually.of_forall (fun _ => rfl)

/-- The actual independent-coordinate laws for a uniform initialization and uniform
disk noise, each expressed as a normalized Lebesgue restriction. -/
noncomputable def randomInitializationLaw : ℕ → Measure Point
  | 0 => ProbabilityTheory.cond volume initialRectangle
  | _+1 => uniformDiskLaw (1/100)

theorem randomInitializationLaw_isProbability (k : ℕ) :
    IsProbabilityMeasure (randomInitializationLaw k) := by
  cases k with
  | zero =>
    apply cond_isProbabilityMeasure_of_finite
    · rw [volume_initialRectangle]; norm_num
    · rw [volume_initialRectangle]; exact ENNReal.ofReal_ne_top
  | succ k => exact uniformDiskLaw_isProbability (by norm_num)

/-- A complete probability space realizing the paper's independent uniform basin
initialization and iid uniform disk perturbations. -/
noncomputable def randomInitializationMeasure : Measure (ℕ → Point) := by
  letI : ∀ k, IsProbabilityMeasure (randomInitializationLaw k) := randomInitializationLaw_isProbability
  exact Measure.infinitePi randomInitializationLaw

theorem randomInitializationMeasure_isProbability :
    IsProbabilityMeasure randomInitializationMeasure := by
  unfold randomInitializationMeasure
  infer_instance

theorem canonical_random_uniform_initialization_selected_trapping
    {v : Point} {γ : ℝ} (hv : U v) (hγlo : (1/2 : ℝ) < γ) (hγhi : γ < 1)
    (selection : Point → Point) (hs : Measurable selection)
    (hselection : ∀ x, selection x ∈ clarkeSubdiff (tilt v) x) :
    let z := randomInitRecursion (fun k (ω : ℕ → Point) => ω k) (powerStep γ) selection
    (∀ᵐ ω ∂randomInitializationMeasure,
      (∀ k, |(z (k+1) ω).1| ≤ (36/5)*powerStep γ k ∧
        |(z (k+1) ω).2| ≤ (39/10)*powerStep γ k) ∧
      Tendsto (fun k => z k ω) atTop (𝓝 0)) ∧
    randomInitializationMeasure (boundedOrbitEvent z \ localMinLimitEvent (tilt v) z) = 1 := by
  letI := randomInitializationMeasure_isProbability
  letI : ∀ k, IsProbabilityMeasure (randomInitializationLaw k) := randomInitializationLaw_isProbability
  apply random_uniform_initialization_selected_trapping_ae randomInitializationMeasure
    hv hγlo hγhi selection hs hselection (fun k (ω : ℕ → Point) => ω k)
    (fun k => measurable_pi_apply k)
  · unfold randomInitializationMeasure
    exact iIndepFun_infinitePi (fun _ => measurable_id)
  · change randomInitializationMeasure.map (Function.eval 0) = randomInitializationLaw 0
    unfold randomInitializationMeasure
    exact (measurePreserving_eval_infinitePi randomInitializationLaw 0).map_eq
  · intro k
    change randomInitializationMeasure.map (Function.eval (k+1)) = randomInitializationLaw (k+1)
    unfold randomInitializationMeasure
    exact (measurePreserving_eval_infinitePi randomInitializationLaw (k+1)).map_eq

end Paper32
