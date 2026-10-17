import Paper32.Main
import Mathlib.Probability.Independence.InfinitePi

/-!
# Fixed Borel selections and genuine iid uniform disk perturbations

The recursion is defined here, not supplied through an assumed adapted process.
Finite-past factorization proves pre-noise measurability from the Borel selection.
The canonical sample space is the infinite product of the actual uniform disk law.
-/

open Set Filter Topology MeasureTheory ProbabilityTheory

namespace Paper32

/-- The selected noisy-subgradient recursion from a deterministic initial point. -/
noncomputable def noisyRecursion {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x0 : E) (a : ℕ → ℝ) (selection : E → E) (noise : ℕ → Ω → E) : ℕ → Ω → E
  | 0, _ => x0
  | k + 1, ω => noisyRecursion x0 a selection noise k ω -
      a k • (selection (noisyRecursion x0 a selection noise k ω) + noise k ω)

/-- Deterministic evaluation of the state from a finite noise vector. -/
noncomputable def finitePastRecursion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x0 : E) (a : ℕ → ℝ) (selection : E → E) : (k : ℕ) → (Fin k → E) → E
  | 0, _ => x0
  | k + 1, u =>
      let x := finitePastRecursion x0 a selection k (fun i => u i.castSucc)
      x - a k • (selection x + u (Fin.last k))

theorem measurable_finitePastRecursion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (x0 : E) (a : ℕ → ℝ)
    (selection : E → E) (hs : Measurable selection) (k : ℕ) :
    Measurable (finitePastRecursion x0 a selection k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hr : Measurable (fun u : Fin (k + 1) → E => fun i : Fin k => u i.castSucc) := by
      fun_prop
    have hx := ih.comp hr
    exact hx.sub (((hs.comp hx).add (measurable_pi_apply (Fin.last k))).const_smul (a k))

theorem noisyRecursion_eq_finitePast {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x0 : E) (a : ℕ → ℝ) (selection : E → E) (noise : ℕ → Ω → E) (k : ℕ) (ω : Ω) :
    noisyRecursion x0 a selection noise k ω =
      finitePastRecursion x0 a selection k (noisePast noise k ω) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [noisyRecursion, finitePastRecursion, ih]
    rfl

/-- State measurability before sampling the current noise follows from the actual
recursion and the Borel selection; it is not a hypothesis. -/
theorem measurable_noisyRecursion_adapted {Ω E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (x0 : E) (a : ℕ → ℝ) (selection : E → E) (hs : Measurable selection) (noise : ℕ → Ω → E) (k : ℕ) :
    Measurable[noisePastSigma noise k] (noisyRecursion x0 a selection noise k) := by
  have hH : Measurable[noisePastSigma noise k] (noisePast noise k) :=
    Measurable.of_comap_le le_rfl
  have h := (measurable_finitePastRecursion x0 a selection hs k).comp hH
  convert h using 1
  funext ω
  exact noisyRecursion_eq_finitePast x0 a selection noise k ω

/-- Theorem 2.3 for any fixed Borel Clarke selection and an actual iid uniformly
distributed disk noise process. -/
theorem iid_uniformDisk_selected_trapping_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {v : Point} {γ : ℝ} (hv : U v) (hγlo : (1/2 : ℝ) < γ) (hγhi : γ < 1)
    (x0 : Point) (hx0 : Dstar x0) (selection : Point → Point)
    (hs : Measurable selection) (hselection : ∀ x, selection x ∈ clarkeSubdiff (tilt v) x)
    (noise : ℕ → Ω → Point) (hnoise : ∀ k, Measurable (noise k))
    (hiid : iIndepFun noise μ)
    (huniform : ∀ k, pdf.IsUniform (noise k) (euclideanDisk (1 / 100)) μ volume) :
    let z := noisyRecursion x0 (powerStep γ) selection noise
    (∀ᵐ ω ∂μ, (∀ k, |(z (k+1) ω).1| ≤ (36/5)*powerStep γ k ∧
      |(z (k+1) ω).2| ≤ (39/10)*powerStep γ k) ∧
      Tendsto (fun k => z k ω) atTop (𝓝 0)) ∧
    μ (boundedOrbitEvent z \ localMinLimitEvent (tilt v) z) = 1 := by
  let z := noisyRecursion x0 (powerStep γ) selection noise
  apply coercive_trapping_ae μ (noisePastSigma noise)
    (fun k => (measurable_noisePast noise hnoise k).comap_le)
    hv hγlo hγhi z (fun k ω => selection (z k ω)) noise
  · exact measurable_noisyRecursion_adapted x0 (powerStep γ) selection hs noise
  · intro k
    exact hs.comp (measurable_noisyRecursion_adapted x0 (powerStep γ) selection hs noise k)
  · exact hnoise
  · exact Eventually.of_forall (fun _ => hx0)
  · exact fun k => Eventually.of_forall (fun ω => hselection (z k ω))
  · intro k
    exact ae_coordinate_bounds_of_uniformDisk μ (noise k) (hnoise k) (by norm_num) (huniform k)
  · exact iid_uniformDisk_conditional_absolutelyContinuous μ noise hnoise hiid huniform
  · exact fun k => Eventually.of_forall (fun _ => rfl)

/-- The defined recursion under iid uniform disk noise avoids the singular
arrangement at every positive time. -/
theorem iid_uniformDisk_selected_avoidance_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x0 : Point) (a : ℕ → ℝ) (ha : ∀ k, a k ≠ 0)
    (selection : Point → Point) (hs : Measurable selection)
    (noise : ℕ → Ω → Point) (hnoise : ∀ k, Measurable (noise k))
    (hiid : iIndepFun noise μ) {r : ℝ}
    (huniform : ∀ k, pdf.IsUniform (noise k) (euclideanDisk r) μ volume) :
    ∀ᵐ ω ∂μ, ∀ k ≥ 1, noisyRecursion x0 a selection noise k ω ∉ singularArrangement := by
  apply ae_forall_positive_avoidance_adapted μ (noisePastSigma noise)
    (fun k => (measurable_noisePast noise hnoise k).comap_le)
    (noisyRecursion x0 a selection noise)
    (fun k ω => selection (noisyRecursion x0 a selection noise k ω)) noise a
  · exact measurable_noisyRecursion_adapted x0 a selection hs noise
  · intro k
    exact hs.comp (measurable_noisyRecursion_adapted x0 a selection hs noise k)
  · exact hnoise
  · exact ha
  · exact iid_uniformDisk_conditional_absolutelyContinuous μ noise hnoise hiid huniform
  · exact fun k => Eventually.of_forall (fun _ => rfl)

/-- The ordinary-gradient conclusion of Corollary 2.5, for every initial point of the
basin outside the singular arrangement.  Every finite-time selected value is the
unique ordinary gradient even though the limit is a nonminimum. -/
theorem iid_uniformDisk_selected_ordinaryGradient_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {v : Point} {γ : ℝ} (hv : U v) (hγlo : (1/2 : ℝ) < γ) (hγhi : γ < 1)
    (x0 : Point) (hx0 : Dstar x0) (hregular : x0 ∉ singularArrangement)
    (selection : Point → Point) (hs : Measurable selection)
    (hselection : ∀ x, selection x ∈ clarkeSubdiff (tilt v) x)
    (noise : ℕ → Ω → Point) (hnoise : ∀ k, Measurable (noise k))
    (hiid : iIndepFun noise μ)
    (huniform : ∀ k, pdf.IsUniform (noise k) (euclideanDisk (1 / 100)) μ volume) :
    let z := noisyRecursion x0 (powerStep γ) selection noise
    ∀ᵐ ω ∂μ, ∀ k,
      HasFDerivAt (tilt v) (linCLM (gradCore (z k ω) - v)) (z k ω) ∧
      selection (z k ω) = gradCore (z k ω) - v := by
  let z := noisyRecursion x0 (powerStep γ) selection noise
  have htrap := (iid_uniformDisk_selected_trapping_ae μ hv hγlo hγhi x0 hx0
    selection hs hselection noise hnoise hiid huniform).1
  have hav := iid_uniformDisk_selected_avoidance_ae μ x0 (powerStep γ)
    (fun k => ne_of_gt (powerStep_pos γ k)) selection hs noise hnoise hiid huniform
  filter_upwards [htrap, hav] with ω htrapω havω
  intro k
  have hnon : z k ω ∉ singularArrangement := by
    cases k with
    | zero => exact hregular
    | succ k => exact havω (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
  have hlocal : l1 (z k ω) < 4 := by
    cases k with
    | zero => change |x0.1| + |x0.2| < 4; linarith [hx0.1, hx0.2]
    | succ k =>
      have hb := htrapω.1 k
      have ha := powerStep_antitone (by linarith : 0 ≤ γ) (Nat.zero_le k)
      have hfirst := powerStep_initial_upper hγlo
      unfold l1
      nlinarith [hb.1, hb.2]
  have hx : (z k ω).1 ≠ 0 := fun h => hnon (Or.inl h)
  have hy : (z k ω).2 ≠ 0 := fun h => hnon (Or.inr (Or.inl h))
  have hb : |(z k ω).2| ≠ 2 * |(z k ω).1| := fun h => hnon (Or.inr (Or.inr h))
  refine ⟨hasFDerivAt_tilt hlocal hx hy hb, ?_⟩
  have hmem := hselection (z k ω)
  rw [clarke_tilt_off_singular hlocal hx hy hb] at hmem
  exact mem_singleton_iff.mp hmem

/-- Canonical iid sample space: the actual countable product of the normalized
Lebesgue restriction to the Euclidean disk. -/
noncomputable def iidUniformDiskMeasure (r : ℝ) (hr : 0 < r) : Measure (ℕ → Point) := by
  letI : IsProbabilityMeasure (uniformDiskLaw r) := uniformDiskLaw_isProbability hr
  exact Measure.infinitePi (fun _ : ℕ => uniformDiskLaw r)

theorem iidUniformDiskMeasure_isProbability (r : ℝ) (hr : 0 < r) :
    IsProbabilityMeasure (iidUniformDiskMeasure r hr) := by
  unfold iidUniformDiskMeasure
  infer_instance

theorem iidUniformDiskMeasure_independent (r : ℝ) (hr : 0 < r) :
    iIndepFun (fun k (ω : ℕ → Point) => ω k) (iidUniformDiskMeasure r hr) := by
  letI : IsProbabilityMeasure (uniformDiskLaw r) := uniformDiskLaw_isProbability hr
  unfold iidUniformDiskMeasure
  exact iIndepFun_infinitePi (fun _ => measurable_id)

theorem iidUniformDiskMeasure_uniform (r : ℝ) (hr : 0 < r) (k : ℕ) :
    pdf.IsUniform (fun ω : ℕ → Point => ω k) (euclideanDisk r)
      (iidUniformDiskMeasure r hr) volume := by
  letI : IsProbabilityMeasure (uniformDiskLaw r) := uniformDiskLaw_isProbability hr
  change (iidUniformDiskMeasure r hr).map (Function.eval k) = uniformDiskLaw r
  unfold iidUniformDiskMeasure
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => uniformDiskLaw r) k).map_eq

/-- An explicit stochastic counterexample on a fully constructed probability space.
No noise distribution, independence, or adaptedness conclusion is assumed. -/
theorem canonical_iid_uniformDisk_selected_trapping
    {v : Point} {γ : ℝ} (hv : U v) (hγlo : (1/2 : ℝ) < γ) (hγhi : γ < 1)
    (x0 : Point) (hx0 : Dstar x0) (selection : Point → Point)
    (hs : Measurable selection) (hselection : ∀ x, selection x ∈ clarkeSubdiff (tilt v) x) :
    let μ := iidUniformDiskMeasure (1/100) (by norm_num)
    let z := noisyRecursion x0 (powerStep γ) selection (fun k (ω : ℕ → Point) => ω k)
    (∀ᵐ ω ∂μ, (∀ k, |(z (k+1) ω).1| ≤ (36/5)*powerStep γ k ∧
      |(z (k+1) ω).2| ≤ (39/10)*powerStep γ k) ∧
      Tendsto (fun k => z k ω) atTop (𝓝 0)) ∧
    μ (boundedOrbitEvent z \ localMinLimitEvent (tilt v) z) = 1 := by
  let hr : (0 : ℝ) < 1/100 := by norm_num
  letI := iidUniformDiskMeasure_isProbability (1/100) hr
  exact iid_uniformDisk_selected_trapping_ae (iidUniformDiskMeasure (1/100) hr)
    hv hγlo hγhi x0 hx0 selection hs hselection (fun k (ω : ℕ → Point) => ω k)
    (fun k => measurable_pi_apply k) (iidUniformDiskMeasure_independent _ hr)
    (iidUniformDiskMeasure_uniform _ hr)

end Paper32
