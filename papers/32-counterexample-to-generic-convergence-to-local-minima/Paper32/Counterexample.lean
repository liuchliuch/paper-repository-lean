import Paper32.IidRecursion
import Paper32.BorelSelection
import Paper32.SelectionAlgebraic
import Paper32.TiltMeasure
import Paper32.FunctionClass

/-! # The actual fixed-selection and conull-set counterexamples

The test defining `CanonicalGoodTilt` is a necessary part of the source's
universal target: it retains every Borel selection, deterministic initial point,
finite noise radius and admissible step sequence, and uses the explicit iid
product probability space. Refuting even this necessary test refutes the target.
-/
open Set Filter Topology MeasureTheory ProbabilityTheory
namespace Paper32

/-- The deterministic differentiability-point initialization in Corollary 2.3. -/
noncomputable def sourceInitial : Point := (1/160,1/100)

lemma sourceInitial_basin : Dstar sourceInitial := by norm_num [Dstar,sourceInitial]
lemma sourceInitial_regular : sourceInitial ∉ singularArrangement := by
  norm_num [sourceInitial,singularArrangement]

/-- The power-law admissibility condition with exactly the quantifiers in Target 2.1. -/
def AdmissiblePowerSteps (a : ℕ → ℝ) : Prop :=
  (∀ k, 0 < a k) ∧ ∃ c₁ c₂ γ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
    (1/2:ℝ) < γ ∧ γ < 1 ∧ ∀ k : ℕ,
      c₁*((k:ℝ)+1)^(-γ) ≤ a k ∧ a k ≤ c₂*((k:ℝ)+1)^(-γ)

lemma powerStep_admissible {γ : ℝ} (hγlo : (1/2:ℝ) < γ) (hγhi : γ < 1) :
    AdmissiblePowerSteps (powerStep γ) := by
  have hγ : 0 ≤ γ := by linarith
  refine ⟨powerStep_pos γ, (8:ℝ)^(-γ),1,γ,Real.rpow_pos_of_pos (by norm_num) _,?_,
    hγlo,hγhi,?_⟩
  · have h := powerStep_upper hγ 0
    simpa [powerStep] using h
  · intro k
    exact ⟨powerStep_lower hγ k,by simpa using powerStep_upper hγ k⟩

lemma probability_one_of_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {P : Ω → Prop} (hP : ∀ᵐ ω ∂μ, P ω) : μ {ω | P ω}=1 := by
  have h : {ω | P ω} =ᵐ[μ] univ := hP.mono fun _ h => propext (iff_true_intro h)
  rw [measure_congr h,measure_univ]

/-- Corollary 2.3 for the actual minimum-Euclidean-norm Borel selection.
The probability space and the iid disk perturbations are supplied as actual laws. -/
theorem minimumNorm_fixed_counterexample
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {v : Point} {γ : ℝ} (hv : U v) (hγlo : (1/2:ℝ) < γ) (hγhi : γ < 1)
    (noise : ℕ → Ω → Point) (hnoise : ∀ k, Measurable (noise k))
    (hiid : iIndepFun noise μ)
    (huniform : ∀ k, pdf.IsUniform (noise k) (euclideanDisk (1/100)) μ volume) :
    let z := noisyRecursion sourceInitial (powerStep γ) (minimumNormSelection v) noise
    μ {ω | Tendsto (fun k => z k ω) atTop (𝓝 0)}=1 ∧
    μ (boundedOrbitEvent z \ localMinLimitEvent (tilt v) z)=1 ∧
    ¬ IsLocalMin (tilt v) 0 := by
  have h := iid_uniformDisk_selected_trapping_ae μ hv hγlo hγhi sourceInitial
    sourceInitial_basin (minimumNormSelection v) (measurable_minimumNormSelection v)
    (minimumNormSelection_mem v) noise hnoise hiid huniform
  exact ⟨probability_one_of_ae μ (h.1.mono fun _ h => h.2),h.2,not_localMin_tilt hv⟩

/-- Remark 2.4 for the displayed differentiability-point initialization. -/
theorem minimumNorm_ordinaryGradient_counterexample
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {v : Point} {γ : ℝ} (hv : U v) (hγlo : (1/2:ℝ) < γ) (hγhi : γ < 1)
    (selection : Point → Point) (hs : Measurable selection)
    (hselection : ∀ x, selection x ∈ clarkeSubdiff (tilt v) x)
    (noise : ℕ → Ω → Point) (hnoise : ∀ k, Measurable (noise k))
    (hiid : iIndepFun noise μ)
    (huniform : ∀ k, pdf.IsUniform (noise k) (euclideanDisk (1/100)) μ volume) :
    let z := noisyRecursion sourceInitial (powerStep γ) selection noise
    ∀ᵐ ω ∂μ, ∀ k, HasFDerivAt (tilt v) (linCLM (gradCore (z k ω)-v)) (z k ω) ∧
      selection (z k ω)=gradCore (z k ω)-v :=
  iid_uniformDisk_selected_ordinaryGradient_ae μ hv hγlo hγhi sourceInitial sourceInitial_basin
    sourceInitial_regular selection hs hselection noise hnoise hiid huniform

/-- A necessary universal good-tilt test from Target 2.1, on a constructed iid
probability space. No choices here may depend on an allegedly conull good set. -/
def CanonicalGoodTilt (v : Point) : Prop :=
  ∀ (selection : Point → Point), Measurable selection →
    (∀ x, selection x ∈ clarkeSubdiff (tilt v) x) →
    ∀ (x0 : Point) (r : ℝ) (hr : 0 < r) (a : ℕ → ℝ), AdmissiblePowerSteps a →
      let μ := iidUniformDiskMeasure r hr
      let z := noisyRecursion x0 a selection (fun k (ω : ℕ → Point) => ω k)
      μ (boundedOrbitEvent z \ localMinLimitEvent (tilt v) z)=0

/-- The universal stochastic target specialized to the original F in dimension two.
Every probability space, Borel Clarke selection, deterministic initialization,
noise radius and positive power-comparable deterministic schedule is quantified. -/
def UniversalGoodTilt (v : Point) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
    ∀ (selection : Point → Point), Measurable selection →
      (∀ x, selection x ∈ clarkeSubdiff (tilt v) x) →
      ∀ (x0 : Point) (r : ℝ), 0 < r → ∀ (a : ℕ → ℝ), AdmissiblePowerSteps a →
        ∀ (noise : ℕ → Ω → Point), (∀ k, Measurable (noise k)) → iIndepFun noise μ →
          (∀ k, pdf.IsUniform (noise k) (euclideanDisk r) μ volume) →
          let z := noisyRecursion x0 a selection noise
          μ (boundedOrbitEvent z \ localMinLimitEvent (tilt v) z)=0

lemma universalGoodTilt_implies_canonical {v : Point} (hv : UniversalGoodTilt v) :
    CanonicalGoodTilt v := by
  intro selection hs hselection x0 r hr a ha
  letI := iidUniformDiskMeasure_isProbability r hr
  exact hv (ℕ → Point) (iidUniformDiskMeasure r hr) selection hs hselection x0 r hr a ha
    (fun k (ω : ℕ → Point) => ω k) (fun k => measurable_pi_apply k)
    (iidUniformDiskMeasure_independent r hr) (iidUniformDiskMeasure_uniform r hr)

/-- Every tilt in the literal nonempty open square fails the universal target. -/
theorem bad_on_entire_tiltSquare {v : Point} (hv : v ∈ tiltSquare) : ¬ CanonicalGoodTilt v := by
  intro hgood
  have hu : U v := (mem_tiltSquare v).mp hv
  have htrap := canonical_iid_uniformDisk_selected_trapping (γ := (3/4:ℝ)) hu
    (by norm_num) (by norm_num) sourceInitial sourceInitial_basin (minimumNormSelection v)
    (measurable_minimumNormSelection v) (minimumNormSelection_mem v)
  have hzero := hgood (minimumNormSelection v) (measurable_minimumNormSelection v)
    (minimumNormSelection_mem v) sourceInitial (1/100) (by norm_num) (powerStep (3/4))
    (powerStep_admissible (by norm_num) (by norm_num))
  have hone := htrap.2
  rw [hzero] at hone
  norm_num at hone

/-- Corollary 2.5: even the canonical iid test admits no conull good-tilt set. -/
theorem no_conull_good_tilt_set :
    ¬ ∃ G : Set Point, volume Gᶜ=0 ∧ ∀ v ∈ G, CanonicalGoodTilt v :=
  no_conull_set_of_bad_square (fun _ hv => bad_on_entire_tiltSquare hv)

/-- Literal failure of Target 2.1 for F, with all algorithmic quantifiers retained. -/
theorem no_conull_universal_good_tilt_set :
    ¬ ∃ G : Set Point, volume Gᶜ=0 ∧ ∀ v ∈ G, UniversalGoodTilt v := by
  rintro ⟨G,hG,hgood⟩
  exact no_conull_good_tilt_set ⟨G,hG,fun v hv => universalGoodTilt_implies_canonical (hgood v hv)⟩

/-- The source's required objective class is satisfied by the same actual F. -/
theorem counterexample_objective_class :
    (∀ z, 0 ≤ F z) ∧ Tendsto F (cocompact Point) atTop ∧
    LipschitzWith 8 F ∧ SemialgebraicFunction F ∧ ContinuousPiecewiseAffine F :=
  ⟨F_nonneg,F_coercive,lipschitz_F,semialgebraic_F,continuousPiecewiseAffine_F⟩

end Paper32
