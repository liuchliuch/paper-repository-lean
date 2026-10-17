import Paper36.Measurability

/-! Borel planning selectors, actual Algorithm 1 measurability, and the reward
comparator. Existence of Borel selectors can be instantiated from the published
measurable maximum and compact-section selection theorems. Only that external
selection ingredient is an input; the algorithm's measurability below is proved. -/
namespace Paper36.BorelAlgorithm
open MeasureTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
noncomputable section
variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A] [MeasurableSpace Ω]

/-- The exact Borel selectors required by the source's oracle protocol. -/
structure BorelOracles (α : ℝ) (c r : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (τ : ℝ) (Q : Set (Kernel S A)) extends Oracles α c r H s₁ τ Q where
  measurable_calibration : Measurable calibration
  measurable_exploitation : Measurable exploitation

lemma measurable_deposits (α τ : ℝ) (c : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (sample : ℕ → Ω → Kernel S A) (hsample : ∀ n, Measurable (sample n)) (n : ℕ) :
    Measurable (deposits α τ c H s₁ sample n) := by
  cases n with
  | zero => exact measurable_const
  | succ n =>
    exact measurable_const.sub ((continuous_minimumRisk α c H 0 s₁).measurable.comp (hsample n))

/-- Both the threshold decision and the selected physical-state Markov policy are measurable. -/
theorem measurable_selected {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelOracles α c r H s₁ τ Q)
    (T : ℕ → ℝ) (sample : ℕ → Ω → Kernel S A) (hsample : ∀ n, Measurable (sample n))
    (n : ℕ) : Measurable (fun ω => selected O.toOracles T sample n ω) := by
  have hd := measurable_deposits α τ c H s₁ sample hsample
  have hset : MeasurableSet {ω | Bank.calibrates T (fun j => deposits α τ c H s₁ sample j ω) n} :=
    measurableSet_lt (Assembly.measurable_bank T _ hd n) measurable_const
  exact Measurable.ite hset (O.measurable_calibration.comp (hsample n))
    (O.measurable_exploitation.comp (hsample n))

/-- A Borel version of the exact constrained value, equal to (2.5) on its entire model support. -/
def comparator {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelOracles α c r H s₁ τ Q) (q : Kernel S A) : ℝ :=
  reward r (O.exploitation q) q H 0 s₁

local instance policyKernel_opens : OpensMeasurableSpace (Policy S A × Kernel S A) :=
  @Prod.opensMeasurableSpace _ _ _ _ _ _ inferInstance inferInstance inferInstance

lemma measurable_comparator {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelOracles α c r H s₁ τ Q) :
    Measurable (comparator O) :=
  (continuous_reward r H 0 s₁).measurable.comp (O.measurable_exploitation.prodMk measurable_id)

lemma comparator_eq_source {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelOracles α c r H s₁ τ Q)
    {q : Kernel S A} (hq : q ∈ Q) :
    comparator O q = constrainedValue α c r H s₁ τ q :=
  (constrainedValue_eq O.toOracles hq).symm

lemma comparator_bounds {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelOracles α c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (q : Kernel S A) :
    comparator O q ∈ Set.Icc 0 (H : ℝ) := reward_bounds r hr (O.exploitation q) q H 0 s₁

/-- The exact comparator is integrable for every prior/learner probability space. -/
lemma integrable_comparator (μ : Measure Ω) [IsFiniteMeasure μ]
    {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelOracles α c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (p : Ω → Kernel S A) (hp : Measurable p) : Integrable (fun ω => comparator O (p ω)) μ := by
  apply Integrable.of_bound ((measurable_comparator O).comp hp).aestronglyMeasurable H
  apply ae_of_all
  intro ω
  have hb := comparator_bounds O hr (p ω)
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

end
end Paper36.BorelAlgorithm
