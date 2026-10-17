import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Paper36.RiskBridge
import Paper36.Algorithm
import Paper36.Assembly

/-! Entrywise measurability of actual finite-policy/kernel values. These lemmas
remove value-measurability premises from the arbitrary-prior statistical layer;
they do not assume any confidence event or any cumulative simulation bound. -/
namespace Paper36.Measurability
open MeasureTheory Paper36
noncomputable section
variable {S A Ω : Type*} [Fintype S] [Fintype A] [MeasurableSpace Ω]

local instance policyKernel_opens : OpensMeasurableSpace (Nested.Policy S A × Nested.Kernel S A) :=
  @Prod.opensMeasurableSpace _ _ _ _ _ _ inferInstance inferInstance inferInstance

def regularPolicy (π : Simulation.Policy S A) : Nested.Policy S A :=
  fun h s => RiskBridge.toRegular (π h s)

def regularKernel (p : Simulation.Kernel S A) : Nested.Kernel S A :=
  fun s a => RiskBridge.toRegular (p s a)

lemma measurable_regularPolicy (π : Ω → Simulation.Policy S A)
    (hπ : ∀ h s a, Measurable (fun ω => (π ω h s).mass a)) :
    Measurable (fun ω => regularPolicy (π ω)) := by
  apply measurable_pi_lambda
  intro h
  apply measurable_pi_lambda
  intro s
  apply Measurable.subtype_mk
  exact measurable_pi_lambda _ (fun a => hπ h s a)

lemma measurable_regularKernel (p : Ω → Simulation.Kernel S A)
    (hp : ∀ s a t, Measurable (fun ω => (p ω s a).mass t)) :
    Measurable (fun ω => regularKernel (p ω)) := by
  apply measurable_pi_lambda
  intro s
  apply measurable_pi_lambda
  intro a
  apply Measurable.subtype_mk
  exact measurable_pi_lambda _ (fun t => hp s a t)

lemma of_regularPolicy (π : Simulation.Policy S A) :
    RiskBridge.ofPolicy (regularPolicy π) = π := by
  funext h s
  change RiskBridge.ofRegular (RiskBridge.toRegular (π h s)) = π h s
  exact RiskBridge.lawEquiv.left_inv _

lemma of_regularKernel (p : Simulation.Kernel S A) :
    RiskBridge.ofKernel (regularKernel p) = p := by
  funext s a
  change RiskBridge.ofRegular (RiskBridge.toRegular (p s a)) = p s a
  exact RiskBridge.lawEquiv.left_inv _

lemma envelope_risk_eq_nested (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Simulation.Policy S A) (p : Simulation.Kernel S A) (n h : ℕ) (s : S) :
    Simulation.risk α c π p n h s =
      Nested.risk α c (regularPolicy π) (regularKernel p) n h s := by
  have he := RiskBridge.risk_eq_nested α hα hα1 c hc (regularPolicy π) (regularKernel p) n h s
  simpa only [of_regularPolicy, of_regularKernel] using he

/-- Entrywise measurable policy and model probabilities imply measurable nested CVaR. -/
theorem measurable_risk (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Ω → Simulation.Policy S A) (p : Ω → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun ω => (π ω h s).mass a))
    (hp : ∀ s a t, Measurable (fun ω => (p ω s a).mass t)) (n h : ℕ) (s : S) :
    Measurable (fun ω => Simulation.risk α c (π ω) (p ω) n h s) := by
  have hm := (Nested.continuous_risk α c n h s).measurable.comp
    ((measurable_regularPolicy π hπ).prodMk (measurable_regularKernel p hp))
  have he : (fun ω => Simulation.risk α c (π ω) (p ω) n h s) =
      (fun ω => Nested.risk α c (regularPolicy (π ω)) (regularKernel (p ω)) n h s) := by
    funext ω
    exact envelope_risk_eq_nested α hα hα1 c hc (π ω) (p ω) n h s
  rw [he]
  exact hm

/-- The ordinary reward functional is exactly the source Nested recursion on the equivalent laws. -/
def reward (r : ℕ → S → A → ℝ) (π : Simulation.Policy S A)
    (p : Simulation.Kernel S A) (n h : ℕ) (s : S) : ℝ :=
  Nested.reward r (regularPolicy π) (regularKernel p) n h s

theorem measurable_reward (r : ℕ → S → A → ℝ)
    (π : Ω → Simulation.Policy S A) (p : Ω → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun ω => (π ω h s).mass a))
    (hp : ∀ s a t, Measurable (fun ω => (p ω s a).mass t)) (n h : ℕ) (s : S) :
    Measurable (fun ω => reward r (π ω) (p ω) n h s) :=
  (Nested.continuous_reward r n h s).measurable.comp
    ((measurable_regularPolicy π hπ).prodMk (measurable_regularKernel p hp))

theorem integrable_risk (μ : Measure Ω) [IsFiniteMeasure μ]
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Ω → Simulation.Policy S A) (p : Ω → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun ω => (π ω h s).mass a))
    (hp : ∀ s a t, Measurable (fun ω => (p ω s a).mass t)) (n h : ℕ) (s : S) :
    Integrable (fun ω => Simulation.risk α c (π ω) (p ω) n h s) μ := by
  apply Integrable.of_bound (measurable_risk α hα hα1 c hc π p hπ hp n h s).aestronglyMeasurable n
  apply ae_of_all
  intro ω
  have hb := Simulation.risk_bounds α hα hα1 c hc (π ω) (p ω) n h s
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

theorem integrable_reward [Nonempty A] (μ : Measure Ω) [IsFiniteMeasure μ]
    (r : ℕ → S → A → ℝ) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (π : Ω → Simulation.Policy S A) (p : Ω → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun ω => (π ω h s).mass a))
    (hp : ∀ s a t, Measurable (fun ω => (p ω s a).mass t)) (n h : ℕ) (s : S) :
    Integrable (fun ω => reward r (π ω) (p ω) n h s) μ := by
  apply Integrable.of_bound (measurable_reward r π p hπ hp n h s).aestronglyMeasurable n
  apply ae_of_all
  intro ω
  have hb := Algorithm.reward_bounds r hr (regularPolicy (π ω)) (regularKernel (p ω)) n h s
  simpa only [reward, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

end
end Paper36.Measurability
