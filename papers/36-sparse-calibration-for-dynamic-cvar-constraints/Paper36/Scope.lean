import Paper36.Endpoints
import Paper36.RowTapes
import Paper36.RiskBridge
import Paper36.Bounds

/-! Remarks 2.2 and 5.7 also exclude reading the risk-value certificate as a
realized-cost certificate. A true one-stage MDP has identically zero signed
risk-value debt, while actual high-cost complete trajectories have positive
probability and exceed the zero certificate. -/
namespace Paper36.Scope
open Paper36.Regularity Paper36.Nested Paper36.CVaR Paper36.Trajectories
open scoped BigOperators
noncomputable section

/-- Fair randomization occurs inside the source's actual one-stage CVaR. -/
def fair : Regularity.Law Bool := ⟨fun _ => (1:ℝ)/2, by
  constructor
  · intro b; norm_num
  · norm_num [Fintype.sum_bool]⟩

def policy : Nested.Policy Unit Bool := fun _ _ => fair

def trajectoryLaw : CVaR.Law (Trajectory Unit Bool 1) :=
  Trajectories.trajectoryLaw (RiskBridge.ofPolicy policy)
    (RiskBridge.ofKernel Endpoints.exampleKernel) 1 0 ()

def highPath : Trajectory Unit Bool 1 := ((), true, ())

lemma fair_risk : Nested.risk 1 Endpoints.exampleCost policy Endpoints.exampleKernel 1 0 () = (1:ℝ)/2 := by
  rw [Endpoints.nested_one_eq_expected_cost Endpoints.exampleCost
    (fun _ _ a => by cases a <;> norm_num [Endpoints.exampleCost]), Endpoints.one_stage_reward]
  norm_num [Regularity.expectation, policy, fair, Endpoints.exampleCost, Fintype.sum_bool, Subtype.coe_mk]
  rfl

/-- This is the mass of a complete physical-state/action/successor trajectory. -/
lemma highPath_probability : trajectoryLaw.mass highPath = (1:ℝ)/2 := by
  norm_num [trajectoryLaw, Trajectories.trajectoryLaw, Trajectories.bindLaw,
    CVaR.joint, Simulation.dirac, RiskBridge.ofPolicy, RiskBridge.ofKernel,
    RiskBridge.ofRegular, policy, fair, Endpoints.exampleKernel, Nested.pure,
    stdSimplex.vertex, highPath, Fintype.sum_unique]
  rfl

/-- The literal one-stage certificate is zero for every prescribed delta. -/
lemma zero_certificate (δ : ℝ) (K : ℕ) :
    Bounds.certificate 1 2 1 (Weights.W 1 1) (Weights.w 1 1) δ K = 0 := by
  simp [Bounds.certificate]

/-- Risk-value debt is exactly zero at every evaluation horizon. -/
theorem risk_value_debt_zero (K : ℕ) :
    (∑ _n ∈ Finset.range K,
      (Nested.risk 1 Endpoints.exampleCost policy Endpoints.exampleKernel 1 0 () - (1:ℝ)/2)) = 0 := by
  simp [fair_risk]

/-- K independent episodes of the real physical trajectory law. -/
def episodes (K : ℕ) : CVaR.Law (Fin K → Trajectory Unit Bool 1) := RowTapes.iidLaw trajectoryLaw K

def realizedDebt {K : ℕ} (paths : Fin K → Trajectory Unit Bool 1) : ℝ :=
  ∑ i, (Endpoints.exampleCost 0 () (paths i).2.1 - (1:ℝ)/2)

lemma all_high_probability (K : ℕ) :
    (episodes K).mass (fun _ => highPath) = ((1:ℝ)/2)^K := by
  simp [episodes, RowTapes.iidLaw, highPath_probability]

lemma all_high_realizedDebt (K : ℕ) : realizedDebt (fun _ : Fin K => highPath) = (K:ℝ)/2 := by
  simp [realizedDebt, highPath, Endpoints.exampleCost]
  ring

/-- An almost-sure risk-value bound does not imply a fixed almost-sure
realized-cost bound, even in a known one-state MDP at alpha=1. -/
theorem realized_cost_not_pathwise_controlled (G : ℝ) :
    (∀ K, (∑ _n ∈ Finset.range K,
      (Nested.risk 1 Endpoints.exampleCost policy Endpoints.exampleKernel 1 0 () - (1:ℝ)/2)) = 0) ∧
    ∃ K, ∃ paths : Fin K → Trajectory Unit Bool 1,
      0 < (episodes K).mass paths ∧ G < realizedDebt paths := by
  refine ⟨risk_value_debt_zero, ?_⟩
  obtain ⟨K,hK⟩ := exists_nat_gt (2*G)
  refine ⟨K, fun _ => highPath, ?_, ?_⟩
  · rw [all_high_probability]; positivity
  · rw [all_high_realizedDebt]; linarith

/-- Already at K=1, a zero risk-value certificate with arbitrary nominal
failure budget cannot be read as the same realized-cost certificate: the
positive-debt trajectory has probability one half. -/
theorem fixed_certificate_does_not_certify_realized_cost :
    Nested.risk 1 Endpoints.exampleCost policy Endpoints.exampleKernel 1 0 () - (1:ℝ)/2 = 0 ∧
    trajectoryLaw.mass highPath = (1:ℝ)/2 ∧
    Bounds.certificate 1 2 1 (Weights.W 1 1) (Weights.w 1 1) ((1:ℝ)/4) 1 <
      Endpoints.exampleCost 0 () highPath.2.1 - (1:ℝ)/2 := by
  constructor
  · rw [fair_risk]; ring
  · refine ⟨highPath_probability, ?_⟩
    rw [zero_certificate]
    norm_num [highPath, Endpoints.exampleCost]

end
end Paper36.Scope
