import Paper36.Selection
import Paper36.StageAlgorithm

/-! The stage-dependent Appendix A.2/B.3 selector bridge. The only general
external theorem is Selection.CompactSectionMaximum; all actual deterministic
calibration and constrained-reward assertions are proved here. -/
namespace Paper36.StageSelection
open Set MeasureTheory Paper36.Regularity Paper36.Nested
noncomputable section
universe u
variable {S A : Type u} [Fintype S] [Fintype A]

local instance law_polish {I : Type u} [Fintype I] : PolishSpace (Law I) :=
  (isClosed_stdSimplex I).polishSpace

local instance kernelPolicy_opens : OpensMeasurableSpace (Kernel S A × Policy S A) :=
  @Prod.opensMeasurableSpace _ _ _ _ _ _ inferInstance inferInstance inferInstance

/-- Pure physical-state policies form the compact product of finite vertex sets. -/
def deterministicPolicies : Set (Policy S A) := {π | ∀ h s, ∃ a, π h s = Nested.pure a}

theorem deterministicPolicies_closed : IsClosed (deterministicPolicies (S := S) (A := A)) := by
  unfold deterministicPolicies
  simp only [Set.setOf_forall, Set.setOf_exists]
  apply isClosed_iInter
  intro h
  apply isClosed_iInter
  intro s
  exact isClosed_iUnion_of_finite (fun a => isClosed_eq (continuous_policy_row h s) continuous_const)

lemma toRegular_dirac (a : A) : RiskBridge.toRegular (Simulation.dirac a) = Nested.pure a := by
  apply Subtype.ext
  funext b
  simp [RiskBridge.toRegular, Simulation.dirac, Nested.pure, stdSimplex.vertex, Pi.single_apply]

lemma ofRegular_pure (a : A) : RiskBridge.ofRegular (Nested.pure a) = Simulation.dirac a := by
  rw [← toRegular_dirac a]
  exact RiskBridge.lawEquiv.left_inv _

omit [Fintype S] in
lemma deterministic_of_vertices {π : Policy S A} (hπ : π ∈ deterministicPolicies) :
    StageCalibration.Deterministic (RiskBridge.ofPolicy π) := by
  intro h s
  obtain ⟨a,ha⟩ := hπ h s
  refine ⟨a, ?_⟩
  change RiskBridge.ofRegular (π h s) = Simulation.dirac a
  rw [ha, ofRegular_pure]

omit [Fintype S] in
lemma vertices_of_deterministic {π : Simulation.Policy S A} (hπ : StageCalibration.Deterministic π) :
    StageCalibration.toPolicy π ∈ deterministicPolicies := by
  intro h s
  obtain ⟨a,ha⟩ := hπ h s
  refine ⟨a, ?_⟩
  change RiskBridge.toRegular (π h s) = Nested.pure a
  rw [ha, toRegular_dirac]

def feasible (β : ℕ → ℝ) (τ : ℝ) (c : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S)
    (Q : Set (Kernel S A)) (q : Kernel S A) : Set (Policy S A) :=
  {π | q ∈ Q → StageAlgorithm.risk β c π q H 0 s₁ ≤ τ}

variable [Nonempty A]

variable (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
  (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (H : ℕ) (s₁ : S)

include hβ hc

theorem actual_risk_continuous :
    Continuous (fun p : Kernel S A × Policy S A => StageAlgorithm.risk β c p.2 p.1 H 0 s₁) :=
  (StageCalibration.continuous_actualRisk β hβ c hc H 0 s₁).comp
    (continuous_snd.prodMk continuous_fst)

theorem feasible_graph_closed (τ : ℝ) :
    IsClosed {p : Kernel S A × Policy S A | StageAlgorithm.risk β c p.2 p.1 H 0 s₁ ≤ τ} :=
  isClosed_le (actual_risk_continuous β hβ c hc H s₁) continuous_const

theorem feasible_graph_measurable (τ : ℝ) (Q : Set (Kernel S A)) (hQ : IsClosed Q) :
    MeasurableSet {p : Kernel S A × Policy S A | p.2 ∈ feasible β τ c H s₁ Q p.1} := by
  have houtside : MeasurableSet {p : Kernel S A × Policy S A | p.1 ∉ Q} :=
    (hQ.measurableSet.preimage measurable_fst).compl
  have hinside := (feasible_graph_closed β hβ c hc H s₁ τ).measurableSet
  convert houtside.union hinside using 1
  ext p
  simp [feasible, or_iff_not_imp_left]

theorem feasible_section_compact (τ : ℝ) (Q : Set (Kernel S A)) (q : Kernel S A) :
    IsCompact (feasible β τ c H s₁ Q q) := by
  by_cases hq : q ∈ Q
  · have heq : feasible β τ c H s₁ Q q = {π | StageAlgorithm.risk β c π q H 0 s₁ ≤ τ} := by
      ext π; simp [feasible, hq]
    rw [heq]
    exact (isClosed_le ((actual_risk_continuous β hβ c hc H s₁).comp
      (continuous_const.prodMk continuous_id)) continuous_const).isCompact
  · have heq : feasible β τ c H s₁ Q q = Set.univ := by ext π; simp [feasible, hq]
    rw [heq]
    exact isCompact_univ

local instance policy_nonempty : Nonempty (Policy S A) :=
  ⟨fun _ _ => Nested.pure (Classical.arbitrary A)⟩

omit hβ hc in
theorem feasible_section_nonempty (τ : ℝ) (Q : Set (Kernel S A))
    (hstrict : ∀ q ∈ Q, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ) (q : Kernel S A) :
    (feasible β τ c H s₁ Q q).Nonempty := by
  by_cases hq : q ∈ Q
  · obtain ⟨π,hπ⟩ := hstrict q hq
    refine ⟨StageCalibration.toPolicy π, fun _ => ?_⟩
    change StageRisk.risk β c (RiskBridge.ofPolicy (StageCalibration.toPolicy π))
      (RiskBridge.ofKernel q) H 0 s₁ ≤ τ
    rw [StageCalibration.ofPolicy_toPolicy]
    exact hπ.le
  · exact ⟨Classical.arbitrary (Policy S A), fun h => (hq h).elim⟩

/-- Calibration is selected from the actual compact deterministic-policy set,
so its deterministic field is proved rather than assumed or dropped. -/
theorem exists_borel_calibration (external : Selection.CompactSectionMaximum.{u}) :
    ∃ σ : Kernel S A → Policy S A, Measurable σ ∧ ∀ q,
      StageAlgorithm.risk β c (σ q) q H 0 s₁ = StageAlgorithm.minimumRisk β c H s₁ q ∧
      StageCalibration.Deterministic (RiskBridge.ofPolicy (σ q)) := by
  have hf := (actual_risk_continuous β hβ c hc H s₁).neg
  have hgraph : MeasurableSet {p : Kernel S A × Policy S A | p.2 ∈ deterministicPolicies} :=
    deterministicPolicies_closed.measurableSet.preimage measurable_snd
  have hne : (deterministicPolicies (S := S) (A := A)).Nonempty :=
    ⟨fun _ _ => Nested.pure (Classical.arbitrary A), fun _ _ => ⟨_,rfl⟩⟩
  obtain ⟨σ,hσ,hs⟩ := external.maximize (fun _ : Kernel S A => deterministicPolicies)
    (fun p => -StageAlgorithm.risk β c p.2 p.1 H 0 s₁) hgraph
    (fun _ => deterministicPolicies_closed.isCompact) (fun _ => hne) hf.measurable
    (fun q => hf.comp (continuous_const.prodMk continuous_id))
  refine ⟨σ,hσ,fun q => ⟨?_,deterministic_of_vertices (hs q).1⟩⟩
  obtain ⟨π,hdet,hatt⟩ := StageCalibration.exists_deterministic_minimizer β hβ c (RiskBridge.ofKernel q) H 0
  have hopt := (hs q).2 (StageCalibration.toPolicy π) (vertices_of_deterministic hdet)
  have hmin := StageCalibration.dp_le_risk β hβ c (RiskBridge.ofKernel q)
    (RiskBridge.ofPolicy (σ q)) H 0 s₁
  change StageAlgorithm.minimumRisk β c H s₁ q ≤ StageAlgorithm.risk β c (σ q) q H 0 s₁ at hmin
  have heq : StageAlgorithm.risk β c (StageCalibration.toPolicy π) q H 0 s₁ =
      StageAlgorithm.minimumRisk β c H s₁ q := by
    unfold StageAlgorithm.risk StageAlgorithm.minimumRisk
    rw [StageCalibration.ofPolicy_toPolicy]
    exact hatt s₁
  rw [heq] at hopt
  linarith

theorem exists_borel_exploitation (external : Selection.CompactSectionMaximum.{u})
    (τ : ℝ) (r : ℕ → S → A → ℝ) (Q : Set (Kernel S A)) (hQ : IsClosed Q)
    (hstrict : ∀ q ∈ Q, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ) :
    ∃ σ : Kernel S A → Policy S A, Measurable σ ∧ ∀ q ∈ Q,
      StageAlgorithm.risk β c (σ q) q H 0 s₁ ≤ τ ∧ ∀ π,
        StageAlgorithm.risk β c π q H 0 s₁ ≤ τ →
          Nested.reward r π q H 0 s₁ ≤ Nested.reward r (σ q) q H 0 s₁ := by
  have hf : Continuous (fun p : Kernel S A × Policy S A => reward r p.2 p.1 H 0 s₁) :=
    (continuous_reward r H 0 s₁).comp (continuous_snd.prodMk continuous_fst)
  obtain ⟨σ,hσ,hs⟩ := external.maximize (feasible β τ c H s₁ Q)
    (fun p => reward r p.2 p.1 H 0 s₁) (feasible_graph_measurable β hβ c hc H s₁ τ Q hQ)
    (feasible_section_compact β hβ c hc H s₁ τ Q)
    (feasible_section_nonempty β c H s₁ τ Q hstrict) hf.measurable
    (fun q => hf.comp (continuous_const.prodMk continuous_id))
  exact ⟨σ,hσ,fun q hq => ⟨(hs q).1 hq,fun π hπ => (hs q).2 π (fun _ => hπ)⟩⟩

/-- The actual stage-dependent exact Borel protocol, including deterministic
calibration, follows from the same fully general external selection ingredient. -/
theorem exists_borel_oracles (external : Selection.CompactSectionMaximum.{u})
    (τ : ℝ) (r : ℕ → S → A → ℝ) (Q : Set (Kernel S A)) (hQ : IsClosed Q)
    (hstrict : ∀ q ∈ Q, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ) :
    Nonempty (StageAlgorithm.BorelOracles β c r H s₁ τ Q) := by
  obtain ⟨cal,hcal,hcalExact⟩ := exists_borel_calibration β hβ c hc H s₁ external
  obtain ⟨exp,hexp,hexpExact⟩ := exists_borel_exploitation β hβ c hc H s₁ external τ r Q hQ hstrict
  exact ⟨{ calibration := cal
           exploitation := exp
           cal_exact := fun q _ => (hcalExact q).1
           cal_deterministic := fun q _ => (hcalExact q).2
           exp_feasible := fun q hq => (hexpExact q hq).1
           exp_optimal := fun q hq => (hexpExact q hq).2
           measurable_calibration := hcal
           measurable_exploitation := hexp }⟩

end
end Paper36.StageSelection
