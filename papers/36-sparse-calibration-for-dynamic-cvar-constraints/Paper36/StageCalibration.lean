import Paper36.StageRisk
import Paper36.RiskBridge
import Paper36.Calibration
import Mathlib.MeasureTheory.Measure.Support

/-! Calibration and the automatic feasibility gap for B.3. The DP and its
minimizers use the actual StageRisk envelope recursion. A compact-primal
recursion is then proved equal to that risk and supplies continuity/Berge. -/
namespace Paper36.StageCalibration
noncomputable section
open scoped BigOperators
open Set Paper36.CVaR Paper36.Simulation
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

private def argmin (f : A → ℝ) : A := Classical.choose (Finite.exists_min f)
private lemma argmin_le (f : A → ℝ) (a : A) : f (argmin f) ≤ f a :=
  Classical.choose_spec (Finite.exists_min f) a

/-- The literal stage-dependent minimum-over-actions calibration recursion. -/
def dp (β : ℕ → ℝ) (c : ℕ → S → A → ℝ) (q : Kernel S A) : ℕ → ℕ → S → ℝ
  | 0, _, _ => 0
  | n+1, h, s =>
    let row := fun a => value (q s a) (β (h+1))
      (fun t => c h s a + dp β c q n (h+1) t)
    row (argmin row)

lemma dp_le_row (β : ℕ → ℝ) (c : ℕ → S → A → ℝ) (q : Kernel S A)
    (n h : ℕ) (s : S) (a : A) :
    dp β c q (n+1) h s ≤ value (q s a) (β (h+1))
      (fun t => c h s a + dp β c q n (h+1) t) := by
  rw [dp]
  exact argmin_le (fun a => value (q s a) (β (h+1))
    (fun t => c h s a + dp β c q n (h+1) t)) a

/-- A pure current action leaves precisely the successor-state CVaR. -/
lemma value_joint_pure (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (a : A) (q : A → Law S) (X : A × S → ℝ) :
    value (joint (dirac a) q) β X = value (q a) β (fun t => X (a,t)) := by
  rw [value_eq_primal_inf _ hβ hβ1, value_eq_primal_inf _ hβ hβ1]
  have heq : primal (joint (dirac a) q) β X = primal (q a) β (fun t => X (a,t)) := by
    funext z
    rw [primal_eq, primal_eq, expect_joint]
    change z + expect (dirac a).mass (fun b => expect (q b).mass (fun t => max (X (b,t)-z) 0)) / β = _
    rw [expect_dirac]
  rw [heq]

/-- Randomizing the current action cannot beat the calibration recursion. -/
theorem dp_le_risk (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (q : Kernel S A) (π : Policy S A)
    (n h : ℕ) (s : S) : dp β c q n h s ≤ StageRisk.risk β c π q n h s := by
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
    have hlow := value_joint_ge_of_forall (π h s) (q s) (hβ (h+1)).1 (hβ (h+1)).2
      (fun x : A × S => c h s x.1 + dp β c q n (h+1) x.2)
      (fun a => dp_le_row β c q n h s a)
    have hmono := value_mono (joint (π h s) (q s)) (hβ (h+1)).1 (hβ (h+1)).2
      (X := fun x : A × S => c h s x.1 + dp β c q n (h+1) x.2)
      (Y := fun x : A × S => c h s x.1 + StageRisk.risk β c π q n (h+1) x.2)
      (fun x => add_le_add_left (ih (h+1) x.2) _)
    exact hlow.trans hmono

lemma risk_congr (β : ℕ → ℝ) (c : ℕ → S → A → ℝ) (q : Kernel S A)
    (π π' : Policy S A) (n h : ℕ) (heq : ∀ j, h ≤ j → π j = π' j) (s : S) :
    StageRisk.risk β c π q n h s = StageRisk.risk β c π' q n h s := by
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
    simp only [StageRisk.risk, heq h le_rfl]
    congr 1
    funext x
    rw [ih (h+1) (fun j hj => heq j (by omega)) x.2]

def Deterministic (π : Policy S A) : Prop := ∀ h s, ∃ a, π h s = dirac a

/-- A single deterministic Markov tail policy attains the true DP simultaneously
at every state; successor-state minimizers are combined into the same tail. -/
theorem exists_deterministic_minimizer (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (q : Kernel S A) (n h : ℕ) :
    ∃ π : Policy S A, Deterministic π ∧ ∀ s, StageRisk.risk β c π q n h s = dp β c q n h s := by
  classical
  induction n generalizing h with
  | zero =>
    refine ⟨fun _ _ => dirac (Classical.arbitrary A), ?_, fun _ => rfl⟩
    intro _ _
    exact ⟨_, rfl⟩
  | succ n ih =>
    obtain ⟨tail, hdet, hatt⟩ := ih (h+1)
    let greedy : S → A := fun s => argmin (fun a => value (q s a) (β (h+1))
      (fun t => c h s a + dp β c q n (h+1) t))
    let π : Policy S A := fun j s => if j = h then dirac (greedy s) else tail j s
    have htail : ∀ s, StageRisk.risk β c π q n (h+1) s = dp β c q n (h+1) s := by
      intro s
      rw [risk_congr β c q π tail n (h+1) (fun j hj => ?_) s, hatt s]
      funext t
      simp only [π, if_neg (show j ≠ h by omega)]
    refine ⟨π, ?_, ?_⟩
    · intro j s
      by_cases hj : j = h
      · exact ⟨greedy s, by simp [π, hj]⟩
      · obtain ⟨a, ha⟩ := hdet j s
        exact ⟨a, by simpa [π, hj] using ha⟩
    · intro s
      rw [StageRisk.risk]
      have hπ : π h s = dirac (greedy s) := by simp only [π, if_pos rfl]
      rw [hπ]
      have hx : (fun x : A × S => c h s x.1 + StageRisk.risk β c π q n (h+1) x.2) =
          (fun x : A × S => c h s x.1 + dp β c q n (h+1) x.2) := by
        funext x
        rw [htail]
      rw [hx, value_joint_pure (β (h+1)) (hβ (h+1)).1 (hβ (h+1)).2 (greedy s)]
      rfl

/-- The DP is exactly the minimum over every randomized physical-state Markov tail. -/
theorem dp_eq_inf_risk (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (q : Kernel S A) (n h : ℕ) (s : S) :
    dp β c q n h s = sInf ((fun π : Policy S A => StageRisk.risk β c π q n h s) '' univ) := by
  obtain ⟨π, _, hatt⟩ := exists_deterministic_minimizer β hβ c q n h
  have hb : BddBelow ((fun π : Policy S A => StageRisk.risk β c π q n h s) '' univ) := by
    refine ⟨dp β c q n h s, ?_⟩
    rintro _ ⟨π', _, rfl⟩
    exact dp_le_risk β hβ c q π' n h s
  apply le_antisymm
  · have hne : ((fun π' : Policy S A => StageRisk.risk β c π' q n h s) '' univ).Nonempty :=
      ⟨StageRisk.risk β c π q n h s, ⟨π, mem_univ _, rfl⟩⟩
    apply le_csInf hne
    rintro _ ⟨π', _, rfl⟩
    exact dp_le_risk β hβ c q π' n h s
  · exact (csInf_le hb ⟨π, mem_univ _, rfl⟩).trans (hatt s).le

/-- Numerical risk bounds are consequences of the minimizer, not additional DP premises. -/
theorem dp_bounds (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (q : Kernel S A) (n h : ℕ) (s : S) : dp β c q n h s ∈ Icc 0 (n : ℝ) := by
  obtain ⟨π, _, hatt⟩ := exists_deterministic_minimizer β hβ c q n h
  rw [← hatt s]
  exact StageRisk.risk_bounds β hβ c hc π q n h s

/-- Pointwise model feasibility is realized by the same simultaneous
minimum-risk deterministic policy, with no supplied baseline policy. -/
theorem exists_feasible_deterministic (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (q : Kernel S A) (H h : ℕ) (s₀ : S) (τ : ℝ)
    (hfeas : ∃ π : Policy S A, StageRisk.risk β c π q H h s₀ < τ) :
    ∃ π : Policy S A, Deterministic π ∧
      (∀ s, StageRisk.risk β c π q H h s = dp β c q H h s) ∧
      StageRisk.risk β c π q H h s₀ < τ := by
  obtain ⟨π₀, hπ₀⟩ := hfeas
  obtain ⟨π, hdet, hatt⟩ := exists_deterministic_minimizer β hβ c q H h
  refine ⟨π, hdet, hatt, ?_⟩
  rw [hatt s₀]
  exact (dp_le_risk β hβ c q π₀ H h s₀).trans_lt hπ₀

/-- A compact-primal representation on the source's compact policy/kernel
simplices. It will be proved equal to the actual StageRisk envelope. -/
def compactRisk (β : ℕ → ℝ) (c : ℕ → S → A → ℝ)
    (π : Nested.Policy S A) (q : Nested.Kernel S A) : ℕ → ℕ → S → ℝ
  | 0, _, _ => 0
  | n+1, h, s => Regularity.compactCVaR (β (h+1)) (n+1 : ℕ)
      (Nested.joint (π h s) (q s))
      (fun x => c h s x.1 + compactRisk β c π q n (h+1) x.2)

lemma compactRisk_bounds (β : ℕ → ℝ) (hβ : ∀ j, 0 ≤ β j)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (π : Nested.Policy S A) (q : Nested.Kernel S A) (n h : ℕ) (s : S) :
    compactRisk β c π q n h s ∈ Icc 0 (n : ℝ) := by
  induction n generalizing h s with
  | zero => simp [compactRisk]
  | succ n ih =>
    constructor
    · exact Regularity.compactCVaR_nonneg _ _ (hβ (h+1)) (by positivity) _ _
    · apply Regularity.compactCVaR_le_bound _ _ (by positivity)
      intro x
      have hx := (ih (h+1) x.2).2
      have hc' := (hc h s x.1).2
      push_cast
      linarith

lemma compactRisk_step_eq_primal (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (π : Nested.Policy S A) (q : Nested.Kernel S A) (n h : ℕ) (s : S) :
    compactRisk β c π q (n+1) h s = Regularity.primalCVaR (β (h+1))
      (Nested.joint (π h s) (q s))
      (fun x => c h s x.1 + compactRisk β c π q n (h+1) x.2) := by
  apply Regularity.compactCVaR_eq_primalCVaR _ _ (hβ (h+1)).1 (hβ (h+1)).2 (by positivity)
  intro x
  have hr := compactRisk_bounds β (fun j => (hβ j).1.le) c hc π q n (h+1) x.2
  have hc' := hc h s x.1
  constructor <;> push_cast <;> linarith [hr.1, hr.2, hc'.1, hc'.2]

/-- Every compact-primal risk value is exactly the actual stage-dependent envelope risk. -/
theorem risk_eq_compact (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (π : Nested.Policy S A) (q : Nested.Kernel S A) (n h : ℕ) (s : S) :
    StageRisk.risk β c (RiskBridge.ofPolicy π) (RiskBridge.ofKernel q) n h s =
      compactRisk β c π q n h s := by
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
    rw [StageRisk.risk, compactRisk_step_eq_primal β hβ c hc π q n h s]
    change value (RiskBridge.ofRegular (Nested.joint (π h s) (q s))) (β (h+1))
      (fun x => c h s x.1 + StageRisk.risk β c (RiskBridge.ofPolicy π)
        (RiskBridge.ofKernel q) n (h+1) x.2) = _
    rw [RiskBridge.value_eq_regular (β (h+1)) (hβ (h+1)).1 (hβ (h+1)).2]
    congr 1
    funext x
    rw [ih]

/-- Joint continuity is proved backward using the compact threshold interval. -/
theorem continuous_compactRisk (β : ℕ → ℝ) (c : ℕ → S → A → ℝ)
    (n h : ℕ) (s : S) :
    Continuous (fun p : Nested.Policy S A × Nested.Kernel S A => compactRisk β c p.1 p.2 n h s) := by
  induction n generalizing h s with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous (fun p : Nested.Policy S A × Nested.Kernel S A =>
      Regularity.compactCVaR (β (h+1)) (n+1 : ℕ) (Nested.joint (p.1 h s) (p.2 s))
        (fun x => c h s x.1 + compactRisk β c p.1 p.2 n (h+1) x.2))
    have hj : Continuous (fun p : Nested.Policy S A × Nested.Kernel S A =>
        Nested.joint (p.1 h s) (p.2 s)) :=
      Nested.continuous_joint.comp (((Nested.continuous_policy_row h s).comp continuous_fst).prodMk
        ((continuous_apply s).comp continuous_snd))
    have hx : Continuous (fun p : Nested.Policy S A × Nested.Kernel S A =>
        fun x : A × S => c h s x.1 + compactRisk β c p.1 p.2 n (h+1) x.2) := by
      apply continuous_pi
      intro x
      exact continuous_const.add (ih (h+1) x.2)
    have hs := (Regularity.continuous_compactCVaR (Ω := A × S) (β (h+1)) (n+1 : ℕ)).comp
      (hj.prodMk hx)
    simpa only [Function.comp_def] using hs

/-- Joint continuity of the actual risk on the actual source probability simplices. -/
theorem continuous_actualRisk (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (n h : ℕ) (s : S) :
    Continuous (fun p : Nested.Policy S A × Nested.Kernel S A =>
      StageRisk.risk β c (RiskBridge.ofPolicy p.1) (RiskBridge.ofKernel p.2) n h s) := by
  simpa only [risk_eq_compact β hβ c hc] using continuous_compactRisk β c n h s

def toPolicy (π : Policy S A) : Nested.Policy S A := fun h s => RiskBridge.toRegular (π h s)

@[simp] lemma ofPolicy_toPolicy (π : Policy S A) : RiskBridge.ofPolicy (toPolicy π) = π := by
  funext h s
  exact RiskBridge.lawEquiv.left_inv (π h s)

lemma actual_risk_eq_compact (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (π : Policy S A) (q : Nested.Kernel S A) (n h : ℕ) (s : S) :
    StageRisk.risk β c π (RiskBridge.ofKernel q) n h s = compactRisk β c (toPolicy π) q n h s := by
  simpa only [ofPolicy_toPolicy] using risk_eq_compact β hβ c hc (toPolicy π) q n h s

/-- The source minimum over the full randomized physical-state Markov class. -/
def minimumRisk (β : ℕ → ℝ) (c : ℕ → S → A → ℝ) (n h : ℕ) (s : S)
    (q : Nested.Kernel S A) : ℝ :=
  sInf ((fun π : Nested.Policy S A => compactRisk β c π q n h s) '' univ)

/-- Berge's compact-minimum argument, applied to the proved stage recursion. -/
theorem continuous_minimumRisk (β : ℕ → ℝ) (c : ℕ → S → A → ℝ)
    (n h : ℕ) (s : S) : Continuous (minimumRisk β c n h s : Nested.Kernel S A → ℝ) := by
  apply isCompact_univ.continuous_sInf
  exact (continuous_compactRisk β c n h s).comp
    (show Continuous (fun p : Nested.Kernel S A × Nested.Policy S A => (p.2, p.1)) from
      continuous_snd.prodMk continuous_fst)

/-- The continuous compact minimum equals the actual pure-action calibration DP. -/
theorem minimumRisk_eq_dp (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (q : Nested.Kernel S A) (n h : ℕ) (s : S) :
    minimumRisk β c n h s q = dp β c (RiskBridge.ofKernel q) n h s := by
  obtain ⟨π, _, hatt⟩ := exists_deterministic_minimizer β hβ c (RiskBridge.ofKernel q) n h
  have hb : BddBelow ((fun π' : Nested.Policy S A => compactRisk β c π' q n h s) '' univ) := by
    refine ⟨dp β c (RiskBridge.ofKernel q) n h s, ?_⟩
    rintro _ ⟨π', _, rfl⟩
    change dp β c (RiskBridge.ofKernel q) n h s ≤ compactRisk β c π' q n h s
    rw [← risk_eq_compact β hβ c hc π' q n h s]
    exact dp_le_risk β hβ c (RiskBridge.ofKernel q) (RiskBridge.ofPolicy π') n h s
  apply le_antisymm
  · have hi := csInf_le hb ⟨toPolicy π, mem_univ _, rfl⟩
    change minimumRisk β c n h s q ≤ compactRisk β c (toPolicy π) q n h s at hi
    rw [← actual_risk_eq_compact β hβ c hc π q n h s, hatt s] at hi
    exact hi
  · have hne : ((fun π' : Nested.Policy S A => compactRisk β c π' q n h s) '' univ).Nonempty :=
      ⟨compactRisk β c (toPolicy π) q n h s, ⟨toPolicy π, mem_univ _, rfl⟩⟩
    apply le_csInf hne
    rintro _ ⟨π', _, rfl⟩
    change dp β c (RiskBridge.ofKernel q) n h s ≤ compactRisk β c π' q n h s
    rw [← risk_eq_compact β hβ c hc π' q n h s]
    exact dp_le_risk β hβ c (RiskBridge.ofKernel q) (RiskBridge.ofPolicy π') n h s

/-- In particular the actual minimum-risk DP is continuous in the unknown kernel. -/
theorem continuous_dp (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (n h : ℕ) (s : S) :
    Continuous (fun q : Nested.Kernel S A => dp β c (RiskBridge.ofKernel q) n h s) := by
  have heq : (minimumRisk β c n h s : Nested.Kernel S A → ℝ) =
      (fun q => dp β c (RiskBridge.ofKernel q) n h s) :=
    funext (fun q => minimumRisk_eq_dp β hβ c hc q n h s)
  rw [← heq]
  exact continuous_minimumRisk β c n h s

/-- The exact constrained exploitation oracle attains its optimum for the same
stage-dependent risk and the ordinary physical-state expected reward. -/
theorem exists_constrained_optimum (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (n h : ℕ) (s : S) (q : Nested.Kernel S A) (τ : ℝ)
    (hne : ∃ π : Nested.Policy S A,
      StageRisk.risk β c (RiskBridge.ofPolicy π) (RiskBridge.ofKernel q) n h s ≤ τ) :
    ∃ π : Nested.Policy S A,
      StageRisk.risk β c (RiskBridge.ofPolicy π) (RiskBridge.ofKernel q) n h s ≤ τ ∧
      ∀ π', StageRisk.risk β c (RiskBridge.ofPolicy π') (RiskBridge.ofKernel q) n h s ≤ τ →
        Nested.reward r π' q n h s ≤ Nested.reward r π q n h s := by
  have hcont : Continuous (fun π : Nested.Policy S A =>
      StageRisk.risk β c (RiskBridge.ofPolicy π) (RiskBridge.ofKernel q) n h s) :=
    (continuous_actualRisk β hβ c hc n h s).comp
      (show Continuous (fun π : Nested.Policy S A => (π,q)) from continuous_id.prodMk continuous_const)
  have hcontR : Continuous (fun π : Nested.Policy S A => Nested.reward r π q n h s) :=
    (Nested.continuous_reward r n h s).comp
      (show Continuous (fun π : Nested.Policy S A => (π,q)) from continuous_id.prodMk continuous_const)
  exact (isClosed_le hcont continuous_const).isCompact.exists_isMaxOn hne hcontR.continuousOn

section Prior
open MeasureTheory
variable [MeasurableSpace (Nested.Kernel S A)]

/-- The induced uniform gap, computed from the actual prior support. -/
def uniformGap (μ : Measure (Nested.Kernel S A)) (β : ℕ → ℝ)
    (c : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S) (τ : ℝ) : ℝ :=
  τ - sSup (minimumRisk β c H 0 s₁ '' μ.support)

/-- Model-wise strict feasibility on the actual prior support yields a positive
uniform gap. The premise supplies neither a common baseline nor a numeric gap. -/
theorem prior_support_uniform_gap (μ : Measure (Nested.Kernel S A)) [IsProbabilityMeasure μ]
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (s₁ : S)
    (τ : ℝ) (hstrict : ∀ q ∈ μ.support, ∃ π : Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ) :
    0 < τ - sSup (minimumRisk β c H 0 s₁ '' μ.support) ∧
      ∀ q ∈ μ.support, τ - sSup (minimumRisk β c H 0 s₁ '' μ.support) ≤
        τ - dp β c (RiskBridge.ofKernel q) H 0 s₁ := by
  have hμ : μ ≠ 0 := by
    intro hz
    have hmass : μ univ = 1 := measure_univ
    simp [hz] at hmass
  have hstrict' : ∀ q ∈ μ.support, minimumRisk β c H 0 s₁ q < τ := by
    intro q hq
    obtain ⟨π, hπ⟩ := hstrict q hq
    rw [minimumRisk_eq_dp β hβ c hc q H 0 s₁]
    exact (dp_le_risk β hβ c (RiskBridge.ofKernel q) π H 0 s₁).trans_lt hπ
  have hg := Regularity.automatic_uniform_margin μ.support μ.isClosed_support.isCompact
    (μ.nonempty_support hμ) (minimumRisk β c H 0 s₁)
    (continuous_minimumRisk β c H 0 s₁).continuousOn τ hstrict'
  simpa only [minimumRisk_eq_dp β hβ c hc] using hg

/-- The actual sampled-model calibration deposit lies between the induced
positive gap and tau, exactly the two numerical facts required by the bank. -/
theorem calibration_deposit_bounds (μ : Measure (Nested.Kernel S A)) [IsProbabilityMeasure μ]
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (s₁ : S)
    (τ : ℝ) (hstrict : ∀ q ∈ μ.support, ∃ π : Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) H 0 s₁ < τ) :
    0 < uniformGap μ β c H s₁ τ ∧ ∀ q ∈ μ.support,
      uniformGap μ β c H s₁ τ ≤ τ-dp β c (RiskBridge.ofKernel q) H 0 s₁ ∧
      τ-dp β c (RiskBridge.ofKernel q) H 0 s₁ ≤ τ := by
  have hg := prior_support_uniform_gap μ β hβ H c hc s₁ τ hstrict
  refine ⟨hg.1, fun q hq => ⟨hg.2 q hq, ?_⟩⟩
  exact sub_le_self _ (dp_bounds β hβ c hc (RiskBridge.ofKernel q) H 0 s₁).1

end Prior

end
end Paper36.StageCalibration
