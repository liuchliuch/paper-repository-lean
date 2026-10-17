import Paper36.Nested
import Paper36.Simulation
import Paper36.Tightening

/-! Bridges between the compact-primal model, the exact finite risk envelope,
and the three-action obstruction. All laws include action randomization. -/
namespace Paper36.RiskBridge
open scoped BigOperators
noncomputable section
variable {Ω S A : Type*} [Fintype Ω] [Fintype S] [Fintype A]

def ofRegular (P : Regularity.Law Ω) : CVaR.Law Ω :=
  ⟨P, P.property.1, P.property.2⟩

def toRegular (P : CVaR.Law Ω) : Regularity.Law Ω :=
  ⟨P.mass, P.nonneg, P.total⟩

/-- The two finite probability-law representations are equivalent. -/
def lawEquiv : CVaR.Law Ω ≃ Regularity.Law Ω where
  toFun := toRegular
  invFun := ofRegular
  left_inv P := by cases P; rfl
  right_inv P := by apply Subtype.ext; rfl

lemma primal_eq_regular (α : ℝ) (P : Regularity.Law Ω) (X : Ω → ℝ) (z : ℝ) :
    CVaR.primal (ofRegular P) α X z = Regularity.objective α P X z := by
  rw [CVaR.primal_eq]
  unfold CVaR.expect Regularity.objective Regularity.expectation ofRegular
  dsimp
  rw [div_eq_mul_inv, mul_comm]

/-- Finite-envelope CVaR equals the unrestricted primal used by the main model. -/
theorem value_eq_regular (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (P : Regularity.Law Ω) (X : Ω → ℝ) :
    CVaR.value (ofRegular P) α X = Regularity.primalCVaR α P X := by
  rw [CVaR.value_eq_primal_inf _ ha ha1]
  unfold Regularity.primalCVaR
  have he : CVaR.primal (ofRegular P) α X = Regularity.objective α P X := by
    funext z
    exact primal_eq_regular α P X z
  rw [he]

/-- Compact thresholds, unrestricted thresholds and the finite envelope coincide. -/
theorem compactCVaR_eq_value (α B : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (hB : 0 ≤ B) (P : Regularity.Law Ω) (X : Ω → ℝ)
    (hX : ∀ i, X i ∈ Set.Icc 0 B) :
    Regularity.compactCVaR α B P X = CVaR.value (ofRegular P) α X := by
  rw [Regularity.compactCVaR_eq_primalCVaR α B ha ha1 hB P X hX,
    value_eq_regular α ha ha1 P X]

/-- The obstruction's law is an actual probability law on its three actions. -/
def tighteningLaw (p : Tightening.Policy) : CVaR.Law Tightening.Action :=
  ⟨p.prob, (Tightening.policy_probability p).1, (Tightening.policy_probability p).2⟩

lemma primal_eq_tightening (α t : ℝ) (p : Tightening.Policy) (z : ℝ) :
    CVaR.primal (tighteningLaw p) α (Tightening.cost t) z =
      Tightening.objective α t p z := by
  rw [Tightening.objective_action_law, CVaR.primal_eq]
  rfl

/-- Proposition 3.1 uses exactly the same CVaR as the simulation and planning model. -/
theorem tightening_risk_eq_value (α t : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (p : Tightening.Policy) :
    Tightening.risk α t p = CVaR.value (tighteningLaw p) α (Tightening.cost t) := by
  rw [CVaR.value_eq_primal_inf _ ha ha1]
  unfold Tightening.risk
  have he : CVaR.primal (tighteningLaw p) α (Tightening.cost t) =
      Tightening.objective α t p := by
    funext z
    exact primal_eq_tightening α t p z
  rw [he]


def ofPolicy (π : Nested.Policy S A) : Simulation.Policy S A :=
  fun h s => ofRegular (π h s)

def ofKernel (p : Nested.Kernel S A) : Simulation.Kernel S A :=
  fun s a => ofRegular (p s a)

lemma ofRegular_joint (π : Regularity.Law A) (p : A → Regularity.Law S) :
    ofRegular (Nested.joint π p) = CVaR.joint (ofRegular π) (fun a => ofRegular (p a)) := rfl

/-- Every simulated nested envelope risk equals the main model's compact-primal risk. -/
theorem risk_eq_nested (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Nested.Policy S A) (p : Nested.Kernel S A) (n h : ℕ) (s : S) :
    Simulation.risk α c (ofPolicy π) (ofKernel p) n h s = Nested.risk α c π p n h s := by
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
    rw [Simulation.risk, Nested.risk_step_eq_primal α ha ha1 c hc π p n h s]
    change CVaR.value (ofRegular (Nested.joint (π h s) (p s))) α
      (fun x => c h s x.1 + Simulation.risk α c (ofPolicy π) (ofKernel p) n (h+1) x.2) = _
    rw [value_eq_regular α ha ha1]
    congr 1
    funext x
    rw [ih]

/-- Corollary 5.4 directly on the source's physical-state Markov comparator. -/
theorem nested_nominal_simulation (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Nested.Policy S A) (p q : Nested.Kernel S A) (H : ℕ) (s₀ : S) :
    Nested.risk α c π p (H+1) 0 s₀-Nested.risk α c π q (H+1) 0 s₀ ≤
      ∑ h ∈ Finset.range H, ((H-h : ℕ) : ℝ)*(α⁻¹)^(h+1) *
        ∑ s, (Simulation.occupancy (Simulation.nominal (ofPolicy π) (ofKernel p))
          (Simulation.dirac s₀) h).mass s *
            ∑ a, π h s a * CVaR.tv (ofRegular (p s a)) (ofRegular (q s a)) := by
  have hs := Simulation.nominal_simulation α ha ha1 c hc (ofPolicy π) (ofKernel p) (ofKernel q) H s₀
  rw [risk_eq_nested α ha ha1 c hc π p, risk_eq_nested α ha ha1 c hc π q] at hs
  exact hs

/-- Corollary C.2 directly on the source's physical-state Markov comparator. -/
theorem nested_uniform_fixed_policy_perturbation [Nonempty S] [Nonempty A]
    (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Nested.Policy S A) (p q : Nested.Kernel S A) (n h : ℕ) (s : S) :
    |Nested.risk α c π p n h s-Nested.risk α c π q n h s| ≤
      (n : ℝ)*((n : ℝ)-1)/(2*α)*Simulation.maxRowTV (ofKernel p) (ofKernel q) := by
  have hs := Simulation.uniform_fixed_policy_perturbation α ha ha1 c hc
    (ofPolicy π) (ofKernel p) (ofKernel q) n h s
  rwa [risk_eq_nested α ha ha1 c hc π p, risk_eq_nested α ha ha1 c hc π q] at hs


/-- The exact local error from Lemma 5.3, in the source's unrestricted-primal notation. -/
def sourceLocalError (α : ℝ) (c : ℕ → S → A → ℝ)
    (π : Nested.Policy S A) (p q : Nested.Kernel S A) (n h : ℕ) (s : S) : ℝ :=
  |Regularity.primalCVaR α (Nested.joint (π h s) (p s))
      (fun x => c h s x.1 + Nested.risk α c π q n (h+1) x.2) -
   Regularity.primalCVaR α (Nested.joint (π h s) (q s))
      (fun x => c h s x.1 + Nested.risk α c π q n (h+1) x.2)|

lemma localError_eq_nested (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Nested.Policy S A) (p q : Nested.Kernel S A) (n h : ℕ) (s : S) :
    Simulation.localError α c (ofPolicy π) (ofKernel p) (ofKernel q) n h s =
      sourceLocalError α c π p q n h s := by
  change |CVaR.value (ofRegular (Nested.joint (π h s) (p s))) α
      (fun x => c h s x.1 + Simulation.risk α c (ofPolicy π) (ofKernel q) n (h+1) x.2) -
    CVaR.value (ofRegular (Nested.joint (π h s) (q s))) α
      (fun x => c h s x.1 + Simulation.risk α c (ofPolicy π) (ofKernel q) n (h+1) x.2)| = _
  simp_rw [value_eq_regular α ha ha1, risk_eq_nested α ha ha1 c hc π q]
  rfl

/-- Lemma 5.3, fully transported to the source's common nested-risk semantics. -/
theorem nested_lemma_5_3 (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (π : Nested.Policy S A) (p q : Nested.Kernel S A) (H : ℕ) (s₀ : S) :
    ∃ d : ℕ → CVaR.Law S, (d 0).mass s₀ = 1 ∧
      (Nested.risk α c π p (H+1) 0 s₀-Nested.risk α c π q (H+1) 0 s₀ ≤
        ∑ h ∈ Finset.range H, CVaR.expect (d h).mass
          (sourceLocalError α c π p q (H+1-(h+1)) h)) ∧
      (Nested.risk α c π p (H+1) 0 s₀-Nested.risk α c π q (H+1) 0 s₀ ≤
        ∑ h ∈ Finset.range H, ((H-h : ℕ) : ℝ)/α *
          ∑ s, (d h).mass s * ∑ a, π h s a * CVaR.tv (ofRegular (p s a)) (ofRegular (q s a))) ∧
      (∀ h s a, (d h).mass s*π h s a ≤
        (α⁻¹)^h*((Simulation.occupancy (Simulation.nominal (ofPolicy π) (ofKernel p))
          (Simulation.dirac s₀) h).mass s*π h s a)) := by
  obtain ⟨d, hi, he, htv, hdom⟩ := Simulation.lemma_5_3 α ha ha1 c hc
    (ofPolicy π) (ofKernel p) (ofKernel q) H s₀
  rw [risk_eq_nested α ha ha1 c hc π p, risk_eq_nested α ha ha1 c hc π q] at he htv
  have heps (h : ℕ) : Simulation.epsilon α c (ofPolicy π) (ofKernel p) (ofKernel q) (H+1) h =
      sourceLocalError α c π p q (H+1-(h+1)) h := by
    funext s
    exact localError_eq_nested α ha ha1 c hc π p q _ h s
  simp_rw [heps] at he
  exact ⟨d, hi, he, htv, hdom⟩


lemma action_value (π : CVaR.Law A) (p : A → CVaR.Law S)
    (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1) (c : A → ℝ) :
    CVaR.value (CVaR.joint π p) α (fun x => c x.1) = CVaR.value π α c := by
  rw [CVaR.value_eq_primal_inf _ ha ha1, CVaR.value_eq_primal_inf _ ha ha1]
  have he : CVaR.primal (CVaR.joint π p) α (fun x => c x.1) = CVaR.primal π α c := by
    funext z
    rw [Simulation.primal_action_only, CVaR.primal_eq]
    rfl
  rw [he]

def tighteningPolicy (p : Tightening.Policy) : Nested.Policy Unit Tightening.Action :=
  fun _ _ => toRegular (tighteningLaw p)

def tighteningKernel : Nested.Kernel Unit Tightening.Action :=
  fun _ _ => toRegular (Simulation.dirac ())

def tighteningCost (t : ℝ) : ℕ → Unit → Tightening.Action → ℝ :=
  fun _ _ => Tightening.cost t

def tighteningReward : ℕ → Unit → Tightening.Action → ℝ :=
  fun _ _ => Tightening.reward

/-- The actual one-state, one-stage main-model risk is exactly the obstruction risk. -/
theorem tightening_nested_risk (α t : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (p : Tightening.Policy) :
    Nested.risk α (tighteningCost t) (tighteningPolicy p) tighteningKernel 1 0 () =
      Tightening.risk α t p := by
  have hc : ∀ h s a, tighteningCost t h s a ∈ Set.Icc 0 1 :=
    fun _ _ a => (Tightening.model_bounds t ht ht1).1 a
  rw [← risk_eq_nested α ha ha1 (tighteningCost t) hc (tighteningPolicy p) tighteningKernel]
  change CVaR.value (CVaR.joint (tighteningLaw p) (fun _ => Simulation.dirac ())) α
    (fun x => Tightening.cost t x.1 + 0) = _
  simp only [add_zero]
  rw [action_value _ _ α ha ha1, tightening_risk_eq_value α t ha ha1]

/-- The expected reward of the same one-stage main model is the high-action mass. -/
theorem tightening_nested_reward (p : Tightening.Policy) :
    Nested.reward tighteningReward (tighteningPolicy p) tighteningKernel 1 0 () =
      Tightening.value p := by
  change (∑ a, p.prob a * (Tightening.reward a + ∑ _s : Unit, _ * 0)) = _
  simpa only [mul_zero, Finset.sum_const_zero, add_zero] using Tightening.reward_expectation p

/-- The construction represents every randomized one-stage physical-state policy row. -/
theorem every_one_stage_policy (π : Nested.Policy Unit Tightening.Action) :
    ∃ p : Tightening.Policy, ∀ a, tighteningPolicy p 0 () a = π 0 () a := by
  obtain ⟨p, hp⟩ := Tightening.every_action_law (fun a => π 0 () a)
    (π 0 ()).property.1 (π 0 ()).property.2
  refine ⟨p, ?_⟩
  intro a
  exact congrFun hp a


/-- Conversely, arbitrary main-model policies have exactly the same one-stage
risk/reward behavior as one of the construction's three-action policies. -/
theorem every_one_stage_behavior (α t : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (π : Nested.Policy Unit Tightening.Action) :
    ∃ p : Tightening.Policy,
      Nested.risk α (tighteningCost t) π tighteningKernel 1 0 () = Tightening.risk α t p ∧
      Nested.reward tighteningReward π tighteningKernel 1 0 () = Tightening.value p := by
  obtain ⟨p, hp⟩ := every_one_stage_policy π
  have hπ : π 0 () = tighteningPolicy p 0 () := by
    apply Subtype.ext
    funext a
    exact (hp a).symm
  refine ⟨p, ?_, ?_⟩
  · rw [← tightening_nested_risk α t ha ha1 ht ht1 p]
    simp only [Nested.risk, hπ]
  · rw [← tightening_nested_reward p]
    simp only [Nested.reward, hπ]

end
end Paper36.RiskBridge
