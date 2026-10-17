import Paper36.Regularity
import Mathlib.Data.Fintype.Lattice

/-! The source's randomized physical-state Markov model and its compact risk recursion. -/
namespace Paper36.Nested
open Set Paper36.Regularity
noncomputable section
variable {S A : Type*} [Fintype S] [Fintype A]

abbrev Kernel (S A : Type*) [Fintype S] := S → A → Law S
abbrev Policy (S A : Type*) [Fintype A] := ℕ → S → Law A

def pure (a : A) : Law A := by
  classical
  exact stdSimplex.vertex a

def joint (l : Law A) (q : A → Law S) : Law (A × S) :=
  ⟨fun x => l x.1 * q x.1 x.2,
   (fun x => mul_nonneg (l.property.1 _) ((q _).property.1 _)), by
    simp [Fintype.sum_prod_type, ← Finset.mul_sum, stdSimplex.sum_eq_one]⟩

lemma continuous_policy_row (h : ℕ) (s : S) :
    Continuous (fun π : Policy S A => π h s) :=
  (continuous_apply s).comp (continuous_apply h)

lemma continuous_kernel_row (s : S) (a : A) :
    Continuous (fun q : Kernel S A => q s a) :=
  (continuous_apply a).comp (continuous_apply s)

lemma continuous_joint : Continuous (fun p : Law A × (A → Law S) => joint p.1 p.2) := by
  unfold joint
  apply Continuous.subtype_mk
  apply continuous_pi
  intro x
  exact ((continuous_law_apply x.1).comp continuous_fst).mul
    ((continuous_law_apply x.2).comp ((continuous_apply x.1).comp continuous_snd))

/-- `n` stages remain, and `h` is the current absolute stage. All action randomness is inside CVaR. -/
def risk (α : ℝ) (c : ℕ → S → A → ℝ) (π : Policy S A) (q : Kernel S A) :
    ℕ → ℕ → S → ℝ
  | 0, _, _ => 0
  | n+1, h, s => compactCVaR α (n+1 : ℕ) (joint (π h s) (q s))
      (fun x => c h s x.1 + risk α c π q n (h+1) x.2)

/-- Ordinary expected reward (2.1), using the identical physical-state Markov policy. -/
def reward (r : ℕ → S → A → ℝ) (π : Policy S A) (q : Kernel S A) :
    ℕ → ℕ → S → ℝ
  | 0, _, _ => 0
  | n+1, h, s => ∑ a, π h s a * (r h s a + ∑ t, q s a t * reward r π q n (h+1) t)

lemma risk_bounds (α : ℝ) (hα : 0 ≤ α) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, c h s a ∈ Icc 0 1) (π : Policy S A) (q : Kernel S A)
    (n h : ℕ) (s : S) : risk α c π q n h s ∈ Icc 0 (n : ℝ) := by
  induction n generalizing h s with
  | zero => simp [risk]
  | succ n ih =>
    constructor
    · exact compactCVaR_nonneg α _ hα (by positivity) _ _
    · apply compactCVaR_le_bound α _ (by positivity)
      intro x
      have hx := (ih (h+1) x.2).2
      have hc' := (hc h s x.1).2
      push_cast
      linarith

/-- Every compact-threshold risk in the recursion equals the unrestricted source primal formula. -/
theorem risk_step_eq_primal (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1)
    (π : Policy S A) (q : Kernel S A) (n h : ℕ) (s : S) :
    risk α c π q (n+1) h s = primalCVaR α (joint (π h s) (q s))
      (fun x => c h s x.1 + risk α c π q n (h+1) x.2) := by
  apply compactCVaR_eq_primalCVaR α _ hα hα1 (by positivity)
  intro x
  have hr := risk_bounds α hα.le c hc π q n (h+1) x.2
  have hc' := hc h s x.1
  constructor <;> push_cast <;> linarith [hr.1, hr.2, hc'.1, hc'.2]

set_option maxHeartbeats 800000 in
lemma continuous_risk (α : ℝ) (c : ℕ → S → A → ℝ) (n h : ℕ) (s : S) :
    Continuous (fun p : Policy S A × Kernel S A => risk α c p.1 p.2 n h s) := by
  induction n generalizing h s with
  | zero =>
    change Continuous (fun _ : Policy S A × Kernel S A => (0 : ℝ))
    exact continuous_const
  | succ n ih =>
    change Continuous (fun p : Policy S A × Kernel S A =>
      compactCVaR α (n+1 : ℕ) (joint (p.1 h s) (p.2 s))
        (fun x => c h s x.1 + risk α c p.1 p.2 n (h+1) x.2))
    have hj : Continuous (fun p : Policy S A × Kernel S A => joint (p.1 h s) (p.2 s)) :=
      continuous_joint.comp (((continuous_policy_row h s).comp continuous_fst).prodMk
        ((continuous_apply s).comp continuous_snd))
    have hx : Continuous (fun p : Policy S A × Kernel S A =>
        fun x : A × S => c h s x.1 + risk α c p.1 p.2 n (h+1) x.2) := by
      apply continuous_pi
      intro x
      exact continuous_const.add (ih (h+1) x.2)
    have hcomp := (continuous_compactCVaR (Ω := A × S) α (n+1 : ℕ)).comp (hj.prodMk hx)
    simpa only [Function.comp_def] using hcomp

lemma continuous_reward (r : ℕ → S → A → ℝ) (n h : ℕ) (s : S) :
    Continuous (fun p : Policy S A × Kernel S A => reward r p.1 p.2 n h s) := by
  induction n generalizing h s with
  | zero => exact continuous_const
  | succ n ih =>
    unfold reward
    apply continuous_finset_sum
    intro a _
    apply Continuous.mul (((continuous_law_apply a).comp (continuous_policy_row h s)).comp continuous_fst)
    apply continuous_const.add
    apply continuous_finset_sum
    intro t _
    exact (((continuous_law_apply t).comp (continuous_kernel_row s a)).comp continuous_snd).mul
      (ih (h+1) t)

/-- The source's minimum nested risk over the full randomized Markov class. -/
def minimumRisk (α : ℝ) (c : ℕ → S → A → ℝ) (n h : ℕ) (s : S)
    (q : Kernel S A) : ℝ := sInf ((fun π : Policy S A => risk α c π q n h s) '' univ)

lemma continuous_minimumRisk (α : ℝ) (c : ℕ → S → A → ℝ) (n h : ℕ) (s : S) :
    Continuous (minimumRisk α c n h s : Kernel S A → ℝ) := by
  apply isCompact_univ.continuous_sInf
  exact (continuous_risk α c n h s).comp
    (show Continuous (fun p : Kernel S A × Policy S A => (p.2, p.1)) from
      continuous_snd.prodMk continuous_fst)

lemma exists_minimumRisk [Nonempty A] (α : ℝ) (c : ℕ → S → A → ℝ)
    (n h : ℕ) (s : S) (q : Kernel S A) :
    ∃ π : Policy S A, minimumRisk α c n h s q = risk α c π q n h s := by
  haveI : Nonempty (Law A) := ⟨pure (Classical.arbitrary A)⟩
  obtain ⟨π, _, hπ⟩ := isCompact_univ.exists_sInf_image_eq (Set.univ_nonempty)
    (((continuous_risk α c n h s).comp
      (show Continuous (fun π : Policy S A => (π, q)) from
        continuous_id.prodMk continuous_const)).continuousOn)
  exact ⟨π, hπ⟩

/-- Lemma 2.1 on any nonempty closed prior support in the kernel simplex. -/
theorem uniform_margin [Nonempty A] (α : ℝ) (c : ℕ → S → A → ℝ)
    (n : ℕ) (s : S) (Q : Set (Kernel S A)) (hclosed : IsClosed Q) (hne : Q.Nonempty)
    (τ : ℝ) (hstrict : ∀ q ∈ Q, minimumRisk α c n 0 s q < τ) :
    0 < τ - sSup (minimumRisk α c n 0 s '' Q) ∧
      ∀ q ∈ Q, τ - sSup (minimumRisk α c n 0 s '' Q) ≤ τ - minimumRisk α c n 0 s q := by
  exact automatic_uniform_margin Q hclosed.isCompact hne _
    (continuous_minimumRisk α c n 0 s).continuousOn τ hstrict

/-- The exact constrained Markov comparator (2.5) exists whenever feasible. -/
theorem exists_constrained_optimum (α : ℝ) (c r : ℕ → S → A → ℝ)
    (n h : ℕ) (s : S) (q : Kernel S A) (τ : ℝ)
    (hne : ∃ π : Policy S A, risk α c π q n h s ≤ τ) :
    ∃ π : Policy S A, risk α c π q n h s ≤ τ ∧
      ∀ π', risk α c π' q n h s ≤ τ → reward r π' q n h s ≤ reward r π q n h s := by
  have hcont : Continuous (fun π : Policy S A => risk α c π q n h s) :=
    (continuous_risk α c n h s).comp
      (show Continuous (fun π : Policy S A => (π, q)) from
        continuous_id.prodMk continuous_const)
  have hcontR : Continuous (fun π : Policy S A => reward r π q n h s) :=
    (continuous_reward r n h s).comp
      (show Continuous (fun π : Policy S A => (π, q)) from
        continuous_id.prodMk continuous_const)
  exact (isClosed_le hcont continuous_const).isCompact.exists_isMaxOn hne hcontR.continuousOn

lemma risk_congr (α : ℝ) (c : ℕ → S → A → ℝ) (q : Kernel S A)
    (π π' : Policy S A) (n h : ℕ) (heq : ∀ j, h ≤ j → π j = π' j) (s : S) :
    risk α c π q n h s = risk α c π' q n h s := by
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
    simp only [risk, heq h le_rfl]
    congr 1
    funext x
    rw [ih (h+1) (fun j hj => heq j (by omega)) x.2]

lemma objective_joint (α : ℝ) (l : Law A) (q : A → Law S)
    (X : A → S → ℝ) (z : ℝ) :
    objective α (joint l q) (fun x => X x.1 x.2) z =
      ∑ a, l a * objective α (q a) (X a) z := by
  simp only [objective, expectation, joint, Subtype.coe_mk,
    Fintype.sum_prod_type, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    law_sum l, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro s _
  change α⁻¹ * ((l a * q a s) * max (X a s - z) 0) = _
  ring

lemma compactCVaR_joint_lower (α B : ℝ) (hB : 0 ≤ B) (l : Law A) (q : A → Law S)
    (X : A → S → ℝ) (b : ℝ) (hb : ∀ a, b ≤ compactCVaR α B (q a) (X a)) :
    b ≤ compactCVaR α B (joint l q) (fun x => X x.1 x.2) := by
  apply le_compactCVaR α B hB
  intro z hz
  rw [objective_joint]
  calc
    b = ∑ a, l a * b := by simp [← Finset.sum_mul, law_sum l]
    _ ≤ ∑ a, l a * objective α (q a) (X a) z := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left ((hb a).trans (compactCVaR_le α B hB _ _ hz))
        (l.property.1 a)

lemma compactCVaR_joint_pure (α B : ℝ) (a : A) (q : A → Law S) (X : A → S → ℝ) :
    compactCVaR α B (joint (pure a) q) (fun x => X x.1 x.2) =
      compactCVaR α B (q a) (X a) := by
  classical
  unfold compactCVaR
  congr 1
  ext y
  simp only [mem_image]
  have heq : ∀ z, objective α (joint (pure a) q) (fun x => X x.1 x.2) z =
      objective α (q a) (X a) z := by
    intro z
    rw [objective_joint]
    simp [pure, stdSimplex.vertex, Pi.single_apply]
  simp only [heq]

end
end Paper36.Nested
