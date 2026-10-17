import Paper36.CVaR
import Lean.Elab.Tactic.Omega

/-! Actual adverse laws, distorted occupancies, and finite-horizon simulation
for randomized physical-state Markov policies. Stage indices start at zero. -/
namespace Paper36.Simulation
open scoped BigOperators
open Paper36.CVaR
noncomputable section

variable {S A : Type*} [Fintype S] [Fintype A]
abbrev Kernel (S A : Type*) [Fintype S] := S → A → Law S
abbrev Policy (S A : Type*) [Fintype A] := ℕ → S → Law A

/-- Source recursion (2.3), using the full action--successor joint law. -/
def risk (α : ℝ) (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A) :
    ℕ → ℕ → S → ℝ
  | 0, _, _ => 0
  | n+1, h, s => value (joint (π h s) (p s)) α
      (fun x => c h s x.1 + risk α c π p n (h+1) x.2)

lemma risk_bounds (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Policy S A) (p : Kernel S A) (n h : ℕ) (s : S) :
    0 ≤ risk α c π p n h s ∧ risk α c π p n h s ≤ n := by
  induction n generalizing h s with
  | zero => simp [risk]
  | succ n ih =>
    apply value_bounds _ ha ha1
    · intro x
      exact add_nonneg (hc h s x.1).1 (ih (h+1) x.2).1
    · intro x
      have := (ih (h+1) x.2).2
      have := (hc h s x.1).2
      push_cast
      linarith

/-- A CVaR optimizer gives the directional continuation inequality. -/
lemma optimizer_difference (P : Law S) (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (X Y : S → ℝ) (w : S → ℝ) (hw : Envelope P α w)
    (hopt : value P α X = expect w X) :
    value P α X - value P α Y ≤ expect w (fun i => X i-Y i) := by
  have hy := expect_le_value P ha ha1 hw Y
  rw [hopt]
  simp only [expect, mul_sub, Finset.sum_sub_distrib] at *
  linarith

/-- An optimizing adverse joint action--successor law, not an assumed witness. -/
def adverse (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (n h : ℕ) (s : S) : Law (A × S) :=
  let ex := exists_optimizer (joint (π h s) (p s)) ha ha1
    (fun x => c h s x.1 + risk α c π p n (h+1) x.2)
  ⟨Classical.choose ex, (Classical.choose_spec ex).1.1,
    (Classical.choose_spec ex).1.2.2⟩

lemma adverse_envelope (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (n h : ℕ) (s : S) :
    Envelope (joint (π h s) (p s)) α (adverse α ha ha1 c π p n h s).mass :=
  (Classical.choose_spec (exists_optimizer (joint (π h s) (p s)) ha ha1
    (fun x => c h s x.1 + risk α c π p n (h+1) x.2))).1

lemma adverse_optimal (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (n h : ℕ) (s : S) :
    risk α c π p (n+1) h s = expect (adverse α ha ha1 c π p n h s).mass
      (fun x => c h s x.1 + risk α c π p n (h+1) x.2) :=
  (Classical.choose_spec (exists_optimizer (joint (π h s) (p s)) ha ha1
    (fun x => c h s x.1 + risk α c π p n (h+1) x.2))).2

/-- State marginal of a joint action--successor law. -/
def stateMarginal (P : Law (A × S)) : Law S where
  mass t := ∑ a, P.mass (a,t)
  nonneg t := Finset.sum_nonneg fun a _ => P.nonneg (a,t)
  total := by rw [Finset.sum_comm, ← Fintype.sum_prod_type]; exact P.total

/-- Pushing a genuine probability law through a probability kernel preserves mass. -/
def advance (d : Law S) (K : S → Law S) : Law S where
  mass t := ∑ s, d.mass s * (K s).mass t
  nonneg t := Finset.sum_nonneg fun s _ => mul_nonneg (d.nonneg s) ((K s).nonneg t)
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, Law.total, mul_one]

def dirac (s₀ : S) : Law S := by
  classical
  exact ⟨fun s => if s=s₀ then 1 else 0, by intro s; dsimp; split <;> norm_num, by simp⟩

/-- Forward state occupancy under arbitrary time-dependent probability kernels. -/
def occupancy (K : ℕ → S → Law S) (d₀ : Law S) : ℕ → Law S
  | 0 => d₀
  | h+1 => advance (occupancy K d₀ h) (K h)

lemma advance_expect (d : Law S) (K : S → Law S) (f : S → ℝ) :
    expect (advance d K).mass f = expect d.mass (fun s => expect (K s).mass f) := by
  simp only [expect, advance, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

lemma stateMarginal_expect (P : Law (A × S)) (f : S → ℝ) :
    expect (stateMarginal P).mass f = expect P.mass (fun x => f x.2) := by
  simp only [expect, stateMarginal, Finset.sum_mul, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma expect_dirac (s₀ : S) (f : S → ℝ) : expect (dirac s₀).mass f = f s₀ := by
  classical
  simp [expect, dirac]

/-- Kernel domination propagates without dividing by any nominal probability. -/
theorem occupancy_domination (K L : ℕ → S → Law S) (d₀ : Law S) (κ : ℝ)
    (hκ : 0 ≤ κ) (hstep : ∀ h s t, (K h s).mass t ≤ κ*(L h s).mass t)
    (h : ℕ) (s : S) :
    (occupancy K d₀ h).mass s ≤ κ^h * (occupancy L d₀ h).mass s := by
  induction h generalizing s with
  | zero => simp [occupancy]
  | succ h ih =>
    change (∑ t, (occupancy K d₀ h).mass t * (K h t).mass s) ≤
      κ^(h+1) * ∑ t, (occupancy L d₀ h).mass t * (L h t).mass s
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    calc
      _ ≤ (κ^h*(occupancy L d₀ h).mass t) * (κ*(L h t).mass s) :=
        mul_le_mul (ih t) (hstep h t s) ((K h t).nonneg s)
          (mul_nonneg (pow_nonneg hκ _) ((occupancy L d₀ h).nonneg t))
      _ = κ^(h+1) * ((occupancy L d₀ h).mass t * (L h t).mass s) := by
        rw [pow_succ]
        ring

/-- The nominal state transition, with the policy row left undistorted. -/
def nominal (π : Policy S A) (p : Kernel S A) (h : ℕ) (s : S) : Law S :=
  stateMarginal (joint (π h s) (p s))

/-- For total horizon H, use the actual CVaR optimizer for its remaining continuation. -/
def adverseKernel (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (H h : ℕ) (s : S) : Law S :=
  stateMarginal (adverse α ha ha1 c π p (H-(h+1)) h s)

lemma adverseKernel_domination (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (H h : ℕ) (s t : S) :
    (adverseKernel α ha ha1 c π p H h s).mass t ≤ α⁻¹*(nominal π p h s).mass t := by
  change (∑ a, (adverse α ha ha1 c π p (H-(h+1)) h s).mass (a,t)) ≤
    α⁻¹ * ∑ a, (joint (π h s) (p s)).mass (a,t)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simpa only [div_eq_mul_inv, mul_comm] using
    (adverse_envelope α ha ha1 c π p (H-(h+1)) h s).2.1 (a,t)

/-- The exact source local error, evaluated at the q-model continuation. -/
def localError (α : ℝ) (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A)
    (n h : ℕ) (s : S) : ℝ :=
  |value (joint (π h s) (p s)) α
      (fun x => c h s x.1 + risk α c π q n (h+1) x.2) -
   value (joint (π h s) (q s)) α
      (fun x => c h s x.1 + risk α c π q n (h+1) x.2)|

/-- The one-step recursion C.3 is derived from the optimizing adverse law. -/
theorem simulation_step (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A)
    (n h : ℕ) (s : S) :
    risk α c π p (n+1) h s - risk α c π q (n+1) h s ≤
      expect (stateMarginal (adverse α ha ha1 c π p n h s)).mass
        (fun t => risk α c π p n (h+1) t-risk α c π q n (h+1) t) +
      localError α c π p q n h s := by
  have hd := optimizer_difference (joint (π h s) (p s)) α ha ha1
    (fun x => c h s x.1 + risk α c π p n (h+1) x.2)
    (fun x => c h s x.1 + risk α c π q n (h+1) x.2)
    (adverse α ha ha1 c π p n h s).mass
    (adverse_envelope α ha ha1 c π p n h s)
    (adverse_optimal α ha ha1 c π p n h s)
  rw [stateMarginal_expect]
  have he : (fun x : A × S => (c h s x.1 + risk α c π p n (h+1) x.2) -
      (c h s x.1 + risk α c π q n (h+1) x.2)) =
      (fun x => risk α c π p n (h+1) x.2-risk α c π q n (h+1) x.2) := by
    funext x; ring
  rw [he] at hd
  have hab := le_abs_self (value (joint (π h s) (p s)) α
    (fun x => c h s x.1 + risk α c π q n (h+1) x.2) -
    value (joint (π h s) (q s)) α
    (fun x => c h s x.1 + risk α c π q n (h+1) x.2))
  unfold localError
  change value _ _ _ - value _ _ _ ≤ _
  change value _ _ _ - value _ _ _ ≤ _ at hd
  linarith

/-- Bellman risk difference at absolute stage h of a total horizon H. -/
def delta (α : ℝ) (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A)
    (H h : ℕ) (s : S) : ℝ := risk α c π p (H-h) h s-risk α c π q (H-h) h s

def epsilon (α : ℝ) (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A)
    (H h : ℕ) (s : S) : ℝ := localError α c π p q (H-(h+1)) h s

lemma delta_step (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A)
    (H h : ℕ) (hh : h < H) (s : S) :
    delta α c π p q H h s ≤ expect (adverseKernel α ha ha1 c π p H h s).mass
      (delta α c π p q H (h+1)) + epsilon α c π p q H h s := by
  have he : H-h = (H-(h+1))+1 := by omega
  simpa only [delta, epsilon, adverseKernel, he] using
    simulation_step α ha ha1 c π p q (H-(h+1)) h s

/-- A derived local inequality telescopes along its actual probability occupancies. -/
lemma unroll (K : ℕ → S → Law S) (d₀ : Law S) (δ e : ℕ → S → ℝ)
    (H : ℕ) (hstep : ∀ h, h < H → ∀ s,
      δ h s ≤ expect (K h s).mass (δ (h+1)) + e h s) :
    expect d₀.mass (δ 0) ≤ expect (occupancy K d₀ H).mass (δ H) +
      ∑ h ∈ Finset.range H, expect (occupancy K d₀ h).mass (e h) := by
  have hs : ∀ n, n ≤ H → expect d₀.mass (δ 0) ≤
      expect (occupancy K d₀ n).mass (δ n) +
        ∑ h ∈ Finset.range n, expect (occupancy K d₀ h).mass (e h) := by
    intro n
    induction n with
    | zero => simp [occupancy]
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hm := expect_mono (occupancy K d₀ n).nonneg (hstep n (by omega))
      have hadd : expect (occupancy K d₀ n).mass
          (fun s => expect (K n s).mass (δ (n+1)) + e n s) =
          expect (occupancy K d₀ (n+1)).mass (δ (n+1)) +
          expect (occupancy K d₀ n).mass (e n) := by
        rw [occupancy, advance_expect]
        simp only [expect, mul_add, Finset.sum_add_distrib]
      rw [hadd] at hm
      rw [Finset.sum_range_succ]
      linarith
  exact hs H le_rfl

/-- Local-error distorted simulation, initially including the terminal zero-error step. -/
theorem distorted_simulation_full (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A)
    (H : ℕ) (s₀ : S) :
    let d := occupancy (adverseKernel α ha ha1 c π p H) (dirac s₀)
    risk α c π p H 0 s₀-risk α c π q H 0 s₀ ≤
      ∑ h ∈ Finset.range H, expect (d h).mass (epsilon α c π p q H h) := by
  dsimp
  have hu := unroll (adverseKernel α ha ha1 c π p H) (dirac s₀)
    (delta α c π p q H) (epsilon α c π p q H) H
    (fun h hh s => delta_step α ha ha1 c π p q H h hh s)
  rw [expect_dirac] at hu
  have hz : delta α c π p q H H = fun _ => 0 := by funext s; simp [delta, risk]
  rw [hz, expect_const (occupancy (adverseKernel α ha ha1 c π p H) (dirac s₀) H).total] at hu
  simpa only [delta, Nat.sub_zero, zero_add] using hu

/-- Equation 5.6, including the undistorted current action probability. -/
theorem distorted_action_domination (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (H h : ℕ) (s₀ s : S) (a : A) :
    (occupancy (adverseKernel α ha ha1 c π p H) (dirac s₀) h).mass s * (π h s).mass a ≤
      (α⁻¹)^h * ((occupancy (nominal π p) (dirac s₀) h).mass s * (π h s).mass a) := by
  have hd := occupancy_domination (adverseKernel α ha ha1 c π p H)
    (nominal π p) (dirac s₀) (α⁻¹) (inv_nonneg.mpr ha.le)
    (fun h s t => adverseKernel_domination α ha ha1 c π p H h s t) h s
  have hh := mul_le_mul_of_nonneg_right hd ((π h s).nonneg a)
  simpa only [mul_assoc] using hh


lemma primal_action_only (π : Law A) (p : A → Law S) (α : ℝ) (c : A → ℝ) (z : ℝ) :
    primal (joint π p) α (fun x => c x.1) z =
      z + (∑ a, π.mass a * max (c a-z) 0) / α := by
  rw [primal_eq, expect_joint]
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  change π.mass a * expect (p a).mass (fun _ => max (c a-z) 0) = _
  rw [expect_const (p a).total]

/-- With no continuation, successor transitions cannot affect stage cost risk. -/
lemma action_only (π : Law A) (p q : A → Law S) (α : ℝ)
    (ha : 0 < α) (ha1 : α ≤ 1) (c : A → ℝ) :
    value (joint π p) α (fun x => c x.1) = value (joint π q) α (fun x => c x.1) := by
  rw [value_eq_primal_inf _ ha ha1, value_eq_primal_inf _ ha ha1]
  have he : primal (joint π p) α (fun x => c x.1) =
      primal (joint π q) α (fun x => c x.1) := by
    funext z
    rw [primal_action_only, primal_action_only]
  rw [he]

lemma localError_zero (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A) (h : ℕ) (s : S) :
    localError α c π p q 0 h s = 0 := by
  simp only [localError, risk, add_zero]
  rw [action_only (π h s) (p s) (q s) α ha ha1 (c h s), sub_self, abs_zero]

/-- Equation 5.4 for every positive horizon H+1, omitting its terminal zero error. -/
theorem distorted_simulation (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Policy S A) (p q : Kernel S A)
    (H : ℕ) (s₀ : S) :
    let d := occupancy (adverseKernel α ha ha1 c π p (H+1)) (dirac s₀)
    risk α c π p (H+1) 0 s₀-risk α c π q (H+1) 0 s₀ ≤
      ∑ h ∈ Finset.range H, expect (d h).mass (epsilon α c π p q (H+1) h) := by
  have hfull := distorted_simulation_full α ha ha1 c π p q (H+1) s₀
  dsimp at *
  rw [Finset.sum_range_succ] at hfull
  have he : epsilon α c π p q (H+1) H = fun _ => 0 := by
    funext s
    simp only [epsilon, Nat.sub_self, localError_zero α ha ha1]
  rw [he, expect_const (occupancy (adverseKernel α ha ha1 c π p (H+1)) (dirac s₀) H).total,
    add_zero] at hfull
  exact hfull

lemma localError_tv (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Policy S A) (p q : Kernel S A) (n h : ℕ) (s : S) :
    localError α c π p q n h s ≤ (n : ℝ)/α *
      ∑ a, (π h s).mass a * tv (p s a) (q s a) :=
  value_joint_tv (π h s) (p s) (q s) ha ha1 (Nat.cast_nonneg n) (c h s)
    (risk α c π q n (h+1))
    (fun t => (risk_bounds α ha ha1 c hc π q n (h+1) t).1)
    (fun t => (risk_bounds α ha ha1 c hc π q n (h+1) t).2)

/-- Equation 5.5, from the actual distorted laws and the proven local TV bound. -/
theorem distorted_simulation_tv (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Policy S A) (p q : Kernel S A) (H : ℕ) (s₀ : S) :
    let d := occupancy (adverseKernel α ha ha1 c π p (H+1)) (dirac s₀)
    risk α c π p (H+1) 0 s₀-risk α c π q (H+1) 0 s₀ ≤
      ∑ h ∈ Finset.range H, ((H-h : ℕ) : ℝ)/α *
        ∑ s, (d h).mass s * ∑ a, (π h s).mass a * tv (p s a) (q s a) := by
  dsimp
  apply (distorted_simulation α ha ha1 c π p q H s₀).trans
  apply Finset.sum_le_sum
  intro h _
  have he : H+1-(h+1) = H-h := by omega
  have hm := expect_mono
    (occupancy (adverseKernel α ha ha1 c π p (H+1)) (dirac s₀) h).nonneg
    (fun s => localError_tv α ha ha1 c hc π p q (H-h) h s)
  simpa only [epsilon, he, expect, Finset.mul_sum, mul_left_comm] using hm

/-- Corollary 5.4: the source coefficient is (H-h) alpha^(-(h+1)) in zero-based time. -/
theorem nominal_simulation (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Policy S A) (p q : Kernel S A) (H : ℕ) (s₀ : S) :
    risk α c π p (H+1) 0 s₀-risk α c π q (H+1) 0 s₀ ≤
      ∑ h ∈ Finset.range H, ((H-h : ℕ) : ℝ)*(α⁻¹)^(h+1) *
        ∑ s, (occupancy (nominal π p) (dirac s₀) h).mass s *
          ∑ a, (π h s).mass a * tv (p s a) (q s a) := by
  apply (distorted_simulation_tv α ha ha1 c hc π p q H s₀).trans
  apply Finset.sum_le_sum
  intro h _
  have hm : (∑ s, (occupancy (adverseKernel α ha ha1 c π p (H+1)) (dirac s₀) h).mass s *
      ∑ a, (π h s).mass a * tv (p s a) (q s a)) ≤
      (α⁻¹)^h * ∑ s, (occupancy (nominal π p) (dirac s₀) h).mass s *
        ∑ a, (π h s).mass a * tv (p s a) (q s a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    have hd := mul_le_mul_of_nonneg_right
      (distorted_action_domination α ha ha1 c π p (H+1) h s₀ s a)
      (tv_nonneg (p s a) (q s a))
    simpa only [mul_assoc] using hd
  have hh := mul_le_mul_of_nonneg_left hm (div_nonneg (Nat.cast_nonneg (H-h)) ha.le)
  convert hh using 1 <;> rw [pow_succ] <;> simp only [div_eq_mul_inv] <;> ring

/-- Uniform fixed-policy perturbation derived from Bellman CVaR, not postulated recursion. -/
theorem uniform_perturbation_bound (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Policy S A) (p q : Kernel S A) (D : ℝ) (hD : 0 ≤ D)
    (hrows : ∀ s a, tv (p s a) (q s a) ≤ D) (n h : ℕ) (s : S) :
    |risk α c π p n h s-risk α c π q n h s| ≤
      (n : ℝ)*((n : ℝ)-1)/(2*α)*D := by
  induction n generalizing h s with
  | zero => simp [risk]
  | succ n ih =>
    let P := joint (π h s) (p s)
    let Q := joint (π h s) (q s)
    let X : A × S → ℝ := fun x => c h s x.1 + risk α c π p n (h+1) x.2
    let Y : A × S → ℝ := fun x => c h s x.1 + risk α c π q n (h+1) x.2
    have hcont : |value P α X-value P α Y| ≤ (n : ℝ)*((n : ℝ)-1)/(2*α)*D := by
      apply value_lipschitz P ha ha1
      intro x
      simpa only [X, Y, add_sub_add_left_eq_sub] using ih (h+1) x.2
    have hlocal := localError_tv α ha ha1 c hc π p q n h s
    have hrow : (∑ a, (π h s).mass a * tv (p s a) (q s a)) ≤ D := by
      calc
        _ ≤ ∑ a, (π h s).mass a * D :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hrows s a) ((π h s).nonneg a)
        _ = D := expect_const (π h s).total D
    have hlocal' : |value P α Y-value Q α Y| ≤ (n : ℝ)/α*D :=
      hlocal.trans (mul_le_mul_of_nonneg_left hrow (div_nonneg (Nat.cast_nonneg n) ha.le))
    have htri := abs_sub_le (value P α X) (value P α Y) (value Q α Y)
    have hcoef : (n : ℝ)*((n : ℝ)-1)/(2*α)*D + (n : ℝ)/α*D =
        ((n+1 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)-1)/(2*α)*D := by
      push_cast
      field_simp
      <;> ring
    change |value P α X-value Q α Y| ≤ _
    rw [← hcoef]
    linarith

/-- Maximum transition-row TV, with the source's finite tabular indexing. -/
def maxRowTV (p q : Kernel S A) : ℝ := sSup (Set.range (fun x : S × A => tv (p x.1 x.2) (q x.1 x.2)))

lemma le_maxRowTV (p q : Kernel S A) (s : S) (a : A) :
    tv (p s a) (q s a) ≤ maxRowTV p q :=
  le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self (s,a))

/-- Corollary C.2, pointwise equivalent to its stated supremum-norm bound. -/
theorem uniform_fixed_policy_perturbation [Nonempty S] [Nonempty A]
    (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Policy S A) (p q : Kernel S A) (n h : ℕ) (s : S) :
    |risk α c π p n h s-risk α c π q n h s| ≤
      (n : ℝ)*((n : ℝ)-1)/(2*α)*maxRowTV p q := by
  have hD : 0 ≤ maxRowTV p q := (tv_nonneg (p (Classical.arbitrary S) (Classical.arbitrary A))
    (q (Classical.arbitrary S) (Classical.arbitrary A))).trans
      (le_maxRowTV p q (Classical.arbitrary S) (Classical.arbitrary A))
  exact uniform_perturbation_bound α ha ha1 c hc π p q (maxRowTV p q) hD
    (le_maxRowTV p q) n h s


/-- Lemma 5.3 with a single concrete family of genuine probability distributions.
The horizon is H+1 and time h=0 corresponds to the paper's stage one. -/
theorem lemma_5_3 (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Policy S A) (p q : Kernel S A) (H : ℕ) (s₀ : S) :
    ∃ d : ℕ → Law S, (d 0).mass s₀ = 1 ∧
      (risk α c π p (H+1) 0 s₀-risk α c π q (H+1) 0 s₀ ≤
        ∑ h ∈ Finset.range H, expect (d h).mass (epsilon α c π p q (H+1) h)) ∧
      (risk α c π p (H+1) 0 s₀-risk α c π q (H+1) 0 s₀ ≤
        ∑ h ∈ Finset.range H, ((H-h : ℕ) : ℝ)/α *
          ∑ s, (d h).mass s * ∑ a, (π h s).mass a * tv (p s a) (q s a)) ∧
      (∀ h s a, (d h).mass s*(π h s).mass a ≤
        (α⁻¹)^h*((occupancy (nominal π p) (dirac s₀) h).mass s*(π h s).mass a)) := by
  refine ⟨occupancy (adverseKernel α ha ha1 c π p (H+1)) (dirac s₀), ?_,
    distorted_simulation α ha ha1 c π p q H s₀,
    distorted_simulation_tv α ha ha1 c hc π p q H s₀, ?_⟩
  · classical
    simp [occupancy, dirac]
  · intro h s a
    exact distorted_action_domination α ha ha1 c π p (H+1) h s₀ s a

end
end Paper36.Simulation
