import Paper36.RareChain
import Paper36.StageRisk

/-! Remark F.1 on the same physical-state graph, with depth-dependent hazards.
Stages are zero-indexed in the recursion; the paper's tail mass after stage h
is `a h`, so the initial transition uses `a 1`. -/
namespace Paper36.LowerBound.Heterogeneous
noncomputable section
open Finset Set Paper36.Regularity
open Paper36.LowerBound

/-- The identical finite probability law in the envelope API. -/
def finiteLaw {Ω : Type*} [Fintype Ω] (P : Law Ω) : Paper36.CVaR.Law Ω :=
  ⟨P, P.property.1, P.property.2⟩

def finitePolicy {S A : Type*} [Fintype A] (π : Nested.Policy S A) : Paper36.Simulation.Policy S A :=
  fun h s => finiteLaw (π h s)

def finiteKernel {S A : Type*} [Fintype S] (q : Nested.Kernel S A) : Paper36.Simulation.Kernel S A :=
  fun s a => finiteLaw (q s a)

theorem finite_joint {S A : Type*} [Fintype S] [Fintype A]
    (l : Law A) (q : A → Law S) :
    Paper36.CVaR.joint (finiteLaw l) (fun a => finiteLaw (q a)) = finiteLaw (Nested.joint l q) := rfl

theorem finite_value_compact {Ω : Type*} [Fintype Ω] (P : Law Ω) {α B : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hB : 0 ≤ B) (X : Ω → ℝ)
    (hX : ∀ i, X i ∈ Set.Icc 0 B) :
    Paper36.CVaR.value (finiteLaw P) α X = compactCVaR α B P X := by
  rw [Paper36.CVaR.value_eq_primal_inf _ hα hα1,
    compactCVaR_eq_primalCVaR α B hα hα1 hB P X hX]
  have heq : Paper36.CVaR.primal (finiteLaw P) α X = objective α P X := by
    funext z
    unfold Paper36.CVaR.primal objective expectation finiteLaw
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    congr 1
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  simp only [primalCVaR, heq]

/-- Compact simplex presentation of the actual stage-dependent source risk. -/
def risk {S A : Type*} [Fintype S] [Fintype A] (a : ℕ → ℝ)
    (c : ℕ → S → A → ℝ) (π : Nested.Policy S A) (q : Nested.Kernel S A) : ℕ → ℕ → S → ℝ
  | 0, _, _ => 0
  | n+1, h, s => compactCVaR (a (h+1)) (n+1 : ℕ) (Nested.joint (π h s) (q s))
      (fun x => c h s x.1 + risk a c π q n (h+1) x.2)

theorem risk_bounds {S A : Type*} [Fintype S] [Fintype A] (a : ℕ → ℝ)
    (ha : ∀ j, 0 < a j ∧ a j ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s u, c h s u ∈ Set.Icc 0 1) (π : Nested.Policy S A) (q : Nested.Kernel S A)
    (n h : ℕ) (s : S) : risk a c π q n h s ∈ Set.Icc 0 (n : ℝ) := by
  induction n generalizing h s with
  | zero => simp [risk]
  | succ n ih =>
    constructor
    · exact compactCVaR_nonneg _ _ (ha (h+1)).1.le (by positivity) _ _
    · apply compactCVaR_le_bound _ _ (by positivity)
      intro x
      have hh := (ih (h+1) x.2).2
      have hcc := (hc h s x.1).2
      push_cast
      linarith

/-- This is exactly `StageRisk.risk`, not an alternative risk functional. -/
theorem stageRisk_bridge {S A : Type*} [Fintype S] [Fintype A] (a : ℕ → ℝ)
    (ha : ∀ j, 0 < a j ∧ a j ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s u, c h s u ∈ Set.Icc 0 1) (π : Nested.Policy S A) (q : Nested.Kernel S A)
    (n h : ℕ) (s : S) :
    Paper36.StageRisk.risk a c (finitePolicy π) (finiteKernel q) n h s = risk a c π q n h s := by
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
    simp only [Paper36.StageRisk.risk, risk, finitePolicy, finiteKernel, finite_joint]
    simp_rw [ih]
    change Paper36.CVaR.value (Paper36.CVaR.joint (finiteLaw (π h s)) (fun u => finiteLaw (q s u)))
      (a (h+1)) (fun x => c h s x.1 + risk a c π q n (h+1) x.2) = _
    rw [finite_joint]
    apply finite_value_compact _ (ha (h+1)).1 (ha (h+1)).2
      (show 0 ≤ ((n+1 : ℕ) : ℝ) by positivity)
    intro x
    have hr := risk_bounds a ha c hc π q n (h+1) x.2
    have hcc := hc h s x.1
    constructor <;> push_cast <;> linarith [hr.1, hr.2, hcc.1, hcc.2]

/-- Hazards are encoded in physical depth states, so the kernel is time homogeneous. -/
def kernel {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ : Bool) : Nested.Kernel (ChainState d) Bool := fun s u =>
  match s with
  | Sum.inl i => if i = 0 then twoPoint (a 1) (ha 1).1.le (ha 1).2
      (successfulNext hd θ u s) failure else Nested.pure s
  | Sum.inr (_,j) => twoPoint (a (j.val+2)) (ha (j.val+2)).1.le (ha (j.val+2)).2
      (successfulNext hd θ u s) failure

/-- Product of the next `n` stage hazards, with the head recurrence exposed. -/
def survival (a : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | h, n+1 => a (h+1)*survival a (h+1) n

@[simp] theorem survival_zero (a : ℕ → ℝ) (h : ℕ) : survival a h 0 = 1 := rfl
@[simp] theorem survival_succ (a : ℕ → ℝ) (h n : ℕ) :
    survival a h (n+1) = a (h+1)*survival a (h+1) n := rfl

theorem survival_pos (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (h n : ℕ) : 0 < survival a h n := by
  induction n generalizing h with
  | zero => simp
  | succ n ih => exact mul_pos (ha (h+1)) (ih (h+1))

theorem survival_le_one (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1) (h n : ℕ) : survival a h n ≤ 1 := by
  induction n generalizing h with
  | zero => simp
  | succ n ih =>
    calc
      survival a h (n+1) ≤ a (h+1)*1 := mul_le_mul_of_nonneg_left (ih (h+1)) (ha (h+1)).1.le
      _ ≤ 1 := by simpa using (ha (h+1)).2

theorem survival_product (a : ℕ → ℝ) (h n : ℕ) :
    survival a h n = ∏ j ∈ Finset.range n, a (h+j+1) := by
  induction n generalizing h with
  | zero => simp
  | succ n ih =>
    rw [survival_succ, Finset.prod_range_succ']
    rw [ih]
    simp only [Nat.add_zero]
    rw [mul_comm (a (h+1))]
    congr 1
    apply prod_congr rfl
    intro j _
    congr 1
    omega

theorem survival_prefix (a : ℕ → ℝ) (n : ℕ) : survival a 0 n = Paper36.Weights.prefixMass a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [survival_product, Paper36.Weights.prefixMass_succ, ← ih, survival_product]
    rw [Finset.prod_range_succ]
    simp only [Nat.zero_add]

theorem absorbing_zero {S A : Type*} [Fintype S] [Fintype A]
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (c : ℕ → S → A → ℝ) (π : Nested.Policy S A) (q : Nested.Kernel S A) (s : S)
    (hc : ∀ h u, c h s u = 0) (hq : ∀ u, q s u = Nested.pure s) (n h : ℕ) :
    risk a c π q n h s = 0 := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    rw [risk]
    apply le_antisymm
    · apply (compactCVaR_le _ (n+1 : ℕ) (by positivity) _ _
        (show (0:ℝ) ∈ Set.Icc 0 ((n+1 : ℕ) : ℝ) from ⟨le_rfl, by positivity⟩)).trans
      rw [Nested.objective_joint (a (h+1)) (π h s) (q s)
        (fun u t => c h s u + risk a c π q n (h+1) t) 0]
      have he (u : A) : objective (a (h+1)) (q s u) (fun t => c h s u + risk a c π q n (h+1) t) 0 = 0 := by
        rw [hq u, hc]
        simp [objective, expectation_pure, ih]
      simp [he]
    · exact compactCVaR_nonneg _ _ (ha (h+1)).1.le (by positivity) _ _

theorem failure_risk {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool) (H n h : ℕ) :
    risk a (chainCost H) π (kernel hd a ha θ) n h failure = 0 := by
  apply absorbing_zero a ha
  · intro h u; simp [chainCost, failure, bad]
  · intro u; simp [kernel, failure]

theorem good_risk {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool) (H n h : ℕ) :
    risk a (chainCost H) π (kernel hd a ha θ) n h good = 0 := by
  apply absorbing_zero a ha
  · intro h u; simp [chainCost, good, bad]
  · intro u; simp [kernel, good]

theorem bad_terminal {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool) :
    risk a (chainCost (d+2)) π (kernel hd a ha θ) 1 (d+1) bad = 1 := by
  simp only [risk, chainCost, and_self, ↓reduceIte, add_zero]
  apply compactCVaR_const _ (ha (d+2)).1 (ha (d+2)).2 (by norm_num) (by norm_num)

theorem step_risk {S A : Type*} [Fintype S] [Fintype A]
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1) (c : ℕ → S → A → ℝ)
    (π : Nested.Policy S A) (q : Nested.Kernel S A) (n h : ℕ) (s v : S)
    (u : A → S) (f : A → Bool) (hc : ∀ b, c h s b = 0)
    (hq : ∀ b, q s b = twoPoint (a (h+1)) (ha (h+1)).1.le (ha (h+1)).2 (u b) v)
    (hu : ∀ b, risk a c π q n (h+1) (u b) = if f b then 1 else 0)
    (hv : risk a c π q n (h+1) v = 0) :
    risk a c π q (n+1) h s = expectation (π h s) (fun b => if f b then 1 else 0) := by
  let x := expectation (π h s) (fun b => if f b then 1 else 0)
  have hx : 0 ≤ x := sum_nonneg fun b _ => mul_nonneg ((π h s).property.1 b) (by cases hf : f b <;> simp [hf])
  have hx1 : x ≤ 1 := by
    calc
      x ≤ expectation (π h s) (fun _ => 1) := expectation_mono _ (fun b => by cases hf : f b <;> simp [hf])
      _ = 1 := expectation_const _ _
  rw [risk]
  have hqfun : q s = fun b => twoPoint (a (h+1)) (ha (h+1)).1.le (ha (h+1)).2 (u b) v := funext hq
  rw [hqfun]
  have hX : (fun y : A × S => c h s y.1 + risk a c π q n (h+1) y.2) =
      (fun y : A × S => risk a c π q n (h+1) y.2) := by funext y; rw [hc, zero_add]
  rw [hX]
  apply compact_bernoulli_of_objective _ _ (ha (h+1)).1 (ha (h+1)).2 (by positivity) hx hx1
  intro z
  exact joint_twoPoint_objective (π h s) (a (h+1)) (ha (h+1)).1.le (ha (h+1)).2 u v
    (risk a c π q n (h+1)) f hu hv z

/-- Backward induction with the local CVaR mass equal to each actual local hazard. -/
theorem depth_risk {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool) (u : Bool)
    (k : ℕ) (j : Fin d) (hjk : j.val+k+1=d) :
    risk a (chainCost (d+2)) π (kernel hd a ha θ) (k+2) (j.val+1) (Sum.inr (u,j)) =
      if u = θ then 0 else 1 := by
  induction k generalizing j with
  | zero =>
    have hj : ¬ j.val+1<d := by omega
    have ht : j.val+1+1=d+1 := by omega
    have hh := step_risk a ha (chainCost (d+2)) π (kernel hd a ha θ) 1 (j.val+1)
      (Sum.inr (u,j)) failure (fun _ => endpoint θ u) (fun _ => badFlag θ u)
      (by intro b; simp [chainCost, bad])
      (by intro b; simp [kernel, successfulNext, hj])
      (by
        intro b
        rw [ht, badFlag_value]
        by_cases hu : u = θ
        · simp [endpoint, hu, good_risk]
        · simp [endpoint, hu, bad_terminal hd a ha])
      (failure_risk hd a ha θ π _ _ _)
    simpa only [expectation_const, badFlag_value] using hh
  | succ k ih =>
    have hj : j.val+1<d := by omega
    let j' : Fin d := ⟨j.val+1,hj⟩
    have hk' : j'.val+k+1=d := by dsimp [j']; omega
    have hh := step_risk a ha (chainCost (d+2)) π (kernel hd a ha θ) (k+2) (j.val+1)
      (Sum.inr (u,j)) failure (fun _ => Sum.inr (u,j')) (fun _ => badFlag θ u)
      (by intro b; simp [chainCost, bad])
      (by intro b; simp [kernel, successfulNext, hj, j'])
      (by intro b; rw [badFlag_value]; simpa only [j', Nat.add_assoc] using ih j' hk')
      (failure_risk hd a ha θ π _ _ _)
    simpa only [expectation_const, badFlag_value, Nat.succ_add] using hh

theorem initial_risk {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool) :
    risk a (chainCost (d+2)) π (kernel hd a ha θ) (d+2) 0 start = π 0 start (!θ) := by
  have hu (u : Bool) : risk a (chainCost (d+2)) π (kernel hd a ha θ) (d+1) 1
      (Sum.inr (u,⟨0,hd⟩)) = if badFlag θ u then 1 else 0 := by
    rw [badFlag_value]
    have hh := depth_risk hd a ha θ π u (d-1) ⟨0,hd⟩ (by simp only; omega)
    have hn : d-1+2=d+1 := by omega
    simpa only [hn, Fin.val_zero, Nat.zero_add] using hh
  have hh := step_risk a ha (chainCost (d+2)) π (kernel hd a ha θ) (d+1) 0 start failure
    (fun u => Sum.inr (u,⟨0,hd⟩)) (badFlag θ)
    (by intro u; simp [chainCost, start, bad]) (by intro u; simp [kernel, successfulNext, start])
    hu (failure_risk hd a ha θ π _ _ _)
  have he : expectation (π 0 start) (fun u => if badFlag θ u then (1:ℝ) else 0) = π 0 start (!θ) := by
    cases θ <;> simp [expectation, badFlag]
  simpa only [he] using hh

/-- Remark F.1's physical initial-risk formula in the official stage risk API. -/
theorem stage_initial_risk {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool) :
    Paper36.StageRisk.risk a (chainCost (d+2)) (finitePolicy π) (finiteKernel (kernel hd a ha θ))
      (d+2) 0 start = π 0 start (!θ) := by
  rw [stageRisk_bridge a ha _ (chainCost_bounds (d+2))]
  exact initial_risk hd a ha θ π


private theorem pure_apply {S : Type*} [Fintype S] [DecidableEq S] (u v : S) :
    Nested.pure u v = if v = u then 1 else 0 := by
  simp [Nested.pure, stdSimplex.vertex, Pi.single_apply, eq_comm]

theorem kernel_feedback_equal {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ)
    (ha : ∀ j, 0 < a j ∧ a j ≤ 1) (s t : ChainState d) (u : Bool)
    (htg : t ≠ good) (htb : t ≠ bad) : kernel hd a ha false s u t = kernel hd a ha true s u t := by
  rcases s with i | ⟨i,j⟩
  · by_cases hi : i = 0
    · simp [kernel, successfulNext, hi]
    · simp [kernel, hi]
  · by_cases hj : j.val+1<d
    · simp [kernel, successfulNext, hj]
    · have he (θ : Bool) : Nested.pure (endpoint θ i) t = 0 := by
        unfold endpoint
        split_ifs <;> simp [pure_apply, htg, htb]
      change a (j.val+2)*Nested.pure (successfulNext hd false u (Sum.inr (i,j))) t +
          (1-a (j.val+2))*Nested.pure failure t =
        a (j.val+2)*Nested.pure (successfulNext hd true u (Sum.inr (i,j))) t +
          (1-a (j.val+2))*Nested.pure failure t
      simp only [successfulNext, hj, ↓reduceDIte, he]

theorem full_trace_likelihood_equal {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ)
    (ha : ∀ j, 0 < a j ∧ a j ≤ 1) (π : Nested.Policy (ChainState d) Bool)
    (xs : Trace d) (hx : ∀ e ∈ xs, e.2.2 ≠ good ∧ e.2.2 ≠ bad) (h : ℕ) :
    traceLikelihood (kernel hd a ha false) π h xs = traceLikelihood (kernel hd a ha true) π h xs := by
  induction xs generalizing h with
  | nil => rfl
  | cons e xs ih =>
    obtain ⟨s,u,t⟩ := e
    have ht := hx (s,u,t) List.mem_cons_self
    have hh : ∀ e ∈ xs, e.2.2 ≠ good ∧ e.2.2 ≠ bad := fun e he => hx e (List.mem_cons_of_mem _ he)
    simp only [traceLikelihood, kernel_feedback_equal hd a ha s t u ht.1 ht.2, ih hh]

theorem run_depth_lower {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ)
    (ha : ∀ j, 0 < a j ∧ a j ≤ 1) (π : Nested.Policy (ChainState d) Bool)
    (V : Bool → Trace d → ℝ) (B b : ℝ) (hb : ∀ θ tr, b ≤ V θ tr)
    (hB : ∀ tr, B ≤ (V false tr+V true tr)/2)
    (u : Bool) (k : ℕ) (j : Fin d) (hjk : j.val+k+1=d) (tr : Trace d) :
    (1-survival a (j.val+1) (k+1))*B+survival a (j.val+1) (k+1)*b ≤
      (run (kernel hd a ha false) π (V false) (k+2) (j.val+1) (Sum.inr (u,j)) tr +
       run (kernel hd a ha true) π (V true) (k+2) (j.val+1) (Sum.inr (u,j)) tr)/2 := by
  induction k generalizing j tr with
  | zero =>
    have hj : ¬ j.val+1<d := by omega
    have hh := run_pair_twoPoint (fun θ => kernel hd a ha θ) π V (ha (j.val+2)).1.le (ha (j.val+2)).2
      1 (j.val+1) (Sum.inr (u,j)) failure (fun θ _ => endpoint θ u) tr B b
      (by intro θ c; simp [kernel, successfulNext, hj])
      (by
        intro c
        have h0 := run_floor (kernel hd a ha false) π (V false) b (hb false)
          1 (j.val+1+1) (endpoint false u) ((Sum.inr (u,j),c,endpoint false u)::tr)
        have h1 := run_floor (kernel hd a ha true) π (V true) b (hb true)
          1 (j.val+1+1) (endpoint true u) ((Sum.inr (u,j),c,endpoint true u)::tr)
        linarith)
      (by
        intro c
        apply run_pair_absorbing _ _ π (V false) (V true) failure
        · intro c; simp [kernel, failure]
        · intro c; simp [kernel, failure]
        · exact hB)
    simp only [Nat.zero_add, survival_succ, survival_zero, mul_one]
    change (1-a (j.val+2))*B+a (j.val+2)*b ≤ _
    linarith only [hh]
  | succ k ih =>
    have hj : j.val+1<d := by omega
    let j' : Fin d := ⟨j.val+1,hj⟩
    have hk' : j'.val+k+1=d := by dsimp [j']; omega
    have hh := run_pair_twoPoint (fun θ => kernel hd a ha θ) π V (ha (j.val+2)).1.le (ha (j.val+2)).2
      (k+2) (j.val+1) (Sum.inr (u,j)) failure (fun _ _ => Sum.inr (u,j')) tr B
      ((1-survival a (j.val+2) (k+1))*B+survival a (j.val+2) (k+1)*b)
      (by intro θ c; simp [kernel, successfulNext, hj, j'])
      (by intro c; simpa only [j', Nat.add_assoc] using ih j' hk' ((Sum.inr (u,j),c,Sum.inr (u,j'))::tr))
      (by
        intro c
        apply run_pair_absorbing _ _ π (V false) (V true) failure
        · intro c; simp [kernel, failure]
        · intro c; simp [kernel, failure]
        · exact hB)
    have he : (1-survival a (j.val+1) (k+1+1))*B+survival a (j.val+1) (k+1+1)*b =
        a (j.val+2)*((1-survival a (j.val+2) (k+1))*B+survival a (j.val+2) (k+1)*b)+(1-a (j.val+2))*B := by
      rw [survival_succ]
      ring
    simpa only [he, Nat.succ_add] using hh

theorem run_initial_lower {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ)
    (ha : ∀ j, 0 < a j ∧ a j ≤ 1) (π : Nested.Policy (ChainState d) Bool)
    (V : Bool → Trace d → ℝ) (B b : ℝ) (hb : ∀ θ tr, b ≤ V θ tr)
    (hB : ∀ tr, B ≤ (V false tr+V true tr)/2) :
    (1-survival a 0 (d+1))*B+survival a 0 (d+1)*b ≤
      (run (kernel hd a ha false) π (V false) (d+2) 0 start [] +
       run (kernel hd a ha true) π (V true) (d+2) 0 start [])/2 := by
  have hh := run_pair_twoPoint (fun θ => kernel hd a ha θ) π V (ha 1).1.le (ha 1).2
    (d+1) 0 start failure (fun _ u => Sum.inr (u,⟨0,hd⟩)) [] B
    ((1-survival a 1 d)*B+survival a 1 d*b)
    (by intro θ u; simp [kernel, successfulNext, start])
    (by
      intro u
      have hh := run_depth_lower hd a ha π V B b hb hB u (d-1) ⟨0,hd⟩
        (by simp only; omega) [(start,u,Sum.inr (u,⟨0,hd⟩))]
      have hn : d-1+1=d := by omega
      have hn' : d-1+2=d+1 := by omega
      simpa only [hn, hn', Fin.val_zero, Nat.zero_add] using hh)
    (by
      intro u
      apply run_pair_absorbing _ _ π (V false) (V true) failure
      · intro u; simp [kernel, failure]
      · intro u; simp [kernel, failure]
      · exact hB)
  have he : (1-survival a 0 (d+1))*B+survival a 0 (d+1)*b =
      a 1*((1-survival a 1 d)*B+survival a 1 d*b)+(1-a 1)*B := by rw [survival_succ]; ring
  simpa only [he] using hh


def debt {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (σ : PhysicalController d) (θ : Bool) (hist : List (Trace d)) : ℕ → ℝ
  | 0 => 0
  | k+1 => risk a (chainCost (d+2)) (σ hist) (kernel hd a ha θ) (d+2) 0 start - 1/4 +
      run (kernel hd a ha θ) (σ hist)
        (fun tr => debt hd a ha σ θ (tr::hist) k) (d+2) 0 start []

def bayesDebt {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (σ : PhysicalController d) (hist : List (Trace d)) (k : ℕ) : ℝ :=
  (debt hd a ha σ false hist k + debt hd a ha σ true hist k)/2

theorem debt_floor {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (σ : PhysicalController d) (θ : Bool) (hist : List (Trace d)) (k : ℕ) :
    -(k : ℝ)/4 ≤ debt hd a ha σ θ hist k := by
  induction k generalizing hist with
  | zero => simp [debt]
  | succ k ih =>
    have hh := run_floor (kernel hd a ha θ) (σ hist) (fun tr => debt hd a ha σ θ (tr::hist) k)
      (-(k : ℝ)/4) (fun tr => ih (tr::hist)) (d+2) 0 start []
    have hr : (0:ℝ) ≤ (σ hist) 0 start (!θ) := ((σ hist) 0 start).property.1 _
    simp only [debt, Nat.cast_add, Nat.cast_one]
    rw [initial_risk hd a ha θ (σ hist)]
    linarith

theorem learner_lower {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (σ : PhysicalController d) (hist : List (Trace d)) (k : ℕ) :
    bound (survival a 0 (d+1)) k ≤ bayesDebt hd a ha σ hist k := by
  induction k generalizing hist with
  | zero => simp [bayesDebt, debt, bound]
  | succ k ih =>
    let V : Bool → Trace d → ℝ := fun θ tr => debt hd a ha σ θ (tr::hist) k
    have hh := run_initial_lower hd a ha (σ hist) V (bound (survival a 0 (d+1)) k) (-(k : ℝ)/4)
      (fun θ tr => debt_floor hd a ha σ θ (tr::hist) k) (fun tr => ih (tr::hist))
    have ht := law_sum ((σ hist) 0 start)
    simp only [Fintype.sum_bool] at ht
    rw [bound_succ]
    simp only [bayesDebt, debt]
    rw [initial_risk hd a ha false (σ hist), initial_risk hd a ha true (σ hist)]
    simp only [Bool.not_false, Bool.not_true]
    dsimp only [V] at hh
    linarith

theorem transitionSignal_correct {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ)
    (ha : ∀ j, 0 < a j ∧ a j ≤ 1) (θ u : Bool) (s t : ChainState d)
    (hq : kernel hd a ha θ s u t ≠ 0) :
    transitionSignal (s,u,t) = none ∨ transitionSignal (s,u,t) = some θ := by
  rcases s with i | ⟨i,j⟩
  · left; rfl
  · have hsup : t = successfulNext hd θ u (Sum.inr (i,j)) ∨ t = failure :=
      twoPoint_support (a (j.val+2)) (ha (j.val+2)).1.le (ha (j.val+2)).2 _ _ t hq
    rcases hsup with rfl | rfl
    · by_cases hj : j.val+1<d
      · left; simp [transitionSignal, successfulNext, hj, good, bad]
      · right
        cases θ <;> cases i <;> simp [transitionSignal, successfulNext, hj, endpoint, good, bad]
    · left; simp [transitionSignal, failure, good, bad]

theorem run_known_const {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool) (V : Trace d → ℝ)
    (old : Option Bool) (b : ℝ) (hV : ∀ tr, updateKnowledge old tr = some θ → V tr = b)
    (n h : ℕ) (s : ChainState d) (tr : Trace d) (htr : updateKnowledge old tr = some θ) :
    run (kernel hd a ha θ) π V n h s tr = b := by
  apply run_invariant_const _ _ _ (fun tr => updateKnowledge old tr = some θ) b hV
  · intro s u t tr htr ht
    exact updateKnowledge_preserved old tr _ θ htr (transitionSignal_correct hd a ha θ u s t ht)
  · exact htr

theorem optimal_known {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ : Bool) (hist : List (Trace d)) (hk : historyKnowledge hist = some θ) (k : ℕ) :
    debt hd a ha optimalPhysical θ hist k = -(k : ℝ)/4 := by
  induction k generalizing hist with
  | zero => simp [debt]
  | succ k ih =>
    rw [debt, initial_risk hd a ha θ]
    have hc : run (kernel hd a ha θ) (optimalPhysical hist)
        (fun tr => debt hd a ha optimalPhysical θ (tr::hist) k) (d+2) 0 start [] = -(k : ℝ)/4 := by
      exact run_known_const hd a ha θ (optimalPhysical hist) _ (historyKnowledge hist) _
        (fun tr htr => ih (tr::hist) htr) (d+2) 0 start [] hk
    rw [hc]
    simp [optimalPhysical, hk, pure_apply]
    ring

theorem run_failure_unknown {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (π : Nested.Policy (ChainState d) Bool) (V : Bool → Trace d → ℝ) (old : Option Bool) (B : ℝ)
    (hV : ∀ tr, updateKnowledge old tr = none → (V false tr+V true tr)/2 = B)
    (n h : ℕ) (tr : Trace d) (htr : updateKnowledge old tr = none) :
    (run (kernel hd a ha false) π (V false) n h failure tr +
     run (kernel hd a ha true) π (V true) n h failure tr)/2 = B := by
  induction n generalizing h tr with
  | zero => exact hV tr htr
  | succ n ih =>
    have hq (θ u : Bool) : kernel hd a ha θ failure u = Nested.pure failure := by simp [kernel, failure]
    simp only [run, hq, expectation_pure]
    rw [expectation_average]
    have he (u : Bool) :
        (run (kernel hd a ha false) π (V false) n (h+1) failure ((failure,u,failure)::tr) +
         run (kernel hd a ha true) π (V true) n (h+1) failure ((failure,u,failure)::tr))/2 = B :=
      ih (h+1) _ (by simpa [updateKnowledge, transitionSignal, failure] using htr)
    simp only [he, expectation_const]

theorem run_depth_equal {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (π : Nested.Policy (ChainState d) Bool) (V : Bool → Trace d → ℝ) (old : Option Bool) (B b : ℝ)
    (hU : ∀ tr, updateKnowledge old tr = none → (V false tr+V true tr)/2 = B)
    (hK : ∀ θ tr, updateKnowledge old tr = some θ → V θ tr = b)
    (u : Bool) (k : ℕ) (j : Fin d) (hjk : j.val+k+1=d) (tr : Trace d)
    (htr : updateKnowledge old tr = none) :
    (run (kernel hd a ha false) π (V false) (k+2) (j.val+1) (Sum.inr (u,j)) tr +
     run (kernel hd a ha true) π (V true) (k+2) (j.val+1) (Sum.inr (u,j)) tr)/2 =
      (1-survival a (j.val+1) (k+1))*B+survival a (j.val+1) (k+1)*b := by
  induction k generalizing j tr with
  | zero =>
    have hj : ¬ j.val+1<d := by omega
    have hh := run_pair_twoPoint_eq (fun θ => kernel hd a ha θ) π V (ha (j.val+2)).1.le (ha (j.val+2)).2
      1 (j.val+1) (Sum.inr (u,j)) failure (fun θ _ => endpoint θ u) tr B b
      (by intro θ c; simp [kernel, successfulNext, hj])
      (by
        intro c
        have he (θ : Bool) := run_known_const hd a ha θ π (V θ) old b (hK θ)
          1 (j.val+1+1) (endpoint θ u) ((Sum.inr (u,j),c,endpoint θ u)::tr)
          (by simp [updateKnowledge, endpoint_transition_signal])
        rw [he false, he true]
        ring)
      (by
        intro c
        exact run_failure_unknown hd a ha π V old B hU 1 _ _
          (by simpa [updateKnowledge, transitionSignal, failure, good, bad] using htr))
    simp only [Nat.zero_add, survival_succ, survival_zero, mul_one]
    change _ = (1-a (j.val+2))*B+a (j.val+2)*b
    linarith only [hh]
  | succ k ih =>
    have hj : j.val+1<d := by omega
    let j' : Fin d := ⟨j.val+1,hj⟩
    have hk' : j'.val+k+1=d := by dsimp [j']; omega
    have hh := run_pair_twoPoint_eq (fun θ => kernel hd a ha θ) π V (ha (j.val+2)).1.le (ha (j.val+2)).2
      (k+2) (j.val+1) (Sum.inr (u,j)) failure (fun _ _ => Sum.inr (u,j')) tr B
      ((1-survival a (j.val+2) (k+1))*B+survival a (j.val+2) (k+1)*b)
      (by intro θ c; simp [kernel, successfulNext, hj, j'])
      (by
        intro c
        simpa only [j', Nat.add_assoc] using ih j' hk' ((Sum.inr (u,j),c,Sum.inr (u,j'))::tr)
          (by simpa [updateKnowledge, transitionSignal, good, bad] using htr))
      (by
        intro c
        exact run_failure_unknown hd a ha π V old B hU _ _ _
          (by simpa [updateKnowledge, transitionSignal, failure, good, bad] using htr))
    have he : (1-survival a (j.val+1) (k+1+1))*B+survival a (j.val+1) (k+1+1)*b =
        a (j.val+2)*((1-survival a (j.val+2) (k+1))*B+survival a (j.val+2) (k+1)*b)+(1-a (j.val+2))*B := by
      rw [survival_succ]
      ring
    simpa only [he, Nat.succ_add] using hh

theorem run_initial_equal {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (π : Nested.Policy (ChainState d) Bool) (V : Bool → Trace d → ℝ) (B b : ℝ)
    (hU : ∀ tr, updateKnowledge none tr = none → (V false tr+V true tr)/2 = B)
    (hK : ∀ θ tr, updateKnowledge none tr = some θ → V θ tr = b) :
    (run (kernel hd a ha false) π (V false) (d+2) 0 start [] +
     run (kernel hd a ha true) π (V true) (d+2) 0 start [])/2 =
      (1-survival a 0 (d+1))*B+survival a 0 (d+1)*b := by
  have hh := run_pair_twoPoint_eq (fun θ => kernel hd a ha θ) π V (ha 1).1.le (ha 1).2
    (d+1) 0 start failure (fun _ u => Sum.inr (u,⟨0,hd⟩)) [] B ((1-survival a 1 d)*B+survival a 1 d*b)
    (by intro θ u; simp [kernel, successfulNext, start])
    (by
      intro u
      have hh := run_depth_equal hd a ha π V none B b hU hK u (d-1) ⟨0,hd⟩
        (by simp only; omega) [(start,u,Sum.inr (u,⟨0,hd⟩))]
        (by simp [updateKnowledge, transitionSignal, start])
      have hn : d-1+1=d := by omega
      have hn' : d-1+2=d+1 := by omega
      simpa only [hn, hn', Fin.val_zero, Nat.zero_add] using hh)
    (by
      intro u
      exact run_failure_unknown hd a ha π V none B hU _ _ _
        (by simp [updateKnowledge, transitionSignal, start]))
  have he : (1-survival a 0 (d+1))*B+survival a 0 (d+1)*b =
      a 1*((1-survival a 1 d)*B+survival a 1 d*b)+(1-a 1)*B := by rw [survival_succ]; ring
  simpa only [he] using hh

theorem optimal_unknown {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (hist : List (Trace d)) (hk : historyKnowledge hist = none) (k : ℕ) :
    bayesDebt hd a ha optimalPhysical hist k = bound (survival a 0 (d+1)) k := by
  induction k generalizing hist with
  | zero => simp [bayesDebt, debt, bound]
  | succ k ih =>
    let V : Bool → Trace d → ℝ := fun θ tr => debt hd a ha optimalPhysical θ (tr::hist) k
    have hh := run_initial_equal hd a ha (optimalPhysical hist) V (bound (survival a 0 (d+1)) k) (-(k : ℝ)/4)
      (by intro tr htr; exact ih (tr::hist) (by simpa [historyKnowledge, hk] using htr))
      (by intro θ tr htr; exact optimal_known hd a ha θ (tr::hist) (by simpa [historyKnowledge, hk] using htr) k)
    have ht := law_sum ((optimalPhysical hist) 0 start)
    simp only [Fintype.sum_bool] at ht
    rw [bound_succ]
    simp only [bayesDebt, debt]
    rw [initial_risk hd a ha false, initial_risk hd a ha true]
    simp only [Bool.not_false, Bool.not_true]
    dsimp only [V] at hh
    linarith

/-- Remark F.1's exact identity with the genuine physical hazard product. -/
theorem exact_optimum {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1) (k : ℕ) :
    IsLeast {v : ℝ | ∃ σ : PhysicalController d, v = bayesDebt hd a ha σ [] k}
      ((1-(1-Paper36.Weights.prefixMass a (d+1))^k)/(2*Paper36.Weights.prefixMass a (d+1))-(k : ℝ)/4) := by
  rw [← survival_prefix a (d+1), ← bound_closed (survival_pos a (fun j => (ha j).1) 0 (d+1))]
  constructor
  · exact ⟨optimalPhysical, (optimal_unknown hd a ha [] rfl k).symm⟩
  · rintro v ⟨σ,rfl⟩
    exact learner_lower hd a ha σ [] k


/-- The learner's one-episode debt is the official stage-dependent nested risk. -/
theorem debt_step_stageRisk {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (σ : PhysicalController d) (θ : Bool) (hist : List (Trace d)) (k : ℕ) :
    debt hd a ha σ θ hist (k+1) =
      Paper36.StageRisk.risk a (chainCost (d+2)) (finitePolicy (σ hist))
        (finiteKernel (kernel hd a ha θ)) (d+2) 0 start - 1/4 +
      run (kernel hd a ha θ) (σ hist) (fun tr => debt hd a ha σ θ (tr::hist) k) (d+2) 0 start [] := by
  rw [debt, stageRisk_bridge a ha _ (chainCost_bounds (d+2))]

def seedDebt {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (σ : Ω → PhysicalController d) (k : ℕ) : ℝ := ∫ ω, bayesDebt hd a ha (σ ω) [] k ∂μ

theorem private_seed_lower {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (σ : Ω → PhysicalController d) (k : ℕ)
    (hσ : MeasureTheory.Integrable (fun ω => bayesDebt hd a ha (σ ω) [] k) μ) :
    bound (Paper36.Weights.prefixMass a (d+1)) k ≤ seedDebt μ hd a ha σ k := by
  rw [← survival_prefix a (d+1)]
  unfold seedDebt
  calc
    bound (survival a 0 (d+1)) k = ∫ _ω : Ω, bound (survival a 0 (d+1)) k ∂μ := by simp
    _ ≤ _ := MeasureTheory.integral_mono (MeasureTheory.integrable_const _) hσ
      (fun ω => learner_lower hd a ha (σ ω) [] k)

/-- The exact F.1 Bayes identity includes all independently privately randomized
learners observing complete physical trajectories. -/
theorem private_seed_exact_optimum {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1) (k : ℕ) :
    IsLeast {v : ℝ | ∃ σ : Ω → PhysicalController d,
      MeasureTheory.Integrable (fun ω => bayesDebt hd a ha (σ ω) [] k) μ ∧ v = seedDebt μ hd a ha σ k}
      ((1-(1-Paper36.Weights.prefixMass a (d+1))^k)/(2*Paper36.Weights.prefixMass a (d+1))-(k : ℝ)/4) := by
  rw [← survival_prefix a (d+1), ← bound_closed (survival_pos a (fun j => (ha j).1) 0 (d+1))]
  constructor
  · refine ⟨fun _ => optimalPhysical, ?_, ?_⟩
    · simpa only [optimal_unknown hd a ha [] rfl k] using
        (MeasureTheory.integrable_const (bound (survival a 0 (d+1)) k) :
          MeasureTheory.Integrable (fun _ω : Ω => bound (survival a 0 (d+1)) k) μ)
    · unfold seedDebt
      simp only [optimal_unknown hd a ha [] rfl k]
      simp
  · rintro v ⟨σ,hσ,rfl⟩
    rw [survival_prefix]
    exact private_seed_lower μ hd a ha σ k hσ

theorem private_seed_tailored {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (hβ4 : Paper36.Weights.prefixMass a (d+1) ≤ 1/4)
    (σ : Ω → PhysicalController d)
    (hσ : MeasureTheory.Integrable
      (fun ω => bayesDebt hd a ha (σ ω) [] (K0 (Paper36.Weights.prefixMass a (d+1)))) μ) :
    1/(32*Paper36.Weights.prefixMass a (d+1)) ≤
      seedDebt μ hd a ha σ (K0 (Paper36.Weights.prefixMass a (d+1))) := by
  have hβ : 0 < Paper36.Weights.prefixMass a (d+1) := Paper36.Weights.prefixMass_pos (fun j _ => (ha j).1)
  exact (tailored_bound hβ hβ4).trans (private_seed_lower μ hd a ha σ _ hσ)

/-- Complete physical histories have equal pre-revelation likelihood, pointwise
in every private seed, since the controller itself has no latent-model input. -/
def historyLikelihood {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (σ : PhysicalController d) (θ : Bool) : List (Trace d) → ℝ
  | [] => 1
  | tr::hist => historyLikelihood hd a ha σ θ hist * traceLikelihood (kernel hd a ha θ) (σ hist) 0 tr

theorem history_likelihood_equal {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ)
    (ha : ∀ j, 0 < a j ∧ a j ≤ 1) (σ : PhysicalController d) (hist : List (Trace d))
    (hu : ∀ tr ∈ hist, ∀ e ∈ tr, e.2.2 ≠ good ∧ e.2.2 ≠ bad) :
    historyLikelihood hd a ha σ false hist = historyLikelihood hd a ha σ true hist := by
  induction hist with
  | nil => rfl
  | cons tr hist ih =>
    have htr := hu tr List.mem_cons_self
    have hh : ∀ tr ∈ hist, ∀ e ∈ tr, e.2.2 ≠ good ∧ e.2.2 ≠ bad := fun tr htr => hu tr (List.mem_cons_of_mem _ htr)
    simp only [historyLikelihood, ih hh, full_trace_likelihood_equal hd a ha (σ hist) tr htr]

/-- Finite source tail-mass vectors extend by one outside the horizon; no extra
hypothesis is imposed on unused stages. -/
def extendRates {n : ℕ} (v : Fin n → ℝ) (j : ℕ) : ℝ :=
  if hj : 1 ≤ j ∧ j ≤ n then v ⟨j-1, by omega⟩ else 1

theorem extendRates_bounds {n : ℕ} (v : Fin n → ℝ) (hv : ∀ j, 0 < v j ∧ v j ≤ 1) :
    ∀ j, 0 < extendRates v j ∧ extendRates v j ≤ 1 := by
  intro j
  unfold extendRates
  split_ifs
  · exact hv _
  · norm_num

theorem extendRates_prefix {n : ℕ} (v : Fin n → ℝ) :
    Paper36.Weights.prefixMass (extendRates v) n = ∏ j, v j := by
  rw [← survival_prefix, survival_product]
  simp only [Nat.zero_add]
  rw [← Fin.prod_univ_eq_prod_range]
  apply prod_congr rfl
  intro j _
  simp [extendRates, j.isLt, Nat.succ_le_iff.mpr j.isLt]

/-- Fully finite-parameter version of Remark F.1, with beta literally the
product of the H-1 supplied tail masses. -/
theorem finite_rates_exact_optimum {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) (v : Fin (d+1) → ℝ) (hv : ∀ j, 0 < v j ∧ v j ≤ 1) (k : ℕ) :
    IsLeast {z : ℝ | ∃ σ : Ω → PhysicalController d,
      MeasureTheory.Integrable (fun ω => bayesDebt hd (extendRates v) (extendRates_bounds v hv) (σ ω) [] k) μ ∧
      z = seedDebt μ hd (extendRates v) (extendRates_bounds v hv) σ k}
      ((1-(1-∏ j, v j)^k)/(2*∏ j, v j)-(k : ℝ)/4) := by
  simpa only [extendRates_prefix] using private_seed_exact_optimum μ hd (extendRates v) (extendRates_bounds v hv) k


def simplexLaw {Ω : Type*} [Fintype Ω] (P : Paper36.CVaR.Law Ω) : Law Ω :=
  ⟨P.mass, P.nonneg, P.total⟩

def simplexPolicy {S A : Type*} [Fintype A] (π : Paper36.Simulation.Policy S A) : Nested.Policy S A :=
  fun h s => simplexLaw (π h s)

theorem finite_simplexLaw {Ω : Type*} [Fintype Ω] (P : Paper36.CVaR.Law Ω) :
    finiteLaw (simplexLaw P) = P := by cases P; rfl

theorem finite_simplexPolicy {S A : Type*} [Fintype A] (π : Paper36.Simulation.Policy S A) :
    finitePolicy (simplexPolicy π) = π := by funext h s; exact finite_simplexLaw _

/-- The stage-risk formula ranges over every policy in the envelope API too. -/
theorem stage_initial_risk_all {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ : Bool) (π : Paper36.Simulation.Policy (ChainState d) Bool) :
    Paper36.StageRisk.risk a (chainCost (d+2)) π (finiteKernel (kernel hd a ha θ)) (d+2) 0 start =
      (π 0 start).mass (!θ) := by
  simpa only [finite_simplexPolicy, simplexPolicy, simplexLaw] using stage_initial_risk hd a ha θ (simplexPolicy π)

theorem kernel_no_return {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ u : Bool) (s : ChainState d) : kernel hd a ha θ s u start = 0 := by
  rcases s with i | ⟨i,j⟩
  · by_cases hi : i = 0
    · simp [kernel, successfulNext, hi, twoPoint_apply, pure_apply, start, failure]
    · simp [kernel, hi, pure_apply, start, Ne.symm hi]
  · have hs : successfulNext hd θ u (Sum.inr (i,j)) ≠ start :=
      (successfulNext_not_start hd θ u _).resolve_right (by simp [start])
    change a (j.val+2)*Nested.pure (successfulNext hd θ u (Sum.inr (i,j))) start +
      (1-a (j.val+2))*Nested.pure failure start = 0
    rw [pure_apply, if_neg (Ne.symm hs)]
    simp [pure_apply, start, failure]

theorem source_reward_one {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ : Bool) (π : Nested.Policy (ChainState d) Bool) (n h : ℕ) (s : ChainState d) :
    Nested.reward chainReward π (kernel hd a ha θ) (n+1) h s = if s = start then 1 else 0 := by
  classical
  induction n generalizing h s with
  | zero =>
    rw [Nested.reward]
    simp only [Nested.reward, mul_zero, sum_const_zero, add_zero, chainReward]
    rw [← sum_mul, law_sum, one_mul]
  | succ n ih =>
    rw [Nested.reward]
    simp only [ih, chainReward]
    have he (u : Bool) : (∑ t, kernel hd a ha θ s u t * (if t=start then (1:ℝ) else 0)) = 0 := by
      simp [kernel_no_return]
    simp only [he, add_zero]
    rw [← sum_mul, law_sum, one_mul]

theorem zero_reward_shortfall {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ : Bool) (σ : PhysicalController d) (hist : List (Trace d)) :
    1-Nested.reward chainReward (σ hist) (kernel hd a ha θ) (d+2) 0 start = 0 := by
  rw [source_reward_one hd a ha θ (σ hist) (d+1) 0 start]
  simp

theorem stage_good_comparator {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (θ : Bool) : ∃ π : Nested.Policy (ChainState d) Bool,
      Paper36.StageRisk.risk a (chainCost (d+2)) (finitePolicy π) (finiteKernel (kernel hd a ha θ)) (d+2) 0 start = 0 ∧
      Nested.reward chainReward π (kernel hd a ha θ) (d+2) 0 start = 1 := by
  refine ⟨fun _ _ => Nested.pure θ, ?_, ?_⟩
  · rw [stage_initial_risk hd a ha θ]
    cases θ <;> simp [pure_apply]
  · simpa using source_reward_one hd a ha θ (fun _ _ => Nested.pure θ) (d+1) 0 start


theorem finite_rates_tailored {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (hd : 0 < d) (v : Fin (d+1) → ℝ) (hv : ∀ j, 0 < v j ∧ v j ≤ 1)
    (hβ4 : (∏ j, v j) ≤ 1/4) (σ : Ω → PhysicalController d)
    (hσ : MeasureTheory.Integrable
      (fun ω => bayesDebt hd (extendRates v) (extendRates_bounds v hv) (σ ω) [] (K0 (∏ j, v j))) μ) :
    1/(32*∏ j, v j) ≤ seedDebt μ hd (extendRates v) (extendRates_bounds v hv) σ (K0 (∏ j, v j)) := by
  have hh := private_seed_tailored μ hd (extendRates v) (extendRates_bounds v hv)
    (by simpa only [extendRates_prefix] using hβ4) σ
    (by simpa only [extendRates_prefix] using hσ)
  simpa only [extendRates_prefix] using hh

/-- The latent-model prior is a real probability law with exactly equal weights. -/
def uniformPrior : Law Bool :=
  ⟨fun _ => 1/2, (by intro _; norm_num), by simp⟩

theorem uniformPrior_expectation (f : Bool → ℝ) : expectation uniformPrior f = (f false+f true)/2 := by
  change (∑ θ : Bool, (1/2 : ℝ)*f θ) = (f false+f true)/2
  simp only [Fintype.sum_bool]
  ring

theorem homogeneous_bayes_prior {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (σ : PhysicalController d) (hist : List (Trace d)) (k : ℕ) :
    physicalBayesDebt hd α hα hα1 σ hist k =
      expectation uniformPrior (fun θ => physicalDebt hd α hα hα1 σ θ hist k) := by
  rw [uniformPrior_expectation]
  rfl

theorem heterogeneous_bayes_prior {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1)
    (σ : PhysicalController d) (hist : List (Trace d)) (k : ℕ) :
    bayesDebt hd a ha σ hist k = expectation uniformPrior (fun θ => debt hd a ha σ θ hist k) := by
  rw [uniformPrior_expectation]
  rfl

theorem models_distinct {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j ∧ a j ≤ 1) :
    kernel hd a ha false ≠ kernel hd a ha true := by
  intro heq
  let π : Nested.Policy (ChainState d) Bool := fun _ _ => Nested.pure false
  have h0 := initial_risk hd a ha false π
  have h1 := initial_risk hd a ha true π
  rw [heq] at h0
  rw [h1] at h0
  simp [π, pure_apply] at h0

theorem homogeneous_models_distinct {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    chainKernel hd α hα.le hα1 false ≠ chainKernel hd α hα.le hα1 true := by
  intro heq
  let π : Nested.Policy (ChainState d) Bool := fun _ _ => Nested.pure false
  have h0 := source_initial_risk hd hα hα1 false π
  have h1 := source_initial_risk hd hα hα1 true π
  rw [heq] at h0
  rw [h1] at h0
  simp [π, pure_apply] at h0


/-- The fixed comparator really is the source constrained Markov optimum. -/
theorem homogeneous_constrained_comparator {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool) : ∃ π : Nested.Policy (ChainState d) Bool,
      Nested.risk α (chainCost (d+2)) π (chainKernel hd α hα.le hα1 θ) (d+2) 0 start ≤ 1/4 ∧
      Nested.reward chainReward π (chainKernel hd α hα.le hα1 θ) (d+2) 0 start = 1 ∧
      ∀ π', Nested.risk α (chainCost (d+2)) π' (chainKernel hd α hα.le hα1 θ) (d+2) 0 start ≤ 1/4 →
        Nested.reward chainReward π' (chainKernel hd α hα.le hα1 θ) (d+2) 0 start ≤ 1 := by
  obtain ⟨π,hπ,hr⟩ := source_good_comparator hd hα hα1 θ
  refine ⟨π, by rw [hπ]; norm_num, hr, ?_⟩
  intro π' _
  simpa using (Paper36.LowerBound.source_reward_one hd α hα.le hα1 θ π' (d+1) 0 start).le

theorem fallback_constrained_comparator {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (θ : Bool) : ∃ π : Nested.Policy (ChainState d) (Option Bool),
      Nested.risk α (fallbackCost (d+2)) π (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start ≤ 1/4 ∧
      Nested.reward fallbackReward π (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start = 1 ∧
      ∀ π', Nested.risk α (fallbackCost (d+2)) π' (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start ≤ 1/4 →
        Nested.reward fallbackReward π' (fallbackKernel hd α hα.le hα1 θ) (d+2) 0 start ≤ 1 := by
  have hh := (fallback_comparators hd hα hα1).1 θ
  refine ⟨fun _ _ => Nested.pure (some θ), by rw [hh.1]; norm_num, hh.2, ?_⟩
  intro π' _
  rw [fallback_source_reward hd α hα.le hα1 θ π' (d+1) 0 start]
  simp only [ite_true]
  have hp : (0:ℝ) ≤ π' 0 start none := (π' 0 start).property.1 none
  linarith

end
end Paper36.LowerBound.Heterogeneous
