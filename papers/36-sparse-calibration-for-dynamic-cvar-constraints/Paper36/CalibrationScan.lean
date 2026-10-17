import Init.Data.Vector.OfFn
import Paper36.RiskBridge
import Paper36.Calibration
import Mathlib.Algebra.BigOperators.Fin

/-! A real greedy tail scan, its exact CVaR certificate, and instrumented arithmetic
cost. The loss vector is supplied in descending order; one ordering can be reused
for all transition rows at the same backward stage. -/
namespace Paper36.CalibrationScan
open scoped BigOperators
noncomputable section

structure ScanResult (n : ℕ) where
  weights : Fin n → ℝ
  threshold : ℝ
  payoff : ℝ
  visited : ℕ
  operations : ℕ

/-- Fill the unit tail from the largest loss downward. A terminal comparison and
multiplication cost two scalar operations; a continuing cell additionally uses
one subtraction and one addition. Capacity evaluation is counted separately. -/
def scan : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ → ScanResult n
  | 0, _, _, _ => ⟨Fin.elim0, 0, 0, 0, 0⟩
  | n+1, cap, loss, remaining =>
    let c := cap 0
    let x := loss 0
    if remaining ≤ c then
      ⟨Fin.cons remaining (fun _ => 0), x, remaining*x, 1, 2⟩
    else
      let tail := scan n (fun i => cap i.succ) (fun i => loss i.succ) (remaining-c)
      ⟨Fin.cons c tail.weights, tail.threshold, c*x+tail.payoff,
        tail.visited+1, tail.operations+4⟩

theorem scan_cost (n : ℕ) (cap loss : Fin n → ℝ) (remaining : ℝ) :
    (scan n cap loss remaining).visited ≤ n ∧ (scan n cap loss remaining).operations ≤ 4*n := by
  induction n generalizing remaining with
  | zero => simp [scan]
  | succ n ih =>
    dsimp [scan]
    split_ifs
    · constructor <;> dsimp <;> omega
    · have ht := ih (cap := fun i => cap i.succ) (loss := fun i => loss i.succ)
        (remaining := remaining-cap 0)
      constructor <;> dsimp <;> omega

/-- The scan fills exactly the requested mass and computes its actual weighted
payoff. These claims do not require loss sorting. -/
theorem scan_feasible (n : ℕ) (cap loss : Fin n → ℝ) (r : ℝ)
    (hc : ∀ i, 0 ≤ cap i) (hr : 0 ≤ r) (ht : r ≤ ∑ i, cap i) :
    (∀ i, 0 ≤ (scan n cap loss r).weights i ∧ (scan n cap loss r).weights i ≤ cap i) ∧
      (∑ i, (scan n cap loss r).weights i) = r ∧
      (scan n cap loss r).payoff = ∑ i, (scan n cap loss r).weights i * loss i := by
  induction n generalizing r with
  | zero =>
    have he : r = 0 := by simpa using le_antisymm ht hr
    subst r
    simp [scan]
  | succ n ih =>
    rw [Fin.sum_univ_succ] at ht
    by_cases h : r ≤ cap 0
    · simp only [scan, if_pos h]
      refine ⟨?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using And.intro hr h
        · simpa using And.intro (le_refl (0 : ℝ)) (hc j.succ)
      · simp [Fin.sum_univ_succ]
      · simp [Fin.sum_univ_succ]
    · have htail : r-cap 0 ≤ ∑ i : Fin n, cap i.succ := by linarith
      have hrem : 0 ≤ r-cap 0 := sub_nonneg.2 (le_of_not_ge h)
      obtain ⟨hw, hsum, hvalue⟩ := ih (cap := fun i => cap i.succ)
        (loss := fun i => loss i.succ) (r := r-cap 0) (fun i => hc i.succ) hrem htail
      simp only [scan, if_neg h]
      refine ⟨?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using And.intro (hc 0) (le_refl (cap 0))
        · simpa using hw j
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        rw [hsum]
        ring
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        rw [hvalue]

/-- A feasible nonempty scan chooses one of the actual losses as its threshold. -/
theorem scan_threshold_mem (n : ℕ) (cap loss : Fin n → ℝ) (r : ℝ)
    (hn : 0 < n) (hc : ∀ i, 0 ≤ cap i) (hr : 0 ≤ r) (ht : r ≤ ∑ i, cap i) :
    ∃ i, (scan n cap loss r).threshold = loss i := by
  induction n generalizing r with
  | zero => omega
  | succ n ih =>
    by_cases h : r ≤ cap 0
    · exact ⟨0, by simp [scan, h]⟩
    · have htail : r-cap 0 ≤ ∑ i : Fin n, cap i.succ := by
        rw [Fin.sum_univ_succ] at ht
        linarith
      have hrem : 0 < r-cap 0 := sub_pos.2 (lt_of_not_ge h)
      have hn' : 0 < n := by
        by_contra hh
        have hn0 : n = 0 := by omega
        subst n
        simp at htail
        linarith
      obtain ⟨i, hi⟩ := ih (cap := fun i => cap i.succ) (loss := fun i => loss i.succ)
        (r := r-cap 0) hn' (fun i => hc i.succ) hrem.le htail
      exact ⟨i.succ, by simpa [scan, h] using hi⟩

/-- Sortedness makes the computed payoff equal a CVaR primal objective. This is
an explicit optimality certificate, rather than an assumed optimal scan. -/
theorem scan_primal_certificate (n : ℕ) (cap loss : Fin n → ℝ) (r : ℝ)
    (hc : ∀ i, 0 ≤ cap i) (hr : 0 ≤ r) (ht : r ≤ ∑ i, cap i) (hsort : Antitone loss) :
    (scan n cap loss r).payoff = r * (scan n cap loss r).threshold +
      ∑ i, cap i * max (loss i - (scan n cap loss r).threshold) 0 := by
  induction n generalizing r with
  | zero => simp [scan]
  | succ n ih =>
    by_cases h : r ≤ cap 0
    · simp only [scan, if_pos h]
      have hz : ∀ i : Fin n, max (loss i.succ - loss 0) 0 = 0 := by
        intro i
        exact max_eq_right (sub_nonpos.2 (hsort (Fin.zero_le i.succ)))
      simp [Fin.sum_univ_succ, hz]
    · have htail : r-cap 0 ≤ ∑ i : Fin n, cap i.succ := by
        rw [Fin.sum_univ_succ] at ht
        linarith
      have hrem : 0 < r-cap 0 := sub_pos.2 (lt_of_not_ge h)
      have hn : 0 < n := by
        by_contra hh
        have hn0 : n = 0 := by omega
        subst n
        simp at htail
        linarith
      have hs : Antitone (fun i : Fin n => loss i.succ) := fun i j hij => hsort (Fin.succ_le_succ_iff.2 hij)
      have he := ih (cap := fun i => cap i.succ) (loss := fun i => loss i.succ)
        (r := r-cap 0) (fun i => hc i.succ) hrem.le htail hs
      obtain ⟨i, hi⟩ := scan_threshold_mem n (fun i => cap i.succ) (fun i => loss i.succ)
        (r-cap 0) hn (fun i => hc i.succ) hrem.le htail
      have hz : (scan n (fun i => cap i.succ) (fun i => loss i.succ) (r-cap 0)).threshold ≤ loss 0 := by
        rw [hi]
        exact hsort (Fin.zero_le i.succ)
      simp only [scan, if_neg h, Fin.sum_univ_succ]
      rw [max_eq_left (sub_nonneg.2 hz), he]
      ring

/-- The true row scan evaluates Pᵢ/α once at each visited successor. -/
def rowScan (P : CVaR.Law (Fin n)) (α : ℝ) (loss : Fin n → ℝ) : ScanResult n :=
  let r := scan n (fun i => P.mass i / α) loss 1
  { r with operations := r.operations+r.visited }

theorem rowScan_cost (P : CVaR.Law (Fin n)) (α : ℝ) (loss : Fin n → ℝ) :
    (rowScan P α loss).operations ≤ 5*n := by
  have h := scan_cost n (fun i => P.mass i/α) loss 1
  dsimp [rowScan]
  omega

/-- A descending row scan returns exactly the finite upper-tail CVaR. -/
theorem rowScan_eq_value (P : CVaR.Law (Fin n)) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (loss : Fin n → ℝ) (hsort : Antitone loss) :
    (rowScan P α loss).payoff = CVaR.value P α loss := by
  have hc : ∀ i, 0 ≤ P.mass i/α := fun i => div_nonneg (P.nonneg i) ha.le
  have ht : (1 : ℝ) ≤ ∑ i, P.mass i/α := by
    rw [← Finset.sum_div, P.total]
    exact (one_le_div ha).2 ha1
  obtain ⟨hw, hsum, hpay⟩ := scan_feasible n _ loss 1 hc zero_le_one ht
  have he := scan_primal_certificate n _ loss 1 hc zero_le_one ht hsort
  have henv : CVaR.Envelope P α (scan n (fun i => P.mass i/α) loss 1).weights :=
    ⟨fun i => (hw i).1, fun i => (hw i).2, hsum⟩
  change (scan n _ loss 1).payoff = _
  apply le_antisymm
  · rw [hpay]
    exact CVaR.expect_le_value P ha ha1 henv loss
  · calc
      CVaR.value P α loss ≤ CVaR.primal P α loss (scan n (fun i => P.mass i/α) loss 1).threshold :=
        CVaR.value_le_primal P ha ha1 _ _
      _ = _ := by simpa only [CVaR.primal, one_mul] using he.symm

/-! ## Reordering, minimum scans, and materialized dynamic-programming tables -/

def reindexLaw (P : CVaR.Law (Fin n)) (e : Equiv.Perm (Fin n)) : CVaR.Law (Fin n) :=
  ⟨fun i => P.mass (e i), fun i => P.nonneg (e i), (Equiv.sum_comp e P.mass).trans P.total⟩

theorem value_reindex (P : CVaR.Law (Fin n)) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (loss : Fin n → ℝ) (e : Equiv.Perm (Fin n)) :
    CVaR.value (reindexLaw P e) α (fun i => loss (e i)) = CVaR.value P α loss := by
  rw [CVaR.value_eq_primal_inf _ ha ha1, CVaR.value_eq_primal_inf _ ha ha1]
  have he : CVaR.primal (reindexLaw P e) α (fun i => loss (e i)) = CVaR.primal P α loss := by
    funext z
    dsimp [CVaR.primal, reindexLaw]
    rw [Equiv.sum_comp e (fun i => P.mass i/α * max (loss i-z) 0)]
  rw [he]

structure SortedOrder (n : ℕ) (loss : Fin n → ℝ) where
  order : Equiv.Perm (Fin n)
  sorted : Antitone (fun i => loss (order i))
  operations : ℕ

def orderedRow (P : CVaR.Law (Fin n)) (α : ℝ) (loss : Fin n → ℝ)
    (e : Equiv.Perm (Fin n)) : ScanResult n := rowScan (reindexLaw P e) α (fun i => loss (e i))

theorem orderedRow_eq_value (P : CVaR.Law (Fin n)) {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (loss : Fin n → ℝ) (order : SortedOrder n loss) :
    (orderedRow P α loss order.order).payoff = CVaR.value P α loss := by
  rw [orderedRow, rowScan_eq_value _ ha ha1 _ order.sorted, value_reindex P ha ha1]

theorem orderedRow_cost (P : CVaR.Law (Fin n)) (α : ℝ) (loss : Fin n → ℝ)
    (e : Equiv.Perm (Fin n)) : (orderedRow P α loss e).operations ≤ 5*n := rowScan_cost _ _ _

structure MinimumResult (m : ℕ) where
  value : ℝ
  index : Fin (m+1)
  operations : ℕ

/-- A genuine comparison scan over a nonempty action table. -/
def minimumScan : (m : ℕ) → (Fin (m+1) → ℝ) → MinimumResult m
  | 0, f => ⟨f 0, 0, 0⟩
  | m+1, f =>
    let tail := minimumScan m (fun i => f i.succ)
    if f 0 ≤ tail.value then ⟨f 0, 0, tail.operations+1⟩
    else ⟨tail.value, tail.index.succ, tail.operations+1⟩

theorem minimumScan_correct (m : ℕ) (f : Fin (m+1) → ℝ) :
    (minimumScan m f).value = f (minimumScan m f).index ∧
      (∀ a, (minimumScan m f).value ≤ f a) ∧ (minimumScan m f).operations = m := by
  induction m with
  | zero =>
    constructor
    · rfl
    constructor
    · intro a
      have ha : a = 0 := Fin.eq_zero a
      subst a
      exact le_rfl
    · rfl
  | succ m ih =>
    have ht := ih (f := fun i => f i.succ)
    by_cases h : f 0 ≤ (minimumScan m (fun i => f i.succ)).value
    · simp only [minimumScan, if_pos h]
      refine ⟨trivial, ?_, by omega⟩
      intro a
      refine Fin.cases ?_ (fun i => ?_) a
      · exact le_rfl
      · exact h.trans (ht.2.1 i)
    · simp only [minimumScan, if_neg h]
      refine ⟨ht.1, ?_, by omega⟩
      intro a
      refine Fin.cases ?_ (fun i => ?_) a
      · exact le_of_not_ge h
      · exact ht.2.1 i

/-- Values are materialized in an array-backed vector; later states read each
computed tail value without rerunning its recursive evaluation. -/
structure DPResult (n : ℕ) where
  values : Vector ℝ n
  operations : ℕ
  actions : ℕ → Fin n → ℕ
  actionTables : List (Vector ℕ n)

def vectorAt (v : Vector β n) (i : Fin n) : β := v[i.val]

@[simp] theorem vectorAt_ofFn (f : Fin n → β) (i : Fin n) :
    vectorAt (Vector.ofFn f) i = f i := by simp [vectorAt]

def DPResult.value (R : DPResult n) : Fin n → ℝ := vectorAt R.values

/-- One continuation ordering is computed once, then reused for every state and
action row. State/action row results and action minima are materialized arrays. -/
def evaluateDP {n m : ℕ} (α : ℝ) (c : ℕ → Fin n → Fin (m+1) → ℝ)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) : ℕ → ℕ → DPResult n
  | 0, _ => ⟨Vector.ofFn (fun _ => 0), 0, fun _ _ => 0, []⟩
  | k+1, h =>
    let tail := evaluateDP α c q sorter k (h+1)
    let order := sorter tail.value
    let rows := Vector.ofFn (fun s : Fin n => Vector.ofFn (fun a : Fin (m+1) =>
      orderedRow (RiskBridge.ofRegular (q s a)) α tail.value order.order))
    let actionTable := Vector.ofFn (fun s : Fin n => Vector.ofFn (fun a : Fin (m+1) =>
      c h s a + (vectorAt (vectorAt rows s) a).payoff))
    let actionValues := fun s a => vectorAt (vectorAt actionTable s) a
    let minima := Vector.ofFn (fun s => minimumScan m (actionValues s))
    ⟨Vector.ofFn (fun s => (vectorAt minima s).value),
      tail.operations+order.operations+
        (∑ s, ∑ a, ((vectorAt (vectorAt rows s) a).operations+1))+
        ∑ s, (vectorAt minima s).operations,
      (fun j s => if j=h then (vectorAt minima s).index.val else tail.actions j s),
      (Vector.ofFn (fun s => (vectorAt minima s).index.val)) :: tail.actionTables⟩

theorem dp_bounds (α : ℝ) (ha : 0 ≤ α) (c : ℕ → Fin n → Fin (m+1) → ℝ)
    (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (q : Nested.Kernel (Fin n) (Fin (m+1))) (k h : ℕ) (s : Fin n) :
    Calibration.dp α c q k h s ∈ Set.Icc 0 (k : ℝ) := by
  obtain ⟨π, _, he⟩ := Calibration.exists_deterministic_minimizer α c q k h
  rw [← he s]
  exact Nested.risk_bounds α ha c hc π q k h s

/-- Translation by the current scalar cost preserves a common ordering of
continuation losses across all state-action rows. -/
theorem row_correct (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (P : Regularity.Law (Fin n)) (g : Fin n → ℝ) (k : ℕ)
    (hg : ∀ s, g s ∈ Set.Icc 0 (k : ℝ)) (d : ℝ) (hd : d ∈ Set.Icc 0 1)
    (order : SortedOrder n g) :
    d+(orderedRow (RiskBridge.ofRegular P) α g order.order).payoff =
      Regularity.compactCVaR α (k+1 : ℕ) P (fun s => d+g s) := by
  rw [orderedRow_eq_value _ ha ha1 _ order]
  rw [RiskBridge.compactCVaR_eq_value α (k+1 : ℕ) ha ha1 (by positivity) P (fun s => d+g s)]
  · have he : (fun s => d+g s) = (fun s => g s+d) := by funext s; ring
    rw [he, CVaR.value_add_const _ ha ha1]
    ring
  · intro s
    constructor <;> push_cast <;> linarith [(hg s).1, (hg s).2, hd.1, hd.2]

/-- The scan-based program computes the source's exact minimum-risk recursion. -/
theorem evaluateDP_correct {n m : ℕ} (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → Fin n → Fin (m+1) → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (k h : ℕ) (s : Fin n) :
    (evaluateDP α c q sorter k h).value s = Calibration.dp α c q k h s := by
  induction k generalizing h s with
  | zero => simp [evaluateDP, DPResult.value, Calibration.dp]
  | succ k ih =>
    let tail := evaluateDP α c q sorter k (h+1)
    let order := sorter tail.value
    let f := fun s a => c h s a +
      (orderedRow (RiskBridge.ofRegular (q s a)) α tail.value order.order).payoff
    have hrow (s : Fin n) (a : Fin (m+1)) : f s a =
        Regularity.compactCVaR α (k+1 : ℕ) (q s a)
          (fun t => c h s a + Calibration.dp α c q k (h+1) t) := by
      have hg : ∀ t, tail.value t ∈ Set.Icc 0 (k : ℝ) := by
        intro t
        change (evaluateDP α c q sorter k (h+1)).value t ∈ _
        rw [ih]
        exact dp_bounds α ha.le c hc q k (h+1) t
      have he := row_correct α ha ha1 (q s a) tail.value k hg (c h s a) (hc h s a) order
      have heq : tail.value = fun t => Calibration.dp α c q k (h+1) t := by funext t; exact ih _ _
      simpa only [f, heq] using he
    have hmin := minimumScan_correct m (f s)
    have hvalue : (evaluateDP α c q sorter (k+1) h).value s = (minimumScan m (f s)).value := by
      simp [evaluateDP, DPResult.value, tail, order, f]
    rw [hvalue]
    apply le_antisymm
    · rw [Calibration.dp]
      convert hmin.2.1 _ using 1
      rw [hrow]
    · rw [hmin.1, hrow]
      exact Calibration.dp_le_row α c q k h s _

/-- Arithmetic-cost bound for the actual recursive table evaluator. Sorting is a
single external primitive per stage with an explicit uniform comparison budget;
the SA tail scans and A-action minima have been implemented and counted here. -/
theorem evaluateDP_cost {n m : ℕ} (α : ℝ) (c : ℕ → Fin n → Fin (m+1) → ℝ)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (K : ℕ)
    (hsort : ∀ g, (sorter g).operations ≤ K*n*n) (k h : ℕ) :
    (evaluateDP α c q sorter k h).operations ≤ k * ((K+7)*(m+1)*n*n) := by
  induction k generalizing h with
  | zero => simp [evaluateDP]
  | succ k ih =>
    let tail := evaluateDP α c q sorter k (h+1)
    let order := sorter tail.value
    let rows := Vector.ofFn (fun s : Fin n => Vector.ofFn (fun a : Fin (m+1) =>
      orderedRow (RiskBridge.ofRegular (q s a)) α tail.value order.order))
    let actionTable := Vector.ofFn (fun s : Fin n => Vector.ofFn (fun a : Fin (m+1) =>
      c h s a + (vectorAt (vectorAt rows s) a).payoff))
    let actionValues := fun s a => vectorAt (vectorAt actionTable s) a
    let minima := Vector.ofFn (fun s => minimumScan m (actionValues s))
    have hrows : (∑ s, ∑ a, ((vectorAt (vectorAt rows s) a).operations+1)) ≤
        n*(m+1)*(5*n+1) := by
      calc
        _ ≤ ∑ _s : Fin n, ∑ _a : Fin (m+1), (5*n+1) := by
          apply Finset.sum_le_sum
          intro s _
          apply Finset.sum_le_sum
          intro a _
          have hr := orderedRow_cost (RiskBridge.ofRegular (q s a)) α tail.value order.order
          simpa only [rows, vectorAt_ofFn] using Nat.add_le_add_right hr 1
        _ = _ := by simp [Finset.sum_const, mul_assoc]
    have hminima : (∑ s, (vectorAt minima s).operations) = n*m := by
      have hm : ∀ s, (vectorAt minima s).operations = m := by
        intro s
        simpa only [minima, vectorAt_ofFn] using (minimumScan_correct m (actionValues s)).2.2
      simp [hm]
    have hn : n ≤ n*n := by cases n <;> nlinarith
    have hnprod := Nat.mul_le_mul_left (2*(m+1)) hn
    have hK := Nat.mul_le_mul_left (K*n*n) (show 1 ≤ m+1 by omega)
    have hnm := Nat.mul_le_mul_left n (show m ≤ m+1 by omega)
    have hstage : K*n*n+n*(m+1)*(5*n+1)+n*m ≤ (K+7)*(m+1)*n*n := by
      nlinarith
    have htail : tail.operations ≤ k*((K+7)*(m+1)*n*n) := ih (h+1)
    have hsorting : order.operations ≤ K*n*n := hsort tail.value
    change tail.operations+order.operations+
      (∑ s, ∑ a, ((vectorAt (vectorAt rows s) a).operations+1))+
      (∑ s, (vectorAt minima s).operations) ≤ _
    rw [hminima]
    calc
      _ ≤ k*((K+7)*(m+1)*n*n)+(K*n*n+n*(m+1)*(5*n+1)+n*m) := by omega
      _ ≤ k*((K+7)*(m+1)*n*n)+(K+7)*(m+1)*n*n := Nat.add_le_add_left hstage _
      _ = (k+1)*((K+7)*(m+1)*n*n) := by ring

/-- Proposition 4.1's semantic minimum is computed by the instrumented scan
program, for the full randomized Markov comparator. -/
theorem evaluateDP_eq_minimumRisk {n m : ℕ} (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → Fin n → Fin (m+1) → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (k h : ℕ) (s : Fin n) :
    (evaluateDP α c q sorter k h).value s = Nested.minimumRisk α c k h s q := by
  rw [evaluateDP_correct α ha ha1 c hc q sorter k h s,
    Calibration.minimumRisk_eq_dp α ha.le c q k h s]

/-- Exact minimum risk with O(H A S²) scalar operations, relative only to the
explicit shared-sort primitive. `n` is S and `m+1` is A. -/
theorem proposition4_1_scan {n m : ℕ} (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → Fin n → Fin (m+1) → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (K : ℕ)
    (hsort : ∀ g, (sorter g).operations ≤ K*n*n) (H h : ℕ) (s : Fin n) :
    (evaluateDP α c q sorter H h).value s = Nested.minimumRisk α c H h s q ∧
      (evaluateDP α c q sorter H h).operations ≤ H*((K+7)*(m+1)*n*n) :=
  ⟨evaluateDP_eq_minimumRisk α ha ha1 c hc q sorter H h s,
    evaluateDP_cost α c q sorter K hsort H h⟩

/-! ## The computed action table and its deterministic minimizing policy -/

theorem evaluateDP_action_bound {n m : ℕ} (α : ℝ) (c : ℕ → Fin n → Fin (m+1) → ℝ)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (k h j : ℕ) (s : Fin n) :
    (evaluateDP α c q sorter k h).actions j s < m+1 := by
  induction k generalizing h with
  | zero => simp [evaluateDP]
  | succ k ih =>
    simp only [evaluateDP]
    split_ifs
    · exact Fin.isLt _
    · exact ih (h+1)

/-- All H statewise action vectors are retained as a finite table, in stage order. -/
theorem evaluateDP_actionTables_length {n m : ℕ} (α : ℝ) (c : ℕ → Fin n → Fin (m+1) → ℝ)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (k h : ℕ) :
    (evaluateDP α c q sorter k h).actionTables.length = k := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih => simpa only [evaluateDP, List.length_cons] using congrArg Nat.succ (ih (h+1))

def evaluatedAction {n m : ℕ} (α : ℝ) (c : ℕ → Fin n → Fin (m+1) → ℝ)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (k h j : ℕ) (s : Fin n) : Fin (m+1) :=
  ⟨(evaluateDP α c q sorter k h).actions j s, evaluateDP_action_bound α c q sorter k h j s⟩

def evaluatedPolicy {n m : ℕ} (α : ℝ) (c : ℕ → Fin n → Fin (m+1) → ℝ)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (k h : ℕ) : Nested.Policy (Fin n) (Fin (m+1)) :=
  fun j s => Nested.pure (evaluatedAction α c q sorter k h j s)

theorem evaluatedPolicy_deterministic {n m : ℕ} (α : ℝ) (c : ℕ → Fin n → Fin (m+1) → ℝ)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (k h : ℕ) :
    Calibration.Deterministic (evaluatedPolicy α c q sorter k h) := by
  intro j s
  exact ⟨_, rfl⟩

theorem evaluatedAction_future {n m : ℕ} (α : ℝ) (c : ℕ → Fin n → Fin (m+1) → ℝ)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (k h j : ℕ) (hj : j ≠ h) (s : Fin n) :
    evaluatedAction α c q sorter (k+1) h j s = evaluatedAction α c q sorter k (h+1) j s := by
  apply Fin.ext
  simp [evaluatedAction, evaluateDP, hj]

/-- The action returned at each current state is the actual row minimizer. -/
theorem evaluatedAction_attains_row {n m : ℕ} (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → Fin n → Fin (m+1) → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (k h : ℕ) (s : Fin n) :
    Calibration.dp α c q (k+1) h s = Regularity.compactCVaR α (k+1 : ℕ)
      (q s (evaluatedAction α c q sorter (k+1) h h s))
      (fun t => c h s (evaluatedAction α c q sorter (k+1) h h s) + Calibration.dp α c q k (h+1) t) := by
  let tail := evaluateDP α c q sorter k (h+1)
  let order := sorter tail.value
  let f := fun s a => c h s a + (orderedRow (RiskBridge.ofRegular (q s a)) α tail.value order.order).payoff
  have hg : ∀ t, tail.value t ∈ Set.Icc 0 (k : ℝ) := by
    intro t
    change (evaluateDP α c q sorter k (h+1)).value t ∈ _
    rw [evaluateDP_correct α ha ha1 c hc q sorter]
    exact dp_bounds α ha.le c hc q k (h+1) t
  have hrow (a : Fin (m+1)) : f s a = Regularity.compactCVaR α (k+1 : ℕ) (q s a)
      (fun t => c h s a + Calibration.dp α c q k (h+1) t) := by
    have he := row_correct α ha ha1 (q s a) tail.value k hg (c h s a) (hc h s a) order
    have heq : tail.value = fun t => Calibration.dp α c q k (h+1) t := by
      funext t
      exact evaluateDP_correct α ha ha1 c hc q sorter k (h+1) t
    simpa only [f, heq] using he
  have hvalue : (evaluateDP α c q sorter (k+1) h).value s = (minimumScan m (f s)).value := by
    simp [evaluateDP, DPResult.value, tail, order, f]
  have haction : evaluatedAction α c q sorter (k+1) h h s = (minimumScan m (f s)).index := by
    apply Fin.ext
    simp [evaluatedAction, evaluateDP, tail, order, f]
  calc
    Calibration.dp α c q (k+1) h s = (evaluateDP α c q sorter (k+1) h).value s :=
      (evaluateDP_correct α ha ha1 c hc q sorter (k+1) h s).symm
    _ = (minimumScan m (f s)).value := hvalue
    _ = f s (minimumScan m (f s)).index := (minimumScan_correct m (f s)).1
    _ = f s (evaluatedAction α c q sorter (k+1) h h s) := by rw [haction]
    _ = _ := hrow _

/-- The finite computed action table yields a deterministic Markov policy that
attains the minimum simultaneously at every state. -/
theorem evaluatedPolicy_optimal {n m : ℕ} (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → Fin n → Fin (m+1) → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (k h : ℕ) (s : Fin n) :
    Nested.risk α c (evaluatedPolicy α c q sorter k h) q k h s = Calibration.dp α c q k h s := by
  induction k generalizing h s with
  | zero => rfl
  | succ k ih =>
    let π := evaluatedPolicy α c q sorter (k+1) h
    let tail := evaluatedPolicy α c q sorter k (h+1)
    have htail : ∀ t, Nested.risk α c π q k (h+1) t = Calibration.dp α c q k (h+1) t := by
      intro t
      rw [Nested.risk_congr α c q π tail k (h+1) (fun j hj => ?_) t]
      · exact ih (h+1) t
      · funext u
        change Nested.pure (evaluatedAction α c q sorter (k+1) h j u) =
          Nested.pure (evaluatedAction α c q sorter k (h+1) j u)
        rw [evaluatedAction_future α c q sorter k h j (by omega)]
    change Nested.risk α c π q (k+1) h s = _
    rw [Nested.risk]
    have hπ : π h s = Nested.pure (evaluatedAction α c q sorter (k+1) h h s) := rfl
    rw [hπ, Nested.compactCVaR_joint_pure α (k+1 : ℕ)
      (evaluatedAction α c q sorter (k+1) h h s) (q s)
      (fun a t => c h s a + Nested.risk α c π q k (h+1) t)]
    simp_rw [htail]
    exact (evaluatedAction_attains_row α ha ha1 c hc q sorter k h s).symm

/-- Full action-producing form of Proposition 4.1, with the original explicit
shared sorting primitive boundary. -/
theorem proposition4_1_actions {n m : ℕ} (α : ℝ) (ha : 0 < α) (ha1 : α ≤ 1)
    (c : ℕ → Fin n → Fin (m+1) → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (K : ℕ)
    (hsort : ∀ g, (sorter g).operations ≤ K*n*n) (H h : ℕ) :
    Calibration.Deterministic (evaluatedPolicy α c q sorter H h) ∧
    (∀ s, Nested.risk α c (evaluatedPolicy α c q sorter H h) q H h s = Nested.minimumRisk α c H h s q) ∧
    (evaluateDP α c q sorter H h).actionTables.length = H ∧
    (evaluateDP α c q sorter H h).operations ≤ H*((K+7)*(m+1)*n*n) := by
  refine ⟨evaluatedPolicy_deterministic α c q sorter H h, ?_, evaluateDP_actionTables_length α c q sorter H h,
    evaluateDP_cost α c q sorter K hsort H h⟩
  intro s
  rw [evaluatedPolicy_optimal α ha ha1 c hc q sorter H h s,
    Calibration.minimumRisk_eq_dp α ha.le c q H h s]

/-- The finite returned tables and the policy lookup contain the same computed
actions; no uncomputed minimizer is substituted during policy extraction. -/
theorem evaluateDP_table_lookup {n m : ℕ} (α : ℝ) (c : ℕ → Fin n → Fin (m+1) → ℝ)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (k h j : ℕ) (hj : j < k) (s : Fin n) :
    ((evaluateDP α c q sorter k h).actionTables[j]?).map (fun v => vectorAt v s) =
      some ((evaluateDP α c q sorter k h).actions (h+j) s) := by
  induction k generalizing h j with
  | zero => omega
  | succ k ih =>
    cases j with
    | zero => simp [evaluateDP]
    | succ j =>
      have hj' : j < k := by omega
      have he := ih (h+1) j hj'
      have hn : h+(j+1) ≠ h := by omega
      simpa [evaluateDP, hn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he

/-- The non-asymptotic refined count leaves the single shared sort budget
separate. Taking T=O(S log S) gives the source's H[S log S+A S²] form. -/
theorem evaluateDP_cost_budget {n m : ℕ} (α : ℝ) (c : ℕ → Fin n → Fin (m+1) → ℝ)
    (q : Nested.Kernel (Fin n) (Fin (m+1)))
    (sorter : (g : Fin n → ℝ) → SortedOrder n g) (T : ℕ)
    (hsort : ∀ g, (sorter g).operations ≤ T) (k h : ℕ) :
    (evaluateDP α c q sorter k h).operations ≤ k*(T+n*(m+1)*(5*n+1)+n*m) := by
  induction k generalizing h with
  | zero => simp [evaluateDP]
  | succ k ih =>
    let tail := evaluateDP α c q sorter k (h+1)
    let order := sorter tail.value
    let rows := Vector.ofFn (fun s : Fin n => Vector.ofFn (fun a : Fin (m+1) =>
      orderedRow (RiskBridge.ofRegular (q s a)) α tail.value order.order))
    let actionTable := Vector.ofFn (fun s : Fin n => Vector.ofFn (fun a : Fin (m+1) =>
      c h s a + (vectorAt (vectorAt rows s) a).payoff))
    let actionValues := fun s a => vectorAt (vectorAt actionTable s) a
    let minima := Vector.ofFn (fun s => minimumScan m (actionValues s))
    have hrows : (∑ s, ∑ a, ((vectorAt (vectorAt rows s) a).operations+1)) ≤
        n*(m+1)*(5*n+1) := by
      calc
        _ ≤ ∑ _s : Fin n, ∑ _a : Fin (m+1), (5*n+1) := by
          apply Finset.sum_le_sum
          intro s _
          apply Finset.sum_le_sum
          intro a _
          have hr := orderedRow_cost (RiskBridge.ofRegular (q s a)) α tail.value order.order
          simpa only [rows, vectorAt_ofFn] using Nat.add_le_add_right hr 1
        _ = _ := by simp [Finset.sum_const, mul_assoc]
    have hminima : (∑ s, (vectorAt minima s).operations) = n*m := by
      have hm : ∀ s, (vectorAt minima s).operations = m := by
        intro s
        simpa only [minima, vectorAt_ofFn] using (minimumScan_correct m (actionValues s)).2.2
      simp [hm]
    have htail : tail.operations ≤ k*(T+n*(m+1)*(5*n+1)+n*m) := ih (h+1)
    have hsorting : order.operations ≤ T := hsort tail.value
    change tail.operations+order.operations+
      (∑ s, ∑ a, ((vectorAt (vectorAt rows s) a).operations+1))+
      (∑ s, (vectorAt minima s).operations) ≤ _
    rw [hminima]
    calc
      _ ≤ k*(T+n*(m+1)*(5*n+1)+n*m)+(T+n*(m+1)*(5*n+1)+n*m) := by omega
      _ = (k+1)*(T+n*(m+1)*(5*n+1)+n*m) := by ring

end
end Paper36.CalibrationScan
