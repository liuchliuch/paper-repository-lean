import Paper36.RowTapes
import Paper36.Counts
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.List.OfFn

/-! Finite row stacks for adaptive sampling. The raw tape law is a constructed
product law, and every unused-coordinate statement is proved from that product. -/
namespace Paper36.AdaptiveTapes
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I J S Row : Type*} [Fintype I] [Fintype J] [Fintype S] [Fintype Row]
  [DecidableEq I] [DecidableEq J] [DecidableEq Row]

/-- Independent categorical coordinates, with potentially different coordinate laws. -/
def productLaw (P : I → Law S) : Law (I → S) where
  mass tape := ∏ i, (P i).mass (tape i)
  nonneg tape := Finset.prod_nonneg fun i _ => (P i).nonneg _
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp [Law.total]

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

lemma lawMeasure_singleton (P : Law S) (s : S) :
    lawMeasure P {s} = ENNReal.ofReal (P.mass s) := by
  rw [lawMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rfl

/-- A finite-law draw lies in the positive-mass support almost surely. -/
lemma ae_positive_mass (P : Law S) : ∀ᵐ s ∂lawMeasure P, 0 < P.mass s := by
  classical
  rw [ae_iff]
  unfold lawMeasure
  rw [PMF.toMeasure_apply_fintype]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : 0 < P.mass s
  · simp [Set.indicator, hs]
  · have hz : P.mass s = 0 := le_antisymm (le_of_not_gt hs) (P.nonneg s)
    simp [Set.indicator, hs, lawPMF, hz]

/-- Our finite real-mass construction is exactly the standard product measure. -/
theorem lawMeasure_productLaw (P : I → Law S) :
    lawMeasure (productLaw P) = Measure.pi (fun i => lawMeasure (P i)) := by
  classical
  apply Measure.ext_of_singleton
  intro tape
  rw [lawMeasure_singleton, ← Set.univ_pi_singleton tape, Measure.pi_pi]
  simp only [lawMeasure_singleton, productLaw]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => (P i).nonneg _)

/-- Any injective collection of coordinates remains independent, with its exact laws. -/
theorem product_projection (P : I → Law S) (e : J ↪ I) :
    (lawMeasure (productLaw P)).map (fun tape j => tape (e j)) =
      lawMeasure (productLaw (fun j => P (e j))) := by
  classical
  rw [lawMeasure_productLaw, lawMeasure_productLaw]
  have hind : iIndepFun (fun i (tape : I → S) => tape i)
      (Measure.pi (fun i => lawMeasure (P i))) := by
    simpa using (iIndepFun_pi (μ := fun i => lawMeasure (P i))
      (X := fun _ (s : S) => s) (fun _ => aemeasurable_id))
  have hsel := hind.precomp e.injective
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map
    (fun j => (measurable_pi_apply (e j)).aemeasurable)).mp hsel
  have heval : ∀ j, (Measure.pi (fun i => lawMeasure (P i))).map
      (fun tape : I → S => tape (e j)) = lawMeasure (P (e j)) := by
    intro j
    exact (measurePreserving_eval (fun i => lawMeasure (P i)) (e j)).map_eq
  simpa only [heval] using hmap

/-- A stack for each row, with a common remaining capacity. -/
abbrev Stack (Row S : Type*) (n : ℕ) := Row × Fin n → S

/-- One head is exposed. Other rows discard only their last, still-unused coordinate. -/
def popIndex (r : Row) (n : ℕ) : Option (Row × Fin n) → Row × Fin (n+1)
  | none => (r, 0)
  | some (q,i) => (q, if q = r then i.succ else i.castSucc)

theorem popIndex_injective (r : Row) (n : ℕ) :
    Function.Injective (popIndex r n) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      rcases y with ⟨q,i⟩
      have hr : r = q := congrArg Prod.fst h
      subst q
      have hi := congrArg (fun z : Row × Fin (n+1) => z.2.val) h
      simp [popIndex] at hi
  | some x =>
    cases y with
    | none =>
      rcases x with ⟨q,i⟩
      have hr : q = r := congrArg Prod.fst h
      subst q
      have hi := congrArg (fun z : Row × Fin (n+1) => z.2.val) h
      simp [popIndex] at hi
    | some y =>
      rcases x with ⟨q,i⟩
      rcases y with ⟨q',j⟩
      have hr : q = q' := congrArg Prod.fst h
      subst q'
      have hi := congrArg (fun z : Row × Fin (n+1) => z.2.val) h
      have hij : i = j := by
        apply Fin.ext
        by_cases hq : q = r <;> simpa [popIndex, hq] using hi
      subst j
      rfl

def head {n : ℕ} (r : Row) (tape : Stack Row S (n+1)) : S := tape (r,0)

def remaining {n : ℕ} (r : Row) (tape : Stack Row S (n+1)) : Stack Row S n :=
  fun c => tape (popIndex r n (some c))

def stackLaw (P : Row → Law S) (n : ℕ) : Law (Stack Row S n) :=
  productLaw fun c : Row × Fin n => P c.1

/-- Exact unused-stack independence after popping any chosen row. -/
theorem pop_law (P : Row → Law S) (r : Row) (n : ℕ) :
    (lawMeasure (stackLaw P (n+1))).map
      (fun tape => (remaining r tape, head r tape)) =
      (lawMeasure (stackLaw P n)).prod (lawMeasure (P r)) := by
  classical
  let e : Option (Row × Fin n) ↪ Row × Fin (n+1) :=
    ⟨popIndex r n, popIndex_injective r n⟩
  let split := MeasurableEquiv.piOptionEquivProd (fun _ : Option (Row × Fin n) => S)
  have hproj := product_projection (fun c : Row × Fin (n+1) => P c.1) e
  have hsplit := Measure.pi_map_piOptionEquivProd
    (fun c : Option (Row × Fin n) => lawMeasure (P (e c).1))
  have hsplit' := congrArg (fun ν => ν.map split) hsplit
  dsimp only at hsplit'
  change (((Measure.pi fun c : Row × Fin n => lawMeasure (P c.1)).prod (lawMeasure (P r))).map split.symm).map split = _ at hsplit'
  rw [MeasurableEquiv.map_map_symm] at hsplit'
  have hmap := congrArg (fun ν => ν.map split) hproj
  dsimp only at hmap
  rw [Measure.map_map split.measurable (by fun_prop)] at hmap
  simp only [lawMeasure_productLaw] at hmap
  rw [← hsplit'] at hmap
  simp only [stackLaw, lawMeasure_productLaw]
  convert hmap using 1

/-- Pop/Fubini identity. The sampled head has its row law and is independent of all unused entries. -/
theorem pop_expect (P : Row → Law S) (r : Row) (n : ℕ)
    (f : S → Stack Row S n → ℝ) :
    expect (stackLaw P (n+1)).mass (fun tape => f (head r tape) (remaining r tape)) =
      expect (P r).mass (fun y => expect (stackLaw P n).mass (f y)) := by
  have hmap := pop_law P r n
  have hi : Integrable (fun z : Stack Row S n × S => f z.2 z.1)
      ((lawMeasure (stackLaw P n)).prod (lawMeasure (P r))) := .of_finite
  calc
    _ = ∫ tape, f (head r tape) (remaining r tape) ∂lawMeasure (stackLaw P (n+1)) :=
      (integral_lawMeasure _ _).symm
    _ = ∫ z, f z.2 z.1 ∂(lawMeasure (stackLaw P (n+1))).map
        (fun tape => (remaining r tape, head r tape)) :=
      (integral_map (φ := fun tape : Stack Row S (n+1) => (remaining r tape, head r tape))
        (f := fun z : Stack Row S n × S => f z.2 z.1)
        Measurable.of_discrete.aemeasurable Measurable.of_discrete.aestronglyMeasurable).symm
    _ = ∫ z, f z.2 z.1 ∂(lawMeasure (stackLaw P n)).prod (lawMeasure (P r)) := by rw [hmap]
    _ = ∫ y, ∫ tape, f y tape ∂lawMeasure (stackLaw P n) ∂lawMeasure (P r) :=
      integral_prod_symm _ hi
    _ = _ := by simp_rw [integral_lawMeasure]

lemma expect_swap {X Y : Type*} [Fintype X] [Fintype Y]
    (P : Law X) (Q : Law Y) (f : X → Y → ℝ) :
    expect P.mass (fun x => expect Q.mass (f x)) =
      expect Q.mass (fun y => expect P.mass (fun x => f x y)) := by
  simp only [expect, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

section Adaptive
variable {Hist : Type*}

/-- Evaluation of an arbitrary history-dependent randomized row strategy on raw stacks. -/
def tapedValue (choose : Hist → Law Row) (update : Hist → Row → S → Hist)
    (payoff : Hist → ℝ) : (n : ℕ) → Hist → Stack Row S n → ℝ
  | 0, h, _ => payoff h
  | n+1, h, tape => expect (choose h).mass (fun r =>
      tapedValue choose update payoff n (update h r (head r tape)) (remaining r tape))

/-- The original online protocol: each selected row supplies a fresh transition. -/
def onlineValue (P : Row → Law S) (choose : Hist → Law Row)
    (update : Hist → Row → S → Hist) (payoff : Hist → ℝ) : ℕ → Hist → ℝ
  | 0, h => payoff h
  | n+1, h => expect (choose h).mass (fun r => expect (P r).mass (fun y =>
      onlineValue P choose update payoff n (update h r y)))

/-- Finite adaptive row-stack coupling for all initial histories and terminal payoffs.
The strategy is arbitrary and can use the entire observed history at every step. -/
theorem adaptive_stack_coupling (P : Row → Law S) (choose : Hist → Law Row)
    (update : Hist → Row → S → Hist) (payoff : Hist → ℝ) (n : ℕ) (h : Hist) :
    expect (stackLaw P n).mass (tapedValue choose update payoff n h) =
      onlineValue P choose update payoff n h := by
  induction n generalizing h with
  | zero => exact expect_const (stackLaw P 0).total _
  | succ n ih =>
    change expect (stackLaw P (n+1)).mass (fun tape => expect (choose h).mass (fun r =>
      tapedValue choose update payoff n (update h r (head r tape)) (remaining r tape))) = _
    rw [expect_swap]
    unfold onlineValue
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    dsimp only
    have hpop := pop_expect P r n (fun y tape =>
      tapedValue choose update payoff n (update h r y) tape)
    apply hpop.trans
    apply Finset.sum_congr rfl
    intro y _
    exact congrArg ((P r).mass y * ·) (ih (update h r y))

/-- The coupling identity is pointwise in any latent model/auxiliary parameter,
so integration preserves it for every prior without a factorization restriction. -/
theorem adaptive_stack_coupling_integrated {M : Type*} [MeasurableSpace M]
    (prior : Measure M) (P : M → Row → Law S) (choose : M → Hist → Law Row)
    (update : M → Hist → Row → S → Hist) (payoff : M → Hist → ℝ)
    (initial : M → Hist) (n : ℕ) :
    (∫ m, expect (stackLaw (P m) n).mass
      (tapedValue (choose m) (update m) (payoff m) n (initial m)) ∂prior) =
      ∫ m, onlineValue (P m) (choose m) (update m) (payoff m) n (initial m) ∂prior := by
  apply integral_congr_ae
  exact ae_of_all _ fun m => adaptive_stack_coupling (P m) (choose m) (update m) (payoff m) n (initial m)

/-- Adaptive reads with a terminal payoff that also inspects every unused coordinate. -/
def residualValue (choose : Hist → Law Row) (update : Hist → Row → S → Hist)
    (L : ℕ) (payoff : Hist → Stack Row S L → ℝ) :
    (n : ℕ) → Hist → Stack Row S (L+n) → ℝ
  | 0, h, tape => payoff h tape
  | n+1, h, tape => expect (choose h).mass (fun r =>
      residualValue choose update L payoff n (update h r (head r tape)) (remaining r tape))

/-- The complete adaptive unused-stack invariant: the terminal history and all
unused stacks have the online history law times an independent fresh product law. -/
theorem adaptive_unused_independent (P : Row → Law S) (choose : Hist → Law Row)
    (update : Hist → Row → S → Hist) (L : ℕ) (payoff : Hist → Stack Row S L → ℝ)
    (n : ℕ) (h : Hist) :
    expect (stackLaw P (L+n)).mass (residualValue choose update L payoff n h) =
      onlineValue P choose update (fun h => expect (stackLaw P L).mass (payoff h)) n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    change expect (stackLaw P (L+n+1)).mass (fun tape => expect (choose h).mass (fun r =>
      residualValue choose update L payoff n (update h r (head r tape)) (remaining r tape))) = _
    rw [expect_swap]
    unfold onlineValue
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    dsimp only
    have hpop := pop_expect P r (L+n) (fun y tape =>
      residualValue choose update L payoff n (update h r y) tape)
    apply hpop.trans
    apply Finset.sum_congr rfl
    intro y _
    exact congrArg ((P r).mass y * ·) (ih (update h r y))

end Adaptive

/-- A window into the original stacks starts exactly at each row's consumed count. -/
def window (tape : Row → ℕ → S) (counts : Row → ℕ) (n : ℕ) : Stack Row S n :=
  fun c => tape c.1 (counts c.1+c.2.val)

def increment (counts : Row → ℕ) (r : Row) : Row → ℕ :=
  fun q => counts q + if q = r then 1 else 0

@[simp] theorem head_window (tape : Row → ℕ → S) (counts : Row → ℕ) (n : ℕ) (r : Row) :
    head r (window tape counts (n+1)) = tape r (counts r) := by simp [head, window]

/-- Pop consumes one entry from exactly the selected row; all other row heads persist. -/
theorem remaining_window (tape : Row → ℕ → S) (counts : Row → ℕ) (n : ℕ) (r : Row) :
    remaining r (window tape counts (n+1)) = window tape (increment counts r) n := by
  funext c
  rcases c with ⟨q,i⟩
  by_cases hq : q = r
  · subst q
    simp [remaining, window, popIndex, increment, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simp [remaining, window, popIndex, increment, hq]

/-- All observed successor values belonging to a row, in their actual reveal order. -/
def rowObservations (history : List (Row × S)) (r : Row) : List S :=
  (history.filter fun z => z.1 = r).map Prod.snd

def rowCount (history : List (Row × S)) (r : Row) : ℕ := (rowObservations history r).length

/-- Observed data are exactly the revealed prefix, with no empirical-law identity postulated. -/
def PrefixCompatible (tape : Row → ℕ → S) (history : List (Row × S)) : Prop :=
  ∀ r, rowObservations history r = List.ofFn (fun i : Fin (rowCount history r) => tape r i.val)

@[simp] theorem rowObservations_append (history : List (Row × S)) (r q : Row) (y : S) :
    rowObservations (history ++ [(r,y)]) q =
      rowObservations history q ++ if r = q then [y] else [] := by
  by_cases h : r = q <;> simp [rowObservations, List.filter_append, h]

@[simp] theorem rowCount_append (history : List (Row × S)) (r q : Row) (y : S) :
    rowCount (history ++ [(r,y)]) q = rowCount history q + if q = r then 1 else 0 := by
  by_cases h : r = q <;> simp [rowCount, h, eq_comm]

/-- The prefix compatibility invariant is preserved by an actual stack read. -/
theorem prefixCompatible_append (tape : Row → ℕ → S) (history : List (Row × S))
    (h : PrefixCompatible tape history) (r : Row) :
    PrefixCompatible tape (history ++ [(r,tape r (rowCount history r))]) := by
  intro q
  rw [rowObservations_append]
  by_cases hq : r = q
  · subst q
    rw [if_pos rfl, rowCount_append]
    simp only [if_pos rfl]
    rw [List.ofFn_succ']
    simpa [h r, List.concat_eq_append]
  · have hqr : q ≠ r := Ne.symm hq
    rw [if_neg hq, List.append_nil, rowCount_append, if_neg hqr, Nat.add_zero]
    exact h q

/-- Direct adaptive reads of the original tapes. -/
def runTape (choose : List (Row × S) → Row) (tape : Row → ℕ → S) :
    ℕ → List (Row × S) → List (Row × S)
  | 0, history => history
  | n+1, history =>
      let r := choose history
      runTape choose tape n (history ++ [(r,tape r (rowCount history r))])

theorem runTape_prefixCompatible (choose : List (Row × S) → Row) (tape : Row → ℕ → S)
    (n : ℕ) (history : List (Row × S)) (h : PrefixCompatible tape history) :
    PrefixCompatible tape (runTape choose tape n history) := by
  induction n generalizing history with
  | zero => exact h
  | succ n ih => exact ih _ (prefixCompatible_append tape history h _)

/-- Empty-history execution reveals actual iid tape prefixes at every adaptive count. -/
theorem observed_prefix (choose : List (Row × S) → Row) (tape : Row → ℕ → S)
    (n : ℕ) (r : Row) :
    rowObservations (runTape choose tape n []) r =
      List.ofFn (fun i : Fin (rowCount (runTape choose tape n []) r) => tape r i.val) := by
  exact runTape_prefixCompatible choose tape n [] (by intro q; simp [PrefixCompatible, rowCount, rowObservations]) r

/-- Deterministic stack execution records the same revealed rows and successors. -/
def runStack (choose : List (Row × S) → Row) :
    (n : ℕ) → List (Row × S) → Stack Row S n → List (Row × S)
  | 0, history, _ => history
  | n+1, history, tape =>
      let r := choose history
      runStack choose n (history ++ [(r,head r tape)]) (remaining r tape)

/-- The finite pop construction reads exactly the original row offsets. -/
theorem runStack_window (choose : List (Row × S) → Row) (tape : Row → ℕ → S)
    (n : ℕ) (history : List (Row × S)) :
    runStack choose n history (window tape (rowCount history) n) = runTape choose tape n history := by
  induction n generalizing history with
  | zero => rfl
  | succ n ih =>
    simp only [runStack, runTape, head_window, remaining_window]
    have hc : increment (rowCount history) (choose history) =
        rowCount (history ++ [(choose history, tape (choose history) (rowCount history (choose history)))]) := by
      funext r
      rw [rowCount_append]
      rfl
    rw [hc, ih]

/-- Actual count bounds are a consequence of the observed list, not an assumption. -/
theorem rowCount_le_length (history : List (Row × S)) (r : Row) : rowCount history r ≤ history.length := by
  simpa [rowCount, rowObservations] using List.length_filter_le (fun z : Row × S => z.1 = r) history

theorem runTape_length (choose : List (Row × S) → Row) (tape : Row → ℕ → S)
    (n : ℕ) (history : List (Row × S)) :
    (runTape choose tape n history).length = history.length+n := by
  induction n generalizing history with
  | zero => simp [runTape]
  | succ n ih => simp [runTape, ih]; omega

/-- Every chosen row's start count is the number of previous observations of that row. -/
theorem adaptive_count_bound (choose : List (Row × S) → Row) (tape : Row → ℕ → S)
    (n : ℕ) (r : Row) : rowCount (runTape choose tape n []) r ≤ n := by
  have h := rowCount_le_length (runTape choose tape n []) r
  simpa [runTape_length] using h

section MarkovEpisodes
universe v
variable {State Action : Type v} [Fintype State] [Fintype Action]
  [DecidableEq State] [DecidableEq Action]
  [MeasurableSpace State] [DiscreteMeasurableSpace State]

/-- The actual action-randomized Markov episode run on the same pre-generated stacks. -/
def tapedTrajectory (π : Simulation.Policy State Action) :
    (n : ℕ) → ℕ → State → Stack (State × Action) State n → Law (Trajectory State Action n)
  | 0, _, s, _ => Simulation.dirac s
  | n+1, h, s, tape => joint (Simulation.dirac s) (fun u => joint (π h u)
      (fun a => tapedTrajectory π n (h+1) (head (u,a) tape) (remaining (u,a) tape)))

lemma expect_mul_const {X : Type*} [Fintype X] (P : Law X) (c : ℝ) (f : X → ℝ) :
    expect P.mass (fun x => c*f x) = c*expect P.mass f := by
  simp only [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Canonical tapes generate exactly the source physical-state Markov trajectory law. -/
theorem tapedTrajectory_mass_average (π : Simulation.Policy State Action)
    (p : Simulation.Kernel State Action) (n h : ℕ) (s : State) (path : Trajectory State Action n) :
    expect (stackLaw (fun r : State × Action => p r.1 r.2) n).mass
      (fun tape => (tapedTrajectory π n h s tape).mass path) =
      (trajectoryLaw π p n h s).mass path := by
  induction n generalizing h s with
  | zero => exact expect_const (stackLaw _ 0).total _
  | succ n ih =>
    rcases path with ⟨u,a,rest⟩
    simp only [tapedTrajectory, trajectoryLaw, joint, bindLaw, ← mul_assoc]
    change expect (stackLaw (fun r : State × Action => p r.1 r.2) (n+1)).mass
      (fun tape => ((Simulation.dirac s).mass u*(π h u).mass a)*
        (tapedTrajectory π n (h+1) (head (u,a) tape) (remaining (u,a) tape)).mass rest) =
      ((Simulation.dirac s).mass u*(π h u).mass a)*
        (∑ t, (p u a).mass t*(trajectoryLaw π p n (h+1) t).mass rest)
    rw [expect_mul_const]
    congr 1
    have hp := pop_expect (fun r : State × Action => p r.1 r.2) (u,a) n
      (fun y tape => (tapedTrajectory π n (h+1) y tape).mass rest)
    apply hp.trans
    apply Finset.sum_congr rfl
    intro y _
    exact congrArg ((p u a).mass y * ·) (ih (h+1) y rest)

/-- All finite test functions have the exact original episode expectation. -/
theorem tapedTrajectory_expect_average (π : Simulation.Policy State Action)
    (p : Simulation.Kernel State Action) (n h : ℕ) (s : State)
    (f : Trajectory State Action n → ℝ) :
    expect (stackLaw (fun r : State × Action => p r.1 r.2) n).mass
      (fun tape => expect (tapedTrajectory π n h s tape).mass f) =
      expect (trajectoryLaw π p n h s).mass f := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro path _
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  exact congrArg (· * f path) (tapedTrajectory_mass_average π p n h s path)

def initialState : (n : ℕ) → Trajectory State Action n → State
  | 0, path => path
  | _+1, path => path.1

/-- Each record contains the visited row and the actual observed successor. -/
def transitionTrace : (n : ℕ) → Trajectory State Action n → List ((State × Action) × State)
  | 0, _ => []
  | n+1, path => ((path.1,path.2.1),initialState n path.2.2)::transitionTrace n path.2.2

theorem tapedTrajectory_initial (π : Simulation.Policy State Action) (n h : ℕ) (s : State)
    (tape : Stack (State × Action) State n) (path : Trajectory State Action n)
    (hp : 0 < (tapedTrajectory π n h s tape).mass path) : initialState n path = s := by
  cases n with
  | zero =>
    change path = s
    by_contra hn
    simpa [tapedTrajectory, Simulation.dirac, hn, Ne.symm hn] using hp
  | succ n =>
    change path.1 = s
    by_contra hn
    simpa [tapedTrajectory, joint, Simulation.dirac, hn, Ne.symm hn] using hp

/-- Every positive-probability trajectory observes the original row tape in prefix order. -/
theorem tapedTrajectory_prefixCompatible (π : Simulation.Policy State Action)
    (original : (State × Action) → ℕ → State) (n : ℕ)
    (history : List ((State × Action) × State)) (hcompat : PrefixCompatible original history)
    (stage : ℕ) (s : State) (path : Trajectory State Action n)
    (hp : 0 < (tapedTrajectory π n stage s (window original (rowCount history) n)).mass path) :
    initialState n path = s ∧ PrefixCompatible original (history ++ transitionTrace n path) := by
  induction n generalizing history stage s with
  | zero =>
    exact ⟨tapedTrajectory_initial π 0 stage s _ path hp, by simpa [transitionTrace] using hcompat⟩
  | succ n ih =>
    rcases path with ⟨u,a,rest⟩
    let r : State × Action := (u,a)
    let y := original r (rowCount history r)
    let history' := history ++ [(r,y)]
    have hc' : PrefixCompatible original history' := prefixCompatible_append original history hcompat r
    have hcounts : increment (rowCount history) r = rowCount history' := by
      funext q
      rw [show history' = history ++ [(r,y)] from rfl, rowCount_append]
      rfl
    have hremain : remaining r (window original (rowCount history) (n+1)) =
        window original (rowCount history') n := by rw [remaining_window, hcounts]
    have hsub : 0 < (tapedTrajectory π n (stage+1)
        (head r (window original (rowCount history) (n+1)))
        (remaining r (window original (rowCount history) (n+1)))).mass rest := by
      by_contra hn
      have hz := le_antisymm (le_of_not_gt hn)
        ((tapedTrajectory π n (stage+1)
          (head r (window original (rowCount history) (n+1)))
          (remaining r (window original (rowCount history) (n+1)))).nonneg rest)
      have hz' : (tapedTrajectory π (n+1) stage s
          (window original (rowCount history) (n+1))).mass (u,a,rest) = 0 := by
        simp only [tapedTrajectory, joint]
        change (Simulation.dirac s).mass u*((π stage u).mass a*_) = 0
        rw [hz, mul_zero, mul_zero]
      linarith
    rw [head_window, hremain] at hsub
    have hrec := ih history' hc' (stage+1) y rest hsub
    refine ⟨tapedTrajectory_initial π (n+1) stage s _ (u,a,rest) hp, ?_⟩
    change PrefixCompatible original (history ++ (((u,a),initialState n rest)::transitionTrace n rest))
    rw [hrec.1]
    simpa [history', r, List.append_assoc] using hrec.2

lemma rowCount_append_trace (history : List ((State × Action) × State))
    (n : ℕ) (path : Trajectory State Action n) (row : State × Action) :
    rowCount (history ++ transitionTrace n path) row = rowCount history row+visitCount row n path := by
  induction n generalizing history with
  | zero => simp [transitionTrace, visitCount]
  | succ n ih =>
    change rowCount (history ++ (((path.1,path.2.1),initialState n path.2.2)::transitionTrace n path.2.2)) row = _
    have he : history ++ (((path.1,path.2.1),initialState n path.2.2)::transitionTrace n path.2.2) =
        (history ++ [((path.1,path.2.1),initialState n path.2.2)]) ++ transitionTrace n path.2.2 := by simp
    rw [he, ih, rowCount_append]
    simp only [visitCount]
    by_cases hn : (path.1,path.2.1) = row
    · rw [hn]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    · have hnr : row ≠ (path.1,path.2.1) := Ne.symm hn
      simp [hn, hnr]

/-- The history used by the learner is the actual concatenation of recorded episodes. -/
def episodeHistory (T : ℕ) (paths : ℕ → Trajectory State Action T) : ℕ → List ((State × Action) × State)
  | 0 => []
  | k+1 => episodeHistory T paths k ++ transitionTrace T (paths k)

/-- Source episode-start counts are derived exactly from observed trajectories. -/
theorem episodeHistory_count_prefix (T : ℕ) (paths : ℕ → Trajectory State Action T)
    (k : ℕ) (row : State × Action) :
    rowCount (episodeHistory T paths k) row = Counts.before (fun j => visitCount row T (paths j)) k := by
  induction k with
  | zero => simp [episodeHistory, rowCount, rowObservations]
  | succ k ih => rw [episodeHistory, rowCount_append_trace, ih, Counts.before_succ]

/-- Canonical joint distribution of raw unused stacks and the trajectory they generate. -/
def tapedEpisodeLaw (π : Simulation.Policy State Action) (p : Simulation.Kernel State Action)
    (n h : ℕ) (s : State) : Law (Stack (State × Action) State n × Trajectory State Action n) :=
  joint (stackLaw (fun r : State × Action => p r.1 r.2) n) (tapedTrajectory π n h s)

lemma law_ext {X : Type*} [Fintype X] {P Q : Law X} (hmass : P.mass = Q.mass) : P = Q := by
  cases P
  cases Q
  cases hmass
  rfl

lemma lawMeasure_joint_snd {X Y : Type v} [Fintype X] [Fintype Y]
    [MeasurableSpace X] [MeasurableSpace Y] [DiscreteMeasurableSpace X] [DiscreteMeasurableSpace Y]
    (P : Law X) (Q : X → Law Y) :
    (lawMeasure (joint P Q)).map Prod.snd = lawMeasure (bindLaw P Q) := by
  classical
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.map_apply measurable_snd (measurableSet_singleton _), lawMeasure_singleton]
  unfold lawMeasure
  rw [PMF.toMeasure_apply_fintype]
  simp only [lawPMF, PMF.ofFintype_apply, Fintype.sum_prod_type]
  change (∑ x, ∑ z, if z = y then ENNReal.ofReal (P.mass x*(Q x).mass z) else 0) =
    ENNReal.ofReal (∑ x, P.mass x*(Q x).mass y)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact (ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (P.nonneg x) ((Q x).nonneg y))).symm

/-- The generated canonical tape/episode law has exactly the source trajectory marginal. -/
theorem tapedEpisodeLaw_trajectory (π : Simulation.Policy State Action) (p : Simulation.Kernel State Action)
    (n h : ℕ) (s : State) :
    (lawMeasure (tapedEpisodeLaw π p n h s)).map Prod.snd = lawMeasure (trajectoryLaw π p n h s) := by
  unfold tapedEpisodeLaw
  rw [lawMeasure_joint_snd]
  congr 1
  apply law_ext
  funext path
  exact tapedTrajectory_mass_average π p n h s path

section EpisodeKernels
variable {Info : Type*} [MeasurableSpace Info]

lemma measurable_tapedTrajectory_mass
    (πOf : Info → Simulation.Policy State Action)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (n h : ℕ) (s : State) (tape : Stack (State × Action) State n)
    (path : Trajectory State Action n) :
    Measurable (fun i => (tapedTrajectory (πOf i) n h s tape).mass path) := by
  induction n generalizing h s with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun i => (Simulation.dirac s).mass path.1 *
      ((πOf i h path.1).mass path.2.1 *
        (tapedTrajectory (πOf i) n (h+1) (head (path.1,path.2.1) tape)
          (remaining (path.1,path.2.1) tape)).mass path.2.2))
    exact measurable_const.mul ((hπ h path.1 path.2.1).mul (ih _ _ _ _))

/-- Measurable canonical kernel that samples unused raw stacks and then executes the actual episode. -/
def tapedEpisodeKernel
    (πOf : Info → Simulation.Policy State Action) (pOf : Info → Simulation.Kernel State Action)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (n : ℕ) (s₀ : State) :
    ProbabilityTheory.Kernel Info (Stack (State × Action) State n × Trajectory State Action n) :=
  lawKernel (fun i => tapedEpisodeLaw (πOf i) (pOf i) n 0 s₀) (fun z => by
    change Measurable (fun i =>
      (∏ c : (State × Action) × Fin n, (pOf i c.1.1 c.1.2).mass (z.1 c)) *
        (tapedTrajectory (πOf i) n 0 s₀ z.1).mass z.2)
    exact (Finset.measurable_prod _ (fun c _ => hp c.1.1 c.1.2 (z.1 c))).mul
      (measurable_tapedTrajectory_mass πOf hπ n 0 s₀ z.1 z.2))

instance tapedEpisodeKernel_markov
    (πOf : Info → Simulation.Policy State Action) (pOf : Info → Simulation.Kernel State Action)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (n : ℕ) (s₀ : State) : IsMarkovKernel (tapedEpisodeKernel πOf pOf hπ hp n s₀) :=
  lawKernel_markov _ _

/-- Forgetting the unused stacks yields the exact canonical episode kernel. -/
theorem tapedEpisodeKernel_trajectory
    (πOf : Info → Simulation.Policy State Action) (pOf : Info → Simulation.Kernel State Action)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (n : ℕ) (s₀ : State) :
    (tapedEpisodeKernel πOf pOf hπ hp n s₀).map Prod.snd = trajectoryKernel πOf pOf hπ hp n s₀ := by
  ext i B hB
  rw [Kernel.map_apply _ measurable_snd]
  change ((lawMeasure (tapedEpisodeLaw (πOf i) (pOf i) n 0 s₀)).map Prod.snd) B =
    (lawMeasure (trajectoryLaw (πOf i) (pOf i) n 0 s₀)) B
  rw [tapedEpisodeLaw_trajectory]

/-- A generated tape/trajectory sample has the source conditional trajectory law.
The source law is a conclusion here, obtained by marginalizing the actual tape execution. -/
theorem conditional_trajectory_of_tapedEpisode
    [Nonempty State] [Nonempty Action]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (πOf : Info → Simulation.Policy State Action) (pOf : Info → Simulation.Kernel State Action)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (n : ℕ) (s₀ : State) (info : Ω → Info)
    (sample : Ω → Stack (State × Action) State n × Trajectory State Action n)
    (hsample : AEMeasurable sample μ)
    (hgen : condDistrib sample info μ =ᵐ[μ.map info] tapedEpisodeKernel πOf pOf hπ hp n s₀) :
    condDistrib (fun ω => (sample ω).2) info μ =ᵐ[μ.map info] trajectoryKernel πOf pOf hπ hp n s₀ := by
  have hc := condDistrib_comp (μ := μ) (Y := sample)
    (mβ := (inferInstance : MeasurableSpace Info)) info hsample (f := Prod.snd) measurable_snd
  filter_upwards [hc, hgen] with i hc hg
  change condDistrib (Prod.snd ∘ sample) info μ i = _
  rw [hc, Kernel.map_apply _ measurable_snd, hg]
  have hkernel := tapedEpisodeKernel_trajectory πOf pOf hπ hp n s₀
  have hval := congrArg (fun κ => κ i) hkernel
  dsimp only at hval
  rw [Kernel.map_apply _ measurable_snd] at hval
  exact hval

end EpisodeKernels

/-- Empirical row law computed only from the actual observed successor list. -/
def observedEmpirical (fallback : State) (history : List ((State × Action) × State))
    (row : State × Action) : Law State :=
  if hn : 0 < rowCount history row then
    RowTapes.empirical hn (fun i => ((rowObservations history row)[i.val]?).getD fallback)
  else Simulation.dirac fallback

/-- The history-defined empirical law is exactly the iid tape prefix at its actual count. -/
theorem observedEmpirical_eq_tape (fallback : State)
    (tape : (State × Action) → ℕ → State) (history : List ((State × Action) × State))
    (hcompat : PrefixCompatible tape history) (row : State × Action)
    (hn : 0 < rowCount history row) :
    observedEmpirical fallback history row =
      RowTapes.empirical hn (fun i : Fin (rowCount history row) => tape row i.val) := by
  unfold observedEmpirical
  rw [dif_pos hn]
  congr 1
  funext i
  rw [hcompat row]
  simp [List.getElem?_ofFn, i.isLt]

/-- The observed-prefix interface follows from the same tape execution that gives E.model. -/
theorem tapedTrajectory_observedEmpirical (π : Simulation.Policy State Action)
    (original : (State × Action) → ℕ → State) (n : ℕ)
    (history : List ((State × Action) × State)) (hcompat : PrefixCompatible original history)
    (stage : ℕ) (s : State) (path : Trajectory State Action n)
    (hp : 0 < (tapedTrajectory π n stage s (window original (rowCount history) n)).mass path)
    (row : State × Action) (hn : 0 < rowCount (history ++ transitionTrace n path) row) :
    observedEmpirical s (history ++ transitionTrace n path) row =
      RowTapes.empirical hn (fun i : Fin (rowCount (history ++ transitionTrace n path) row) => original row i.val) :=
  observedEmpirical_eq_tape s original _ (tapedTrajectory_prefixCompatible π original n history hcompat stage s path hp).2 row hn

/-- Prefix compatibility holds almost surely under the actual tape-generated episode law. -/
theorem tapedTrajectory_ae_prefixCompatible (π : Simulation.Policy State Action)
    (original : (State × Action) → ℕ → State) (n : ℕ)
    (history : List ((State × Action) × State)) (hcompat : PrefixCompatible original history)
    (stage : ℕ) (s : State) :
    ∀ᵐ path ∂lawMeasure (tapedTrajectory π n stage s (window original (rowCount history) n)),
      PrefixCompatible original (history ++ transitionTrace n path) := by
  filter_upwards [ae_positive_mass (tapedTrajectory π n stage s (window original (rowCount history) n))]
    with path hp
  exact (tapedTrajectory_prefixCompatible π original n history hcompat stage s path hp).2

/-- The empirical-prefix record is an almost-sure theorem of the generated execution. -/
theorem tapedTrajectory_ae_observedEmpirical (π : Simulation.Policy State Action)
    (original : (State × Action) → ℕ → State) (n : ℕ)
    (history : List ((State × Action) × State)) (hcompat : PrefixCompatible original history)
    (stage : ℕ) (s : State) :
    ∀ᵐ path ∂lawMeasure (tapedTrajectory π n stage s (window original (rowCount history) n)),
      ∀ row (hn : 0 < rowCount (history ++ transitionTrace n path) row),
        observedEmpirical s (history ++ transitionTrace n path) row =
          RowTapes.empirical hn (fun i : Fin (rowCount (history ++ transitionTrace n path) row) => original row i.val) := by
  filter_upwards [tapedTrajectory_ae_prefixCompatible π original n history hcompat stage s]
    with path hp row hn
  exact observedEmpirical_eq_tape s original _ hp row hn

end MarkovEpisodes

end
end Paper36.AdaptiveTapes
