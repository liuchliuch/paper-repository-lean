import Paper36.AdaptiveTapes

/-! Deterministic replay of the actual physical episodes on one persistent
raw tape. Every draw stores arbitrary learner metadata and T action choices.
The trajectory, visit counts and observed data are functions of the same draw
sequence and the same tape, including on probability-zero sample points. -/
namespace Paper36.SourceReplay
open MeasureTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes
open scoped BigOperators
noncomputable section
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

abbrev RawTape (S A : Type u) := (S × A) → ℕ → S
abbrev Draw (Meta : Type*) (A : Type u) (T : ℕ) := Meta × (Fin T → A)

/-- Each successor uses exactly the next still-unconsumed entry of its visited row. -/
def replayStep (raw : RawTape S A) (counts : S × A → ℕ) :
    (n : ℕ) → S → (Fin n → A) → Trajectory S A n
  | 0, s, _ => s
  | n+1, s, actions =>
      let a := actions 0
      let row := (s,a)
      (s,a,replayStep raw (increment counts row) n (raw row (counts row)) (fun i => actions i.succ))

@[simp] lemma replayStep_initial (raw : RawTape S A) (counts : S × A → ℕ)
    (n : ℕ) (s : S) (actions : Fin n → A) :
    initialState n (replayStep raw counts n s actions) = s := by
  cases n <;> rfl

/-- The action coordinate stored by a physical trajectory, in source stage order. -/
def actionsOfPath : (n : ℕ) → Trajectory S A n → Fin n → A
  | 0, _ => Fin.elim0
  | n+1, path => Fin.cases path.2.1 (actionsOfPath n path.2.2)

@[simp] lemma actionsOfPath_replayStep (raw : RawTape S A) (counts : S × A → ℕ)
    (n : ℕ) (s : S) (actions : Fin n → A) :
    actionsOfPath n (replayStep raw counts n s actions) = actions := by
  induction n generalizing counts s with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [actionsOfPath, replayStep, Fin.cases_succ]
      exact congrFun (ih _ _ _) j

/-- Actual replay preserves the original iid tape prefix on every sample point. -/
theorem replayStep_prefixCompatible (raw : RawTape S A) (n : ℕ)
    (history : List ((S × A) × S)) (hcompat : PrefixCompatible raw history)
    (s : S) (actions : Fin n → A) :
    PrefixCompatible raw (history ++ transitionTrace n (replayStep raw (rowCount history) n s actions)) := by
  induction n generalizing history s with
  | zero => simpa only [transitionTrace, List.append_nil] using hcompat
  | succ n ih =>
    let row := (s,actions 0)
    let y := raw row (rowCount history row)
    let history' := history ++ [(row,y)]
    have hc' : PrefixCompatible raw history' := prefixCompatible_append raw history hcompat row
    have hcount : increment (rowCount history) row = rowCount history' := by
      funext q
      rw [show history' = history ++ [(row,y)] from rfl, rowCount_append]
      rfl
    have hrec := ih history' hc' y (fun i => actions i.succ)
    simp only [replayStep, transitionTrace, replayStep_initial]
    change PrefixCompatible raw (history ++ (row,y)::transitionTrace n
      (replayStep raw (increment (rowCount history) row) n y (fun i => actions i.succ)))
    rw [hcount]
    simpa only [history', List.append_assoc, List.singleton_append] using hrec

/-- A supported taped trajectory is exactly the deterministic replay of its actions. -/
theorem replayStep_of_positive_tapedTrajectory
    (π : Simulation.Policy S A) (raw : RawTape S A) (counts : S × A → ℕ)
    (n h : ℕ) (s : S) (path : Trajectory S A n)
    (hp : 0 < (tapedTrajectory π n h s (window raw counts n)).mass path) :
    replayStep raw counts n s (actionsOfPath n path) = path := by
  induction n generalizing counts h s with
  | zero =>
    exact (tapedTrajectory_initial π 0 h s _ path hp).symm
  | succ n ih =>
    rcases path with ⟨u,a,rest⟩
    have hu : u = s := tapedTrajectory_initial π (n+1) h s _ (u,a,rest) hp
    subst u
    have hsub : 0 < (tapedTrajectory π n (h+1)
        (head (s,a) (window raw counts (n+1)))
        (remaining (s,a) (window raw counts (n+1)))).mass rest := by
      by_contra hn
      have hz := le_antisymm (le_of_not_gt hn)
        ((tapedTrajectory π n (h+1) (head (s,a) (window raw counts (n+1)))
          (remaining (s,a) (window raw counts (n+1)))).nonneg rest)
      have hz' : (tapedTrajectory π (n+1) h s (window raw counts (n+1))).mass (s,a,rest) = 0 := by
        simp only [tapedTrajectory, joint]
        change (Simulation.dirac s).mass s * ((π h s).mass a * _) = 0
        rw [hz, mul_zero, mul_zero]
      linarith
    rw [head_window, remaining_window] at hsub
    have hrec := ih (increment counts (s,a)) (h+1) (raw (s,a) (counts (s,a))) rest hsub
    simp only [replayStep, actionsOfPath, Fin.cases_zero, Fin.cases_succ]
    rw [hrec]

variable {Meta : Type*}

/-- All actually observed transition records before episode k. -/
def episodeReplay (raw : RawTape S A) (s₀ : S) {T : ℕ} (draws : ℕ → Draw Meta A T) :
    ℕ → List ((S × A) × S)
  | 0 => []
  | k+1 =>
      let history := episodeReplay raw s₀ draws k
      history ++ transitionTrace T (replayStep raw (rowCount history) T s₀ (draws k).2)

/-- The real episode path, including its final observed successor. -/
def episodePath (raw : RawTape S A) (s₀ : S) {T : ℕ} (draws : ℕ → Draw Meta A T)
    (k : ℕ) : Trajectory S A T :=
  replayStep raw (rowCount (episodeReplay raw s₀ draws k)) T s₀ (draws k).2

@[simp] lemma episodeReplay_succ (raw : RawTape S A) (s₀ : S) {T : ℕ}
    (draws : ℕ → Draw Meta A T) (k : ℕ) :
    episodeReplay raw s₀ draws (k+1) =
      episodeReplay raw s₀ draws k ++ transitionTrace T (episodePath raw s₀ draws k) := rfl

theorem episodeReplay_eq_episodeHistory (raw : RawTape S A) (s₀ : S) {T : ℕ}
    (draws : ℕ → Draw Meta A T) (k : ℕ) :
    episodeReplay raw s₀ draws k = episodeHistory T (episodePath raw s₀ draws) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [episodeReplay_succ, episodeHistory, ih]

/-- The actual starting count is the sum of the actual preceding episode visits. -/
theorem count_prefix (raw : RawTape S A) (s₀ : S) {T : ℕ}
    (draws : ℕ → Draw Meta A T) (k : ℕ) (row : S × A) :
    rowCount (episodeReplay raw s₀ draws k) row =
      Counts.before (fun j => visitCount row T (episodePath raw s₀ draws j)) k := by
  rw [episodeReplay_eq_episodeHistory]
  exact episodeHistory_count_prefix T _ k row

/-- Prefix compatibility holds for every tape and every learner draw sequence. -/
theorem episodeReplay_prefixCompatible (raw : RawTape S A) (s₀ : S) {T : ℕ}
    (draws : ℕ → Draw Meta A T) (k : ℕ) :
    PrefixCompatible raw (episodeReplay raw s₀ draws k) := by
  induction k with
  | zero => intro row; simp [episodeReplay, rowCount, rowObservations]
  | succ k ih => exact replayStep_prefixCompatible raw T _ ih s₀ (draws k).2

theorem observedEmpirical_eq_tape
    (raw : RawTape S A) (s₀ : S) {T : ℕ} (draws : ℕ → Draw Meta A T)
    (k : ℕ) (row : S × A) (hn : 0 < rowCount (episodeReplay raw s₀ draws k) row) :
    AdaptiveTapes.observedEmpirical s₀ (episodeReplay raw s₀ draws k) row =
      RowTapes.empirical hn (fun i : Fin (rowCount (episodeReplay raw s₀ draws k) row) => raw row i.val) :=
  AdaptiveTapes.observedEmpirical_eq_tape s₀ raw _ (episodeReplay_prefixCompatible raw s₀ draws k) row hn

/-- Finite physical history uses only the finite vector of already realized paths. -/
def finiteTrace {T k : ℕ} (paths : Fin k → Trajectory S A T) : List ((S × A) × S) :=
  (List.ofFn paths).flatMap (transitionTrace T)

@[simp] lemma finiteTrace_succ {T k : ℕ} (paths : Fin (k+1) → Trajectory S A T) :
    finiteTrace paths = finiteTrace (fun i : Fin k => paths i.castSucc) ++ transitionTrace T (paths (Fin.last k)) := by
  simp only [finiteTrace, List.ofFn_succ', List.concat_eq_append, List.flatMap_append, List.flatMap_singleton]

/-- Replay of a finite draw prefix, without choosing any infinite extension. -/
def finitePaths (raw : RawTape S A) (s₀ : S) {T : ℕ} :
    (k : ℕ) → (Fin k → Draw Meta A T) → Fin k → Trajectory S A T
  | 0, _ => Fin.elim0
  | k+1, draws =>
      let previous := finitePaths raw s₀ k (fun i => draws i.castSucc)
      Fin.lastCases (replayStep raw (rowCount (finiteTrace previous)) T s₀ (draws (Fin.last k)).2) previous

theorem episodeReplay_eq_finiteTrace (raw : RawTape S A) (s₀ : S) {T : ℕ}
    (draws : ℕ → Draw Meta A T) (k : ℕ) :
    episodeReplay raw s₀ draws k = finiteTrace (fun i : Fin k => episodePath raw s₀ draws i.val) := by
  induction k with
  | zero => simp [episodeReplay, finiteTrace]
  | succ k ih => rw [episodeReplay_succ, finiteTrace_succ, ih]; rfl

/-- A finite draw prefix and any infinite continuation generate exactly the same past paths. -/
theorem finitePaths_eq_episodePath (raw : RawTape S A) (s₀ : S) {T : ℕ}
    (draws : ℕ → Draw Meta A T) (k : ℕ) :
    finitePaths raw s₀ k (fun i => draws i.val) = fun i => episodePath raw s₀ draws i.val := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [finitePaths, Fin.lastCases_last, Fin.val_last]
      change replayStep raw (rowCount (finiteTrace (finitePaths raw s₀ k (fun i => draws i.val)))) T s₀
        (draws k).2 = _
      rw [ih, ← episodeReplay_eq_finiteTrace]
      rfl
    · simp only [finitePaths, Fin.lastCases_castSucc, Fin.coe_castSucc]
      exact congrFun ih j

/-- A history retains arbitrary learner metadata and the actual physical paths. -/
abbrev History (Meta : Type*) (S A : Type u) (T : ℕ) :=
  Σ k : ℕ, (Fin k → Meta) × (Fin k → Trajectory S A T)

def finiteHistory (raw : RawTape S A) (s₀ : S) {T k : ℕ} (draws : Fin k → Draw Meta A T) :
    History Meta S A T := ⟨k, (fun i => (draws i).1), finitePaths raw s₀ k draws⟩

def replayHistory (raw : RawTape S A) (s₀ : S) {T : ℕ} (draws : ℕ → Draw Meta A T) (k : ℕ) :
    History Meta S A T := finiteHistory raw s₀ (fun i : Fin k => draws i.val)

@[simp] theorem replayHistory_paths (raw : RawTape S A) (s₀ : S) {T : ℕ}
    (draws : ℕ → Draw Meta A T) (k : ℕ) :
    (replayHistory raw s₀ draws k).2.2 = fun i => episodePath raw s₀ draws i.val :=
  finitePaths_eq_episodePath raw s₀ draws k

def historyTrace {T : ℕ} (history : History Meta S A T) : List ((S × A) × S) :=
  finiteTrace history.2.2

@[simp] theorem replayHistory_trace (raw : RawTape S A) (s₀ : S) {T : ℕ}
    (draws : ℕ → Draw Meta A T) (k : ℕ) :
    historyTrace (replayHistory raw s₀ draws k) = episodeReplay raw s₀ draws k := by
  change finiteTrace (finitePaths raw s₀ k (fun i => draws i.val)) = _
  rw [finitePaths_eq_episodePath, ← episodeReplay_eq_finiteTrace]

def historyCount {T : ℕ} (history : History Meta S A T) : S × A → ℕ :=
  rowCount (historyTrace history)

def historyObserved {T : ℕ} (fallback : S) (history : History Meta S A T) (row : S × A) : Law S :=
  AdaptiveTapes.observedEmpirical fallback (historyTrace history) row

@[simp] theorem replayHistory_count_prefix (raw : RawTape S A) (s₀ : S) {T : ℕ}
    (draws : ℕ → Draw Meta A T) (k : ℕ) (row : S × A) :
    historyCount (replayHistory raw s₀ draws k) row =
      Counts.before (fun j => visitCount row T (episodePath raw s₀ draws j)) k := by
  rw [historyCount, replayHistory_trace, count_prefix]

theorem replayHistory_observed_prefix (raw : RawTape S A) (s₀ : S) {T : ℕ}
    (draws : ℕ → Draw Meta A T) (k : ℕ) (row : S × A)
    (hn : 0 < historyCount (replayHistory raw s₀ draws k) row) :
    historyObserved s₀ (replayHistory raw s₀ draws k) row =
      RowTapes.empirical hn (fun i => raw row i.val) := by
  unfold historyObserved
  have hh : historyTrace (replayHistory raw s₀ draws k) = episodeReplay raw s₀ draws k := replayHistory_trace raw s₀ draws k
  apply AdaptiveTapes.observedEmpirical_eq_tape
  rw [hh]
  exact episodeReplay_prefixCompatible raw s₀ draws k

/-- Every finite realized draw prefix has a pointwise compatible observed history. -/
theorem finitePaths_prefixCompatible (raw : RawTape S A) (s₀ : S) {T : ℕ}
    (k : ℕ) (draws : Fin k → Draw Meta A T) :
    PrefixCompatible raw (finiteTrace (finitePaths raw s₀ k draws)) := by
  induction k with
  | zero => intro row; simp [finiteTrace, rowCount, rowObservations]
  | succ k ih =>
    rw [finiteTrace_succ]
    simp only [finitePaths, Fin.lastCases_castSucc, Fin.lastCases_last]
    exact replayStep_prefixCompatible raw T _ (ih _) s₀ (draws (Fin.last k)).2

theorem finiteHistory_observed_prefix (raw : RawTape S A) (s₀ : S) {T k : ℕ}
    (draws : Fin k → Draw Meta A T) (row : S × A)
    (hn : 0 < historyCount (finiteHistory raw s₀ draws) row) :
    historyObserved s₀ (finiteHistory raw s₀ draws) row =
      RowTapes.empirical hn (fun i => raw row i.val) :=
  AdaptiveTapes.observedEmpirical_eq_tape s₀ raw _ (finitePaths_prefixCompatible raw s₀ k draws) row hn

instance instMeasurableSpaceTrace : MeasurableSpace (List ((S × A) × S)) := ⊤
instance instDiscreteMeasurableSpaceTrace : DiscreteMeasurableSpace (List ((S × A) × S)) :=
  ⟨fun _ => trivial⟩

section Measurability
variable [MeasurableSpace A] [DiscreteMeasurableSpace A] [MeasurableSpace Meta]
  {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_eval_countable {I X : Type*} [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] [MeasurableSpace X] :
    Measurable (fun z : (I → X) × I => z.1 z.2) :=
  measurable_from_prod_countable_left fun i => measurable_pi_apply i

/-- Dynamic row and dynamic index reads are measurable on the raw infinite product. -/
lemma measurable_read (raw : Ω → RawTape S A) (counts : Ω → S × A → ℕ)
    (row : Ω → S × A) (hraw : Measurable raw) (hcounts : Measurable counts) (hrow : Measurable row) :
    Measurable (fun ω => raw ω (row ω) (counts ω (row ω))) := by
  have hr := measurable_eval_countable.comp (hraw.prodMk hrow)
  have hc := measurable_eval_countable.comp (hcounts.prodMk hrow)
  exact measurable_eval_countable.comp (hr.prodMk hc)

lemma measurable_increment (counts : Ω → S × A → ℕ) (row : Ω → S × A)
    (hcounts : Measurable counts) (hrow : Measurable row) :
    Measurable (fun ω => increment (counts ω) (row ω)) := by
  apply measurable_pi_lambda
  intro q
  have heq : MeasurableSet {ω | q = row ω} := by
    simpa only [Set.preimage, Set.mem_singleton_iff, eq_comm] using hrow (measurableSet_singleton q)
  exact (hcounts.eval).add (Measurable.ite heq
    measurable_const measurable_const)

/-- Replay measurability follows the actual successive tape reads. -/
theorem measurable_replayStep (raw : Ω → RawTape S A) (hraw : Measurable raw)
    (n : ℕ) (counts : Ω → S × A → ℕ) (hcounts : Measurable counts)
    (s : Ω → S) (hs : Measurable s) (actions : Ω → Fin n → A) (ha : Measurable actions) :
    Measurable (fun ω => replayStep (raw ω) (counts ω) n (s ω) (actions ω)) := by
  induction n generalizing counts s with
  | zero =>
    have hid : @Measurable S (Trajectory S A 0) inferInstance (instMeasurableSpaceTrajectory 0)
        (fun x => x) := Measurable.of_discrete
    exact hid.comp hs
  | succ n ih =>
    let row : Ω → S × A := fun ω => (s ω, actions ω 0)
    have hr : Measurable row := hs.prodMk ha.eval
    have hc := measurable_increment counts row hcounts hr
    have hy := measurable_read raw counts row hraw hcounts hr
    have htail : Measurable (fun ω => fun i : Fin n => actions ω i.succ) :=
      measurable_pi_lambda _ fun i => ha.eval
    have ht := ih (fun ω => increment (counts ω) (row ω)) hc
      (fun ω => raw ω (row ω) (counts ω (row ω))) hy _ htail
    have hjoin : @Measurable (S × (A × Trajectory S A n)) (Trajectory S A (n+1))
        inferInstance (instMeasurableSpaceTrajectory (n+1)) (fun x => x) :=
      Measurable.of_discrete
    exact hjoin.comp (hs.prodMk ((ha.eval (a := 0)).prodMk ht))

lemma measurable_finiteTrace {T k : ℕ} :
    Measurable (finiteTrace (S := S) (A := A) (T := T) (k := k)) := Measurable.of_discrete

lemma measurable_rowCount (history : Ω → List ((S × A) × S)) (hh : Measurable history) :
    Measurable (fun ω => rowCount (history ω)) := by
  apply measurable_pi_lambda
  intro row
  exact (Measurable.of_discrete : Measurable (fun h : List ((S × A) × S) => rowCount h row)).comp hh

/-- Physical histories contain only actually replayed transitions, measurably. -/
theorem measurable_episodeReplay (raw : Ω → RawTape S A) (s₀ : S) {T : ℕ}
    (draws : Ω → ℕ → Draw Meta A T) (hraw : Measurable raw) (hd : Measurable draws) (k : ℕ) :
    Measurable (fun ω => episodeReplay (raw ω) s₀ (draws ω) k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hp := measurable_replayStep raw hraw T _ (measurable_rowCount _ ih)
      (fun _ => s₀) measurable_const (fun ω => (draws ω k).2) (hd.eval.snd)
    have happ : Measurable (fun z : List ((S × A) × S) × Trajectory S A T =>
        z.1 ++ transitionTrace T z.2) := Measurable.of_discrete
    exact happ.comp (ih.prodMk hp)

theorem measurable_episodePath (raw : Ω → RawTape S A) (s₀ : S) {T : ℕ}
    (draws : Ω → ℕ → Draw Meta A T) (hraw : Measurable raw) (hd : Measurable draws) (k : ℕ) :
    Measurable (fun ω => episodePath (raw ω) s₀ (draws ω) k) :=
  measurable_replayStep raw hraw T _ (measurable_rowCount _ (measurable_episodeReplay raw s₀ draws hraw hd k))
    (fun _ => s₀) measurable_const _ (hd.eval.snd)

/-- Finite prefix replay is measurable without inspecting any future draw. -/
theorem measurable_finitePaths (raw : Ω → RawTape S A) (s₀ : S) {T : ℕ}
    (hraw : Measurable raw) (k : ℕ) (draws : Ω → Fin k → Draw Meta A T) (hd : Measurable draws) :
    Measurable (fun ω => finitePaths (raw ω) s₀ k (draws ω)) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hprev : Measurable (fun ω => finitePaths (raw ω) s₀ k (fun i => draws ω i.castSucc)) :=
      ih _ (measurable_pi_lambda _ fun i => hd.eval)
    have hh := measurable_finiteTrace.comp hprev
    have hp := measurable_replayStep raw hraw T _ (measurable_rowCount _ hh)
      (fun _ => s₀) measurable_const (fun ω => (draws ω (Fin.last k)).2) hd.eval.snd
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [finitePaths, Fin.lastCases_last] using hp
    · simpa only [finitePaths, Fin.lastCases_castSucc] using hprev.eval (a := j)

lemma measurable_history_mk {T : ℕ} (k : ℕ) :
    Measurable (fun z : (Fin k → Meta) × (Fin k → Trajectory S A T) => (⟨k,z⟩ : History Meta S A T)) :=
  Measurable.of_le_map (iInf_le _ k)

lemma measurable_historyTrace {T : ℕ} :
    Measurable (historyTrace (Meta := Meta) (S := S) (A := A) (T := T)) := by
  intro B hB
  apply MeasurableSpace.measurableSet_iInf.2
  intro k
  exact (measurable_finiteTrace.comp measurable_snd) hB

lemma measurable_historyCount {T : ℕ} (row : S × A) :
    Measurable (fun history : History Meta S A T => historyCount history row) :=
  (Measurable.of_discrete : Measurable (fun h : List ((S × A) × S) => rowCount h row)).comp
    measurable_historyTrace

lemma measurable_historyObserved_mass {T : ℕ} (fallback : S) (row : S × A) (t : S) :
    Measurable (fun history : History Meta S A T => (historyObserved fallback history row).mass t) :=
  (Measurable.of_discrete : Measurable (fun h : List ((S × A) × S) =>
    (AdaptiveTapes.observedEmpirical fallback h row).mass t)).comp measurable_historyTrace

theorem measurable_finiteHistory (raw : Ω → RawTape S A) (s₀ : S) {T k : ℕ}
    (draws : Ω → Fin k → Draw Meta A T) (hraw : Measurable raw) (hd : Measurable draws) :
    Measurable (fun ω => finiteHistory (raw ω) s₀ (draws ω)) :=
  (measurable_history_mk k).comp ((measurable_pi_lambda _ fun i => hd.eval.fst).prodMk
    (measurable_finitePaths raw s₀ hraw k draws hd))

theorem measurable_replayHistory (raw : Ω → RawTape S A) (s₀ : S) {T : ℕ}
    (draws : Ω → ℕ → Draw Meta A T) (hraw : Measurable raw) (hd : Measurable draws) (k : ℕ) :
    Measurable (fun ω => replayHistory (raw ω) s₀ (draws ω) k) :=
  measurable_finiteHistory raw s₀ _ hraw (measurable_pi_lambda _ fun i => hd.eval)

/-- The constructor may keep the original uncurried row-by-index tape coordinates. -/
lemma measurable_curry_raw :
    Measurable (fun raw : (S × A) × ℕ → S => fun row n => raw (row,n)) := by
  apply measurable_pi_lambda
  intro row
  apply measurable_pi_lambda
  intro n
  exact measurable_pi_apply _

end Measurability

end
end Paper36.SourceReplay
