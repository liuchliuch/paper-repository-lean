import CalibrationDistance.Implementation

/-! Resumable initialization, not merely a progress counter.

A suspended job exposes finite construction steps. `advance` executes a bounded
number and returns the remaining job. The actual integer parameter search and
bulk tree builder are turned into such jobs below; completing the scheduled
budget returns the correct prepared tree, including all cached signs.
-/

namespace CalibrationDistance

inductive InitJob (α : Type*) where
  | done (value : α)
  | step (next : Unit → InitJob α)

namespace InitJob

def result {α} : InitJob α → α
  | .done a => a
  | .step next => result (next ())

def work {α} : InitJob α → ℕ
  | .done _ => 0
  | .step next => work (next ())+1

def bind {α β} : InitJob α → (α → InitJob β) → InitJob β
  | .done a, f => f a
  | .step next, f => .step (fun _ => bind (next ()) f)

@[simp] theorem result_bind {α β} (job : InitJob α) (f : α → InitJob β) :
    result (bind job f) = result (f (result job)) := by
  induction job with
  | done a => rfl
  | step next ih => exact ih ()

@[simp] theorem work_bind {α β} (job : InitJob α) (f : α → InitJob β) :
    work (bind job f) = work job + work (f (result job)) := by
  induction job with
  | done a => simp [bind,work,result]
  | step next ih => simpa [bind,work,result,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih ()

def advance {α} : ℕ → InitJob α → InitJob α
  | 0, job => job
  | _+1, .done a => .done a
  | n+1, .step next => advance n (next ())

theorem advance_complete {α} (n : ℕ) : ∀ job : InitJob α, work job ≤ n →
    advance n job = .done (result job) := by
  induction n with
  | zero =>
    intro job hj
    cases job with
    | done a => rfl
    | step next => simp [work] at hj
  | succ n ih =>
    intro job hj
    cases job with
    | done a => rfl
    | step next => exact ih (next ()) (by simpa only [work,Nat.add_le_add_iff_right] using hj)

@[simp] theorem advance_done {α} (n : ℕ) (a : α) : advance n (.done a) = .done a := by
  cases n <;> rfl

theorem advance_add {α} (m n : ℕ) (job : InitJob α) :
    advance (m+n) job = advance n (advance m job) := by
  induction m generalizing job with
  | zero => simp [advance]
  | succ m ih =>
    cases job with
    | done a => simp
    | step next => simpa [advance,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (next ())

end InitJob

namespace GridTree

def initializationJob {α} (test : α → Bool) : (d : ℕ) → (ℕ → α) → InitJob (Tree α d)
  | 0, f => .step (fun _ => .done (.leaf (f 0) (test (f 0))))
  | d+1, f => .step (fun _ => InitJob.bind (initializationJob test d f) (fun left =>
      InitJob.bind (initializationJob test d (fun i => f (2^d+i))) (fun right =>
        .done (branch left right))))

@[simp] theorem initializationJob_result {α} (test : α → Bool) (d : ℕ) (f : ℕ → α) :
    (initializationJob test d f).result = build test d f := by
  induction d generalizing f with
  | zero => rfl
  | succ d ih => simp [initializationJob,InitJob.result,ih,build]

@[simp] theorem initializationJob_work {α} (test : α → Bool) (d : ℕ) (f : ℕ → α) :
    (initializationJob test d f).work = nodes (build test d f) := by
  induction d generalizing f with
  | zero => rfl
  | succ d ih =>
    simp [initializationJob,InitJob.work,InitJob.result,ih,build,branch,nodes]
    omega

end GridTree

def parameterInitializationJob (T : ℕ) : ℕ → ℕ → InitJob ℕ
  | 0, n => .done n
  | fuel+1, n => .step (fun _ => if T ≤ n*(n+1) then .done n
      else parameterInitializationJob T fuel (n+1))

@[simp] theorem parameterInitializationJob_result (T fuel n : ℕ) :
    (parameterInitializationJob T fuel n).result = gridParameterSearch T fuel n := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    simp only [parameterInitializationJob,InitJob.result,gridParameterSearch]
    split_ifs <;> simp [InitJob.result,ih]

@[simp] theorem parameterInitializationJob_work (T fuel n : ℕ) :
    (parameterInitializationJob T fuel n).work = gridParameterSearchVisits T fuel n := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    simp only [parameterInitializationJob,InitJob.work,gridParameterSearchVisits]
    split_ifs <;> simp [InitJob.work,ih,Nat.add_comm]

def nextEpochInitializationJob (L : ℕ) : InitJob (Σ m, GridSearchTree m) :=
  InitJob.bind (parameterInitializationJob (2*L) L 1) (fun m =>
    InitJob.bind (GridTree.initializationJob (gridTreeFlag m) (gridTreeDepth m)
      (fun i => (i,(0:ℤ)))) (fun tree => .done ⟨m,tree⟩))

theorem nextEpochInitializationJob_result (L : ℕ) (hL : 1 ≤ L) :
    (nextEpochInitializationJob L).result =
      ⟨optimalGrid (2*L),gridTreeInitial (optimalGrid (2*L))⟩ := by
  have htree (m : ℕ) :
      (InitJob.bind (GridTree.initializationJob (gridTreeFlag m) (gridTreeDepth m)
        (fun i => (i,(0:ℤ)))) (fun tree => InitJob.done (Sigma.mk m tree : Σ m, GridSearchTree m))).result =
          (Sigma.mk m (gridTreeInitial m) : Σ m, GridSearchTree m) := by
    simp only [InitJob.result_bind,InitJob.result,GridTree.initializationJob_result]
    rfl
  rw [nextEpochInitializationJob,InitJob.result_bind,htree,parameterInitializationJob_result]
  exact congrArg (fun m => (Sigma.mk m (gridTreeInitial m) : Σ m, GridSearchTree m))
    (nextGridParameter_correct L hL)

theorem nextEpochInitializationJob_work (L : ℕ) (hL : 1 ≤ L) :
    (nextEpochInitializationJob L).work = nextInitializationWork L := by
  have htree (m : ℕ) :
      (InitJob.bind (GridTree.initializationJob (gridTreeFlag m) (gridTreeDepth m)
        (fun i => (i,(0:ℤ)))) (fun tree => InitJob.done (Sigma.mk m tree : Σ m, GridSearchTree m))).work =
          GridTree.nodes (gridTreeInitial m) := by
    simp only [InitJob.work_bind,InitJob.work,add_zero,GridTree.initializationJob_work]
    rfl
  rw [nextEpochInitializationJob,InitJob.work_bind,htree,
    parameterInitializationJob_work,parameterInitializationJob_result]
  change gridParameterSearchVisits (2*L) L 1 +
    GridTree.nodes (gridTreeInitial (nextGridParameter L)) = _
  rw [nextGridParameter_correct L hL]
  rfl

/-- Scheduled execution actually returns the required initial tree by the
boundary, rather than only advancing an unrelated numerical counter. -/
theorem prepared_tree_ready (L : ℕ) (hL : 1 ≤ L) :
    InitJob.advance (9*L) (nextEpochInitializationJob L) =
      .done ⟨optimalGrid (2*L),gridTreeInitial (optimalGrid (2*L))⟩ := by
  rw [← nextEpochInitializationJob_result L hL]
  apply InitJob.advance_complete
  rw [nextEpochInitializationJob_work L hL]
  exact nextInitializationWork_budget L hL

/-- Nine bounded construction quanta on each current round implement the
same execution as the completed budget at the boundary. -/
def runInitializationRounds (L : ℕ) : ℕ → InitJob (Σ m, GridSearchTree m)
  | 0 => nextEpochInitializationJob L
  | rounds+1 => InitJob.advance 9 (runInitializationRounds L rounds)

theorem runInitializationRounds_eq (L rounds : ℕ) :
    runInitializationRounds L rounds = InitJob.advance (9*rounds) (nextEpochInitializationJob L) := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
    rw [runInitializationRounds,ih,← InitJob.advance_add]
    congr 1

theorem next_epoch_ready (L : ℕ) (hL : 1 ≤ L) :
    runInitializationRounds L L =
      .done ⟨optimalGrid (2*L),gridTreeInitial (optimalGrid (2*L))⟩ := by
  rw [runInitializationRounds_eq]
  exact prepared_tree_ready L hL

end CalibrationDistance
