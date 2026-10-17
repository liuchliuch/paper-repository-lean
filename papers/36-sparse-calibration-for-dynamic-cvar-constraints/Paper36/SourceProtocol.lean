import Paper36.SourceExperiment
import Paper36.SourceReplay
import Paper36.SourceBlocks
import Paper36.Statistical

/-! The original posterior/planner protocol is executed on one retained raw
infinite row tape. Only the private metadata and action draws are random output
coordinates. Every physical path and every empirical count is deterministic
replay of those outputs on that same original tape. -/
namespace Paper36.SourceProtocol
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay

universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {Meta M : Type*} [MeasurableSpace Meta] [MeasurableSpace M]

/-- The physical policy's action vector is sampled by running that policy on
the actual, already allocated raw stack. -/
def actionLaw (π : Policy S A) (T : ℕ) (s₀ : S) (tape : Stack (S × A) S T) :
    Law (Fin T → A) :=
  SourceBlocks.pushLaw (tapedTrajectory π T 0 s₀ tape) (actionsOfPath T)

lemma measurable_actionLaw_mass (π : Meta → Policy S A)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (T : ℕ) (s₀ : S) (actions : Fin T → A) :
    Measurable (fun z : Meta × Stack (S × A) S T => (actionLaw (π z.1) T s₀ z.2).mass actions) := by
  change Measurable (fun z : Meta × Stack (S × A) S T =>
    ∑ path : Trajectory S A T, (tapedTrajectory (π z.1) T 0 s₀ z.2).mass path *
      (dirac (actionsOfPath T path)).mass actions)
  apply Finset.measurable_sum
  intro path _
  apply Measurable.mul_const
  exact measurable_from_prod_countable_left fun tape =>
    measurable_tapedTrajectory_mass π hπ T 0 s₀ tape path

/-- A genuine finite action kernel, including all policy randomization. -/
def actionKernel (π : Meta → Policy S A)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a)) (T : ℕ) (s₀ : S) :
    ProbabilityTheory.Kernel (Meta × Stack (S × A) S T) (Fin T → A) :=
  lawKernel (fun z => actionLaw (π z.1) T s₀ z.2) (measurable_actionLaw_mass π hπ T s₀)

instance actionKernel_markov (π : Meta → Policy S A)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a)) (T : ℕ) (s₀ : S) :
    IsMarkovKernel (actionKernel π hπ T s₀) := lawKernel_markov _ _

abbrev Base (M S A : Type u) := M × ((S × A) × ℕ → S)

/-- The observed history is computed before sampling the next model or policy. -/
def past (T n : ℕ) (s₀ : S)
    (x : (M × ((S × A) × ℕ → S)) × (Fin n → Draw Meta A T)) : History Meta S A T :=
  finiteHistory (fun row j => x.1.2 (row,j)) s₀ x.2

lemma measurable_past (T n : ℕ) (s₀ : S) :
    Measurable (past (S := S) (A := A) (Meta := Meta) (M := M) T n s₀) :=
  measurable_finiteHistory _ s₀ _ (measurable_curry_raw.comp measurable_fst.snd) measurable_snd

/-- The next physical block starts at the actual count of its own observed history. -/
def nextWindow (T n : ℕ) (s₀ : S)
    (x : (M × ((S × A) × ℕ → S)) × (Fin n → Draw Meta A T)) : Stack (S × A) S T :=
  window (fun row j => x.1.2 (row,j)) (historyCount (past T n s₀ x)) T

lemma measurable_nextWindow (T n : ℕ) (s₀ : S) :
    Measurable (nextWindow (S := S) (A := A) (Meta := Meta) (M := M) T n s₀) := by
  apply measurable_pi_lambda
  intro c
  have hc : Measurable (fun x : (M × ((S × A) × ℕ → S)) × (Fin n → Draw Meta A T) =>
      historyCount (past T n s₀ x) c.1 + c.2.val) :=
    ((measurable_historyCount c.1).comp (measurable_past T n s₀)).add_const _
  exact measurable_eval_countable.comp (measurable_fst.snd.prodMk (measurable_const.prodMk hc))

/-- This is the concrete original source protocol. It first samples the
posterior model/planner metadata using only observed history, then samples the
physical actions on the original row tape. There is no unused-stack hypothesis. -/
def protocolKernel (π : Meta → Policy S A)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) (s₀ : S) (n : ℕ) :
    ProbabilityTheory.Kernel ((M × ((S × A) × ℕ → S)) × (Fin n → Draw Meta A T)) (Draw Meta A T) :=
  planner.comap (past T n s₀) (measurable_past T n s₀) ⊗ₖ
    (actionKernel π hπ T s₀).comap
      (fun z => (z.2,nextWindow T n s₀ z.1))
      (measurable_snd.prodMk ((measurable_nextWindow T n s₀).comp measurable_fst))

instance protocolKernel_markov (π : Meta → Policy S A)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (n : ℕ) : IsMarkovKernel (protocolKernel (M := M) π hπ planner s₀ n) := by
  unfold protocolKernel
  infer_instance

/-- One canonical experiment for the arbitrary-prior posterior/planner source. -/
def measure (ν : Measure M) (P : M → S × A → Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) :
    Measure ((M × ((S × A) × ℕ → S)) × (ℕ → Draw Meta A T)) :=
  SourceExperiment.source ν P hP (protocolKernel π hπ planner s₀) dummy

instance measure_probability [Nonempty S] (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) : IsProbabilityMeasure (measure ν P hP π hπ planner s₀ dummy) := by
  unfold measure
  infer_instance

abbrev Sample (M Meta S A : Type*) (T : ℕ) :=
  (M × ((S × A) × ℕ → S)) × (ℕ → Meta × (Fin T → A))

/-- Actual physical observations, for every sample point, including null ones. -/
def path (s₀ : S) (T k : ℕ) (ω : Sample M Meta S A T) : Trajectory S A T :=
  episodePath (fun row j => ω.1.2 (row,j)) s₀ ω.2 k

def history (s₀ : S) (T k : ℕ) (ω : Sample M Meta S A T) : History Meta S A T :=
  replayHistory (fun row j => ω.1.2 (row,j)) s₀ ω.2 k

lemma measurable_history (s₀ : S) (T k : ℕ) :
    Measurable (history (S := S) (A := A) (Meta := Meta) (M := M) s₀ T k) :=
  measurable_replayHistory _ s₀ _ (measurable_curry_raw.comp measurable_fst.snd) measurable_snd k

lemma measurable_path (s₀ : S) (T k : ℕ) :
    Measurable (path (S := S) (A := A) (Meta := Meta) (M := M) s₀ T k) :=
  measurable_episodePath _ s₀ _ (measurable_curry_raw.comp measurable_fst.snd) measurable_snd k

/-- Both frozen counts and physical paths belong to the same actual execution. -/
theorem actual_count_prefix (s₀ : S) (T k : ℕ) (ω : Sample M Meta S A T) (row : S × A) :
    historyCount (history s₀ T k ω) row =
      Counts.before (fun j => visitCount row T (path s₀ T j ω)) k :=
  replayHistory_count_prefix _ s₀ _ k row

/-- Observed empirical rows are exactly the prefixes of the retained original
raw tapes, on every sample point. -/
theorem actual_observed_prefix (s₀ : S) (T k : ℕ) (ω : Sample M Meta S A T) (row : S × A)
    (hn : 0 < historyCount (history s₀ T k ω) row) :
    historyObserved s₀ (history s₀ T k ω) row =
      RowTapes.empirical hn (fun i => ω.1.2 (row,i.val)) :=
  replayHistory_observed_prefix _ s₀ _ k row hn

/-- The raw tape conditional-iid fields are theorems of this concrete planner
and physical execution, not independent realization assumptions. -/
theorem actual_tape_model [Nonempty S] (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (row : S × A) (n : ℕ) :
    condDistrib (fun ω : Sample M Meta S A T => fun i : Fin n => ω.1.2 (row,i.val))
      (fun ω => ω.1.1) (measure ν P hP π hπ planner s₀ dummy) =ᵐ[ν]
      RowTapes.iidKernel (fun m => P m row) (hP row) n :=
  SourceExperiment.source_tape_model ν P hP (protocolKernel π hπ planner s₀) dummy row n

end
end Paper36.SourceProtocol
