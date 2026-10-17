import Paper36.SourceProtocol
import Paper36.SourceNativeConditional

/-! Field assembly on the single concrete source experiment. All raw-tape,
count and empirical-prefix fields are proved from generation and replay. The
conditional physical law is proved by the actual block-kernel induction. The
final constructor has only the source's exact Bayes identity as an input. -/
namespace Paper36.SourceSystem
noncomputable section
open scoped ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
  Paper36.SourceProtocol Paper36.StatisticalCounts

universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code]

abbrev Info (M Code : Type*) (S A : Type u) (T : ℕ) :=
  (M × History (M × Code) S A T) × (M × Code)

variable (T : ℕ) (s₀ : S)

def analystInfo (k : ℕ) (ω : Sample M (M × Code) S A T) : Info M Code S A T :=
  ((ω.1.1, SourceProtocol.history s₀ T k ω),(ω.2 k).1)

lemma measurable_analystInfo (k : ℕ) : Measurable (analystInfo (S := S) (A := A) (M := M) (Code := Code) T s₀ k) :=
  (measurable_fst.fst.prodMk (SourceProtocol.measurable_history s₀ T k)).prodMk
    ((measurable_pi_apply k).comp measurable_snd).fst

def policy (π : Code → Policy S A) (_k : ℕ) (i : Info M Code S A T) : Policy S A := π i.2.2

def transition (P : M → S × A → Law S) (_k : ℕ) (i : Info M Code S A T) : Simulation.Kernel S A :=
  fun s a => P i.1.1 (s,a)

lemma policy_meas (π : Code → Policy S A)
    (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a)) (k h : ℕ) (s : S) (a : A) :
    Measurable (fun i : Info M Code S A T => (policy T π k i h s).mass a) :=
  (hπ h s a).comp measurable_snd.snd

lemma transition_meas (P : M → S × A → Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) (k : ℕ) (s : S) (a : A) (t : S) :
    Measurable (fun i : Info M Code S A T => (transition T P k i s a).mass t) :=
  (hP (s,a) t).comp measurable_fst.fst

variable (ν : Measure M) [IsProbabilityMeasure ν]
  (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
  (π : Code → Policy S A) (hπ : ∀ h s a, Measurable (fun c => (π c h s).mass a))
  (planner : ProbabilityTheory.Kernel (History (M × Code) S A T) (M × Code)) [IsMarkovKernel planner]
  (dummy : Draw (M × Code) A T)

abbrev μ := SourceProtocol.measure ν P hP (fun m : M × Code => π m.2)
  (fun h s a => (hπ h s a).comp measurable_snd) planner s₀ dummy

/-- The precise remaining physical-law statement. It is stated for the concrete
constructed source measure, rather than added as a field of another realization. -/
def PhysicalLaw : Prop := ∀ k,
  condDistrib (SourceProtocol.path (M := M) (Meta := M × Code) s₀ T k)
    (analystInfo T s₀ k) (μ T s₀ ν P hP π hπ planner dummy) =ᵐ[
      (μ T s₀ ν P hP π hπ planner dummy).map (analystInfo T s₀ k)]
    trajectoryKernel (policy T π k) (transition T P k)
      (policy_meas T π hπ k) (transition_meas T P hP k) T s₀

/-- Once the concrete physical-law lemma is proved, the episode record has no
count, occupancy, unused-iid or empirical-prefix obligations left to assume. -/
def episodeSystemOfLaw
    (hphysical : PhysicalLaw T s₀ ν P hP π hπ planner dummy) :
    EpisodeSystem (μ T s₀ ν P hP π hπ planner dummy) (Info M Code S A T) S A T s₀ where
  policy := policy T π
  transition := transition T P
  latent ω s a := P ω.1.1 (s,a)
  info := analystInfo T s₀
  path := SourceProtocol.path s₀ T
  policy_meas := policy_meas T π hπ
  transition_meas := transition_meas T P hP
  info_meas := measurable_analystInfo T s₀
  path_meas k := (SourceProtocol.measurable_path s₀ T k).aemeasurable
  model := hphysical
  transition_match := fun _ _ => rfl
  count _ i row := historyCount i.1.2 row
  count_meas _ row := (measurable_historyCount row).comp measurable_fst.snd
  count_prefix k ω row := actual_count_prefix s₀ T k ω row

/-- The exact Bayes sampling identity is a primitive of the posterior sampler.
All coupling and physical observation fields below are independently derived. -/
def BayesLaw : Prop := ∀ k,
  condDistrib (fun ω : Sample M (M × Code) S A T => ω.1.1)
    (SourceProtocol.history s₀ T k) (μ T s₀ ν P hP π hπ planner dummy) =ᵐ[
      (μ T s₀ ν P hP π hπ planner dummy).map (SourceProtocol.history s₀ T k)]
    condDistrib (fun ω : Sample M (M × Code) S A T => (ω.2 k).1.1)
      (SourceProtocol.history s₀ T k) (μ T s₀ ν P hP π hπ planner dummy)

/-- Raw fields are assembled from the actual canonical source. In particular,
`tape_model` and `observed_prefix` are conclusions of construction and replay. -/
def posteriorSystemOfLaw
    (hphysical : PhysicalLaw T s₀ ν P hP π hπ planner dummy)
    (hBayes : BayesLaw T s₀ ν P hP π hπ planner dummy) :
    Statistical.PosteriorSystem (Model := M) (Hist := History (M × Code) S A T)
      (episodeSystemOfLaw T s₀ ν P hP π hπ planner dummy hphysical) where
  decode m s a := P m (s,a)
  decode_meas s a t := hP (s,a) t
  latent := fun ω => ω.1.1
  latent_meas := measurable_fst.fst
  latent_match := fun _ => rfl
  sampled k ω := (ω.2 k).1.1
  sampled_meas k := ((measurable_pi_apply k).comp measurable_snd).fst.fst
  history := SourceProtocol.history s₀ T
  history_meas := SourceProtocol.measurable_history s₀ T
  posterior := hBayes
  count := historyCount
  count_meas := measurable_historyCount
  count_match := fun _ _ _ => rfl
  observed := historyObserved s₀
  observed_meas := measurable_historyObserved_mass s₀
  tape ω row n := ω.1.2 (row,n)
  tape_meas row n := (measurable_pi_apply (row,n)).comp measurable_fst.snd
  tape_model row n := by
    have ht := actual_tape_model ν P hP (fun m : M × Code => π m.2)
      (fun h s a => (hπ h s a).comp measurable_snd) planner s₀ dummy row n
    simpa only [μ, SourceProtocol.measure, SourceExperiment.source_latent_law] using ht
  observed_prefix k ω row hn := actual_observed_prefix s₀ T k ω row hn


/-- The conditional physical Markov law of this concrete source is a theorem.
It is obtained from the original prior, actual planner and actual raw-tape
execution, without a fresh-unused or physical-law input. -/
theorem physicalLaw : PhysicalLaw T s₀ ν P hP π hπ planner dummy := by
  intro k
  simpa only [μ, analystInfo, policy, transition,
    SourceNativeConditional.actualInfo, SourceNativeConditional.trueInfoTrajectory] using
    SourceNativeConditional.actual_physicalLaw ν P hP (fun m : M × Code => π m.2)
      (fun h s a => (hπ h s a).comp measurable_snd) planner s₀ dummy k

/-- The actual episode system on the one canonical source probability space. -/
def episodeSystem :
    EpisodeSystem (μ T s₀ ν P hP π hπ planner dummy) (Info M Code S A T) S A T s₀ :=
  episodeSystemOfLaw T s₀ ν P hP π hπ planner dummy
    (physicalLaw T s₀ ν P hP π hπ planner dummy)

/-- The original posterior-sampling source, realized on one shared probability
space with its original infinite tapes and all actual trajectories. Every
coupling, fresh-window, dynamics, count and empirical-prefix field is derived.
The only law input is the source's exact conditional posterior identity. -/
def toPosteriorSystem (hBayes : BayesLaw T s₀ ν P hP π hπ planner dummy) :
    Statistical.PosteriorSystem (Model := M) (Hist := History (M × Code) S A T)
      (episodeSystem T s₀ ν P hP π hπ planner dummy) :=
  posteriorSystemOfLaw T s₀ ν P hP π hπ planner dummy
    (physicalLaw T s₀ ν P hP π hπ planner dummy) hBayes

/-- The construction preserves the arbitrary original prior exactly. -/
theorem prior_law :
    (μ T s₀ ν P hP π hπ planner dummy).map
      (fun ω : Sample M (M × Code) S A T => ω.1.1) = ν :=
  SourceExperiment.source_latent_law ν P hP
    (SourceProtocol.protocolKernel (fun m : M × Code => π m.2)
      (fun h s a => (hπ h s a).comp measurable_snd) planner s₀) dummy

/-- A Prop-valued source-realization theorem for the final contract. The same
sample contains the original latent model, original tapes and actual replayed
paths. Neither fresh-unused nor physical dynamics is an extra premise. -/
theorem exists_posteriorSystem (hBayes : BayesLaw T s₀ ν P hP π hπ planner dummy) :
    ∃ Q : Statistical.PosteriorSystem (Model := M) (Hist := History (M × Code) S A T)
        (episodeSystem T s₀ ν P hP π hπ planner dummy),
      Q.latent = (fun ω => ω.1.1) ∧
      Q.tape = (fun ω row n => ω.1.2 (row,n)) ∧
      (∀ k ω, (episodeSystem T s₀ ν P hP π hπ planner dummy).path k ω =
        SourceProtocol.path s₀ T k ω) ∧
      (μ T s₀ ν P hP π hπ planner dummy).map Q.latent = ν := by
  refine ⟨toPosteriorSystem T s₀ ν P hP π hπ planner dummy hBayes, rfl, rfl, ?_, ?_⟩
  · intro k ω
    rfl
  · exact prior_law T s₀ ν P hP π hπ planner dummy

end
end Paper36.SourceSystem
