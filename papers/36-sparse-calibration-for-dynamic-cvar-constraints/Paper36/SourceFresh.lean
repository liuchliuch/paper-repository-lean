import Paper36.SourceSummary
import Paper36.SourceInduction
import Paper36.SourcePlanBlock
import Paper36.SourceStepReplay

/-! Fresh unused rows for every episode of the one original source experiment.
The invariant is derived from the original product tape law and the actual
finite-prefix recursion. In particular, freshness is not a source assumption. -/
namespace Paper36.SourceFresh
noncomputable section
open scoped ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
  Paper36.SourceProtocol Paper36.SourceSummary
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta]

def initial (T : ℕ) (m : M) : Ctx M Meta S A T 0 :=
  (m,(Fin.elim0,Fin.elim0))

lemma measurable_initial (T : ℕ) :
    Measurable (initial (M := M) (Meta := Meta) (S := S) (A := A) T) :=
  measurable_id.prodMk measurable_const

def prefixInput (T k : ℕ) (ω : Sample M Meta S A T) : Input M Meta S A T k :=
  (ω.1,fun i => ω.2 i.val)

lemma measurable_prefixInput (T k : ℕ) :
    Measurable (prefixInput (M := M) (Meta := Meta) (S := S) (A := A) T k) :=
  measurable_fst.prodMk (measurable_pi_lambda _ fun i => measurable_snd.eval)

def actualContext (T k : ℕ) (s₀ : S) (ω : Sample M Meta S A T) : Ctx M Meta S A T k :=
  context T k s₀ (prefixInput T k ω)

lemma measurable_actualContext (T k : ℕ) (s₀ : S) :
    Measurable (actualContext (M := M) (Meta := Meta) (A := A) T k s₀) :=
  (measurable_context T k s₀).comp (measurable_prefixInput T k)

def actualWindow (T k L : ℕ) (s₀ : S) (ω : Sample M Meta S A T) : Stack (S × A) S L :=
  (summary T k L s₀ (prefixInput T k ω)).2

lemma measurable_actualWindow (T k L : ℕ) (s₀ : S) :
    Measurable (actualWindow (M := M) (Meta := Meta) (A := A) T k L s₀) :=
  ((measurable_summary T k L s₀).comp (measurable_prefixInput T k)).snd

lemma summary_zero (T L : ℕ) (s₀ : S) (x : Input M Meta S A T 0) :
    summary T 0 L s₀ x = (initial T x.1.1,AdaptiveKernel.fullPrefix L x.1.2) := by
  apply Prod.ext
  · change context T 0 s₀ x = initial T x.1.1
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _
  · funext c
    simp [summary,past,finiteHistory,historyCount,historyTrace,finiteTrace,
      finitePaths,rowCount,rowObservations,window,AdaptiveKernel.fullPrefix]

/-- Initially every row window has its categorical product law conditional on
the arbitrary latent model, with the genuinely empty observed history. -/
theorem initial_tape_joint (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (T L : ℕ) :
    (InfiniteTapes.priorTapes ν P hP).map
      (fun x => (initial (Meta := Meta) T x.1,AdaptiveKernel.fullPrefix L x.2)) =
      ν.map (initial T) ⊗ₘ SourcePlanBlock.freshCtx P hP T 0 L := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  have hi := measurable_initial (M := M) (Meta := Meta) (S := S) (A := A) T
  have hp := AdaptiveKernel.measurable_fullPrefix (Row := S × A) (S := S) L
  have hm : Measurable (fun x : M × ((S × A) × ℕ → S) =>
      (initial (Meta := Meta) T x.1,AdaptiveKernel.fullPrefix L x.2)) :=
    (hi.comp measurable_fst).prodMk (hp.comp measurable_snd)
  have hint : Measurable (fun c : Ctx M Meta S A T 0 =>
      ∫⁻ r, f (c,r) ∂SourcePlanBlock.freshCtx P hP T 0 L c) :=
    hf.lintegral_kernel_prod_right'
  have hfun : Measurable (fun x : M × ((S × A) × ℕ → S) =>
      f (initial (Meta := Meta) T x.1,AdaptiveKernel.fullPrefix L x.2)) := hf.comp hm
  rw [lintegral_map hf hm,InfiniteTapes.priorTapes,
    Measure.lintegral_compProd hfun,Measure.lintegral_compProd hf,
    lintegral_map hint hi]
  apply lintegral_congr_ae
  apply ae_of_all
  intro m
  have hfm : Measurable (fun r => f (initial T m,r)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  change (∫⁻ raw, f (initial T m,AdaptiveKernel.fullPrefix L raw)
      ∂InfiniteTapes.infiniteLaw (fun c : (S × A) × ℕ => P m c.1)) =
    ∫⁻ r, f (initial T m,r) ∂lawMeasure (stackLaw (P m) L)
  rw [← AdaptiveKernel.fullPrefix_law (P m) L,lintegral_map hfm hp]

variable [Nonempty S]

def actualPrefix (ν : Measure M) (P : M → S × A → Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k : ℕ) : Measure (Input M Meta S A T k) :=
  (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (prefixInput T k)

instance actualPrefix_probability (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k : ℕ) :
    IsProbabilityMeasure (actualPrefix ν P hP π hπ planner s₀ dummy k) := by
  unfold actualPrefix
  exact Measure.isProbabilityMeasure_map (measurable_prefixInput T k).aemeasurable

def onlineHistory (ν : Measure M) (P : M → S × A → Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) : (k : ℕ) → Measure (Ctx M Meta S A T k)
  | 0 => ν.map (initial T)
  | k+1 => SourcePlanBlock.onlineNext π P hπ hP planner s₀ k ∘ₘ
      onlineHistory ν P hP π hπ planner s₀ k

instance onlineHistory_probability (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (k : ℕ) : IsProbabilityMeasure (onlineHistory ν P hP π hπ planner s₀ k) := by
  induction k with
  | zero =>
    change IsProbabilityMeasure (ν.map (initial (Meta := Meta) (S := S) (A := A) T))
    exact Measure.isProbabilityMeasure_map (measurable_initial T).aemeasurable
  | succ k ih =>
    change IsProbabilityMeasure (SourcePlanBlock.onlineNext π P hπ hP planner s₀ k ∘ₘ
      onlineHistory ν P hP π hπ planner s₀ k)
    infer_instance

theorem actualPrefix_zero (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (L : ℕ) :
    (actualPrefix ν P hP π hπ planner s₀ dummy 0).map (summary T 0 L s₀) =
      onlineHistory ν P hP π hπ planner s₀ 0 ⊗ₘ SourcePlanBlock.freshCtx P hP T 0 L := by
  have hi := measurable_initial (M := M) (Meta := Meta) (S := S) (A := A) T
  have hp := AdaptiveKernel.measurable_fullPrefix (Row := S × A) (S := S) L
  have hm : Measurable (fun x : M × ((S × A) × ℕ → S) =>
      (initial (Meta := Meta) T x.1,AdaptiveKernel.fullPrefix L x.2)) :=
    (hi.comp measurable_fst).prodMk (hp.comp measurable_snd)
  have hbase : (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map Prod.fst =
      InfiniteTapes.priorTapes ν P hP := by
    exact Measure.fst_compProd _ _
  rw [actualPrefix,Measure.map_map (measurable_summary T 0 L s₀) (measurable_prefixInput T 0)]
  change (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map
    (fun ω => summary T 0 L s₀ (prefixInput T 0 ω)) = _
  simp_rw [summary_zero]
  change (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map
    ((fun x => (initial T x.1,AdaptiveKernel.fullPrefix L x.2)) ∘ Prod.fst) = _
  rw [← Measure.map_map hm measurable_fst,hbase]
  exact initial_tape_joint ν P hP T L

variable [MeasurableSingletonClass M]

/-- The unused-window invariant for the actual finite prefixes of the one
infinite source measure. The all-episode statement is proved by induction. -/
theorem actual_prefix_fresh (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k L : ℕ) :
    (actualPrefix ν P hP π hπ planner s₀ dummy k).map (summary T k L s₀) =
      onlineHistory ν P hP π hπ planner s₀ k ⊗ₘ SourcePlanBlock.freshCtx P hP T k L := by
  apply SourceInduction.propagate_fresh T
    (actualPrefix ν P hP π hπ planner s₀ dummy)
    (onlineHistory ν P hP π hπ planner s₀)
    (SourceMarginals.stepDraw (protocolKernel π hπ planner s₀))
    (SourcePlanBlock.onlineNext π P hπ hP planner s₀)
    (SourcePlanBlock.freshCtx P hP T)
    (fun k L => summary T k L s₀) (fun k L => measurable_summary T k L s₀)
    (SourcePlanBlock.localBlock π hπ planner s₀)
  · intro j
    exact SourceMarginals.actual_prefix_succ (InfiniteTapes.priorTapes ν P hP)
      (protocolKernel π hπ planner s₀) dummy j
  · intro j
    rfl
  · exact actualPrefix_zero ν P hP π hπ planner s₀ dummy
  · exact SourceStepReplay.step_summary π hπ planner s₀
  · exact SourcePlanBlock.local_factorization π P hπ hP planner s₀

/-- The actual observed-history marginal is exactly the online true-transition
history law. This equality concerns the original source experiment. -/
theorem actual_context (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k : ℕ) :
    (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (actualContext T k s₀) =
      onlineHistory ν P hP π hπ planner s₀ k := by
  calc
    _ = (actualPrefix ν P hP π hπ planner s₀ dummy k).map (context T k s₀) := by
      rw [actualPrefix,Measure.map_map (measurable_context T k s₀) (measurable_prefixInput T k)]
      rfl
    _ = ((actualPrefix ν P hP π hπ planner s₀ dummy k).map (summary T k 0 s₀)).map Prod.fst := by
      rw [Measure.map_map measurable_fst (measurable_summary T k 0 s₀)]
      rfl
    _ = _ := by
      rw [actual_prefix_fresh ν P hP π hπ planner s₀ dummy k 0]
      exact Measure.fst_compProd _ _

/-- The actual observed history follows the genuine physical trajectory kernel
after each posterior/planner choice. -/
theorem actual_context_succ (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k : ℕ) :
    (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (actualContext T (k+1) s₀) =
      SourcePlanBlock.onlineNext π P hπ hP planner s₀ k ∘ₘ
        (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (actualContext T k s₀) := by
  rw [actual_context ν P hP π hπ planner s₀ dummy (k+1),
    actual_context ν P hP π hπ planner s₀ dummy k]
  rfl

/-- Joint freshness conditional on the actual latent model and observed
history, after every finite number of whole episodes. -/
theorem actual_fresh (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k L : ℕ) :
    (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map
      (fun ω => (actualContext T k s₀ ω,actualWindow T k L s₀ ω)) =
      (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (actualContext T k s₀) ⊗ₘ
        SourcePlanBlock.freshCtx P hP T k L := by
  rw [actual_context ν P hP π hπ planner s₀ dummy k]
  change (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map
    (summary T k L s₀ ∘ prefixInput T k) = _
  rw [← Measure.map_map (measurable_summary T k L s₀) (measurable_prefixInput T k)]
  exact actual_prefix_fresh ν P hP π hπ planner s₀ dummy k L

/-- The corresponding regular conditional law of the actual unused window. -/
theorem actual_fresh_condDistrib (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k L : ℕ) :
    condDistrib (actualWindow T k L s₀) (actualContext T k s₀)
      (SourceProtocol.measure ν P hP π hπ planner s₀ dummy) =ᵐ[
        (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (actualContext T k s₀)]
      SourcePlanBlock.freshCtx P hP T k L := by
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (measurable_actualContext T k s₀) (measurable_actualWindow T k L s₀)
    (actual_fresh ν P hP π hπ planner s₀ dummy k L)

def liftContext (T k : ℕ) (c : Ctx M Meta S A T k) : M × History Meta S A T :=
  (c.1,⟨k,c.2⟩)

lemma measurable_liftContext (T k : ℕ) :
    Measurable (liftContext (M := M) (Meta := Meta) (S := S) (A := A) T k) :=
  measurable_fst.prodMk ((measurable_history_mk k).comp measurable_snd)

def historyInfo (T k : ℕ) (s₀ : S) (ω : Sample M Meta S A T) : M × History Meta S A T :=
  (ω.1.1,SourceProtocol.history s₀ T k ω)

lemma historyInfo_eq (T k : ℕ) (s₀ : S) :
    historyInfo (M := M) (Meta := Meta) (A := A) T k s₀ =
      liftContext T k ∘ actualContext T k s₀ := rfl

lemma measurable_historyInfo (T k : ℕ) (s₀ : S) :
    Measurable (historyInfo (M := M) (Meta := Meta) (A := A) T k s₀) :=
  measurable_fst.fst.prodMk (SourceProtocol.measurable_history s₀ T k)

/-- Change only the retained information coordinate of a joint kernel law. -/
lemma map_joint_fst {X Y R : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace R] (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : ProbabilityTheory.Kernel X R) [IsMarkovKernel κ]
    (η : ProbabilityTheory.Kernel Y R) [IsMarkovKernel η]
    (f : X → Y) (hf : Measurable f) (hκη : ∀ x, κ x = η (f x)) :
    (μ ⊗ₘ κ).map (fun z => (f z.1,z.2)) = μ.map f ⊗ₘ η := by
  haveI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  apply (Measure.ext_iff_lintegral _).mpr
  intro g hg
  have hm : Measurable (fun z : X × R => (f z.1,z.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  have hfun : Measurable (fun z : X × R => g (f z.1,z.2)) := hg.comp hm
  have hi : Measurable (fun y => ∫⁻ r, g (y,r) ∂η y) := hg.lintegral_kernel_prod_right'
  rw [lintegral_map hg hm,Measure.lintegral_compProd hfun,
    Measure.lintegral_compProd hg,lintegral_map hi hf]
  apply lintegral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  rw [hκη x]

def freshHistory (P : M → S × A → Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) (T L : ℕ) :
    ProbabilityTheory.Kernel (M × History Meta S A T) (Stack (S × A) S L) :=
  (AdaptiveKernel.freshKernel P hP L).comap Prod.fst measurable_fst

instance freshHistory_markov (P : M → S × A → Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) (T L : ℕ) :
    IsMarkovKernel (freshHistory (Meta := Meta) P hP T L) := by
  unfold freshHistory
  infer_instance

/-- Freshness stated using the original variable-length observed history
itself, on the same source measure and the same original unused raw coordinates. -/
theorem actual_history_fresh (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k L : ℕ) :
    (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map
      (fun ω => (historyInfo T k s₀ ω,actualWindow T k L s₀ ω)) =
      (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (historyInfo T k s₀) ⊗ₘ
        freshHistory P hP T L := by
  haveI : IsProbabilityMeasure
      ((SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (actualContext T k s₀)) :=
    Measure.isProbabilityMeasure_map (measurable_actualContext T k s₀).aemeasurable
  have hpair : Measurable (fun ω : Sample M Meta S A T =>
      (actualContext T k s₀ ω,actualWindow T k L s₀ ω)) :=
    (measurable_actualContext T k s₀).prodMk (measurable_actualWindow T k L s₀)
  have hlift : Measurable (fun z : Ctx M Meta S A T k × Stack (S × A) S L =>
      (liftContext T k z.1,z.2)) :=
    ((measurable_liftContext T k).comp measurable_fst).prodMk measurable_snd
  calc
    _ = ((SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map
        (fun ω => (actualContext T k s₀ ω,actualWindow T k L s₀ ω))).map
          (fun z => (liftContext T k z.1,z.2)) := by
      rw [Measure.map_map hlift hpair]
      rfl
    _ = ((SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map
        (actualContext T k s₀) ⊗ₘ SourcePlanBlock.freshCtx P hP T k L).map
          (fun z => (liftContext T k z.1,z.2)) := by
      rw [actual_fresh ν P hP π hπ planner s₀ dummy k L]
    _ = _ := by
      rw [map_joint_fst _ (SourcePlanBlock.freshCtx P hP T k L)
        (freshHistory P hP T L)
        (liftContext T k) (measurable_liftContext T k) (fun _ => rfl),
        Measure.map_map (measurable_liftContext T k) (measurable_actualContext T k s₀)]
      rfl

theorem actual_history_fresh_condDistrib (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k L : ℕ) :
    condDistrib (actualWindow T k L s₀) (historyInfo T k s₀)
      (SourceProtocol.measure ν P hP π hπ planner s₀ dummy) =ᵐ[
        (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (historyInfo T k s₀)]
      freshHistory P hP T L := by
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (measurable_historyInfo T k s₀) (measurable_actualWindow T k L s₀)
    (actual_history_fresh ν P hP π hπ planner s₀ dummy k L)

end
end Paper36.SourceFresh
