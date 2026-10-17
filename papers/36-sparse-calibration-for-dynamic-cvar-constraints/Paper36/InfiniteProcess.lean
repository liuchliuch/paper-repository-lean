import Paper36.InfiniteExecution

/-! A single persistent raw-tape Markov process. Every finite execution is a
projection of this same process, so its finite laws are automatically compatible
with the infinite-history construction used by the source experiment. -/
namespace Paper36.AdaptiveKernel
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes

variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

abbrev InfiniteState (Row S Hist : Type*) := (Row × ℕ → S) × ((Row → ℕ) × Hist)

def stateWindow (L : ℕ) (x : InfiniteState Row S Hist) : Hist × Stack Row S L :=
  (x.2.2, window (fun r j => x.1 (r,j)) x.2.1 L)

omit [Fintype S] [DiscreteMeasurableSpace S] in
lemma measurable_eval_countable {I : Type*} [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] :
    Measurable (fun x : (I → S) × I => x.1 x.2) :=
  measurable_from_prod_countable_left fun i => measurable_pi_apply i

lemma measurable_stateWindow (L : ℕ) : Measurable (stateWindow (Row := Row) (S := S) (Hist := Hist) L) := by
  apply measurable_snd.snd.prodMk
  apply measurable_pi_lambda
  intro c
  have hc0 : Measurable (fun x : InfiniteState Row S Hist => x.2.1 c.1) :=
    (measurable_pi_apply c.1).comp measurable_snd.fst
  have hc : Measurable (fun x : InfiniteState Row S Hist => x.2.1 c.1 + c.2.val) := hc0.add_const c.2.val
  exact measurable_eval_countable.comp (measurable_fst.prodMk (measurable_const.prodMk hc))

def persistentConsume (update : Hist × (Row × S) → Hist) :
    InfiniteState Row S Hist × (Row × Hist) → InfiniteState Row S Hist :=
  fun z => (z.1.1, (increment z.1.2.1 z.2.1,
    update (z.2.2, (z.2.1, z.1.1 (z.2.1, z.1.2.1 z.2.1)))))

lemma measurable_persistentConsume (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) :
    Measurable (persistentConsume update) := by
  have hcount : Measurable (fun z : InfiniteState Row S Hist × (Row × Hist) => z.1.2.1 z.2.1) :=
    measurable_eval_countable.comp (measurable_fst.snd.fst.prodMk measurable_snd.fst)
  have hread : Measurable (fun z : InfiniteState Row S Hist × (Row × Hist) => z.1.1 (z.2.1,z.1.2.1 z.2.1)) :=
    measurable_eval_countable.comp (measurable_fst.fst.prodMk (measurable_snd.fst.prodMk hcount))
  have hinc : Measurable (fun z : InfiniteState Row S Hist × (Row × Hist) => increment z.1.2.1 z.2.1) := by
    apply measurable_pi_lambda
    intro r
    apply ((measurable_pi_apply r).comp measurable_fst.snd.fst).add
    exact (measurable_of_countable (fun q : Row => if r = q then (1:ℕ) else 0)).comp measurable_snd.fst
  exact measurable_fst.fst.prodMk (hinc.prodMk
    (hupdate.comp (measurable_snd.snd.prodMk (measurable_snd.fst.prodMk hread))))

/-- The physical transition reads precisely the next unused original tape entry. -/
theorem stateWindow_consume (update : Hist × (Row × S) → Hist)
    (L : ℕ) (x : InfiniteState Row S Hist) (rh : Row × Hist) :
    stateWindow L (persistentConsume update (x,rh)) =
      consume update L (stateWindow (L+1) x, rh) := by
  apply Prod.ext
  · simp only [stateWindow, persistentConsume, consume, head_window]
  · exact (remaining_window (fun r j => x.1 (r,j)) x.2.1 L rh.1).symm

def persistentStep (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    (update : Hist × (Row × S) → Hist) : ProbabilityTheory.Kernel (InfiniteState Row S Hist) (InfiniteState Row S Hist) :=
  (ProbabilityTheory.Kernel.id ×ₖ choose.comap (fun x => x.2.2) measurable_snd.snd).map (persistentConsume update)

instance persistentStep_markov (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) :
    IsMarkovKernel (persistentStep choose update) := by
  unfold persistentStep
  exact Kernel.IsMarkovKernel.map _ (measurable_persistentConsume update hupdate)

lemma persistentStep_lintegral (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (f : InfiniteState Row S Hist → ℝ≥0∞) (hf : Measurable f) (x : InfiniteState Row S Hist) :
    (∫⁻ y, f y ∂persistentStep choose update x) =
      ∫⁻ rh, f (persistentConsume update (x,rh)) ∂choose x.2.2 := by
  unfold persistentStep
  rw [Kernel.lintegral_map _ (measurable_persistentConsume update hupdate) _ hf]
  have hm : Measurable (fun z : InfiniteState Row S Hist × (Row × Hist) => f (persistentConsume update z)) :=
    hf.comp (measurable_persistentConsume update hupdate)
  rw [Kernel.id, Kernel.lintegral_deterministic_prod measurable_id _ _ hm]
  rfl

def persistentKernel (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    (update : Hist × (Row × S) → Hist) : ℕ → ProbabilityTheory.Kernel (InfiniteState Row S Hist) (InfiniteState Row S Hist)
  | 0 => ProbabilityTheory.Kernel.id
  | n+1 => persistentKernel choose update n ∘ₖ persistentStep choose update

instance persistentKernel_markov (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n : ℕ) :
    IsMarkovKernel (persistentKernel choose update n) := by
  induction n with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ n ih =>
    haveI := persistentStep_markov choose update hupdate
    change IsMarkovKernel (persistentKernel choose update n ∘ₖ persistentStep choose update)
    infer_instance

/-- Every finite raw-stack execution is a projection of the same persistent
process. This is the required compatibility between all finite run lengths. -/
theorem persistentKernel_window (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (n L : ℕ) (x : InfiniteState Row S Hist) :
    (persistentKernel choose update n x).map (stateWindow L) =
      residualKernel choose update hupdate L n (stateWindow (L+n) x) := by
  induction n generalizing L x with
  | zero =>
    simp only [persistentKernel, residualKernel, Kernel.id_apply,
      Measure.map_dirac (measurable_stateWindow L), Nat.add_zero]
  | succ n ih =>
    apply (Measure.ext_iff_lintegral _).mpr
    intro f hf
    have hfm : Measurable (fun y : InfiniteState Row S Hist => f (stateWindow L y)) :=
      hf.comp (measurable_stateWindow L)
    rw [lintegral_map hf (measurable_stateWindow L), persistentKernel,
      Kernel.lintegral_comp _ _ _ hfm]
    have hi (z : InfiniteState Row S Hist) :
        (∫⁻ y, f (stateWindow L y) ∂persistentKernel choose update n z) =
          ∫⁻ y, f y ∂residualKernel choose update hupdate L n (stateWindow (L+n) z) := by
      rw [← lintegral_map hf (measurable_stateWindow L), ih]
    simp_rw [hi]
    have hg : Measurable (fun z : InfiniteState Row S Hist =>
        ∫⁻ y, f y ∂residualKernel choose update hupdate L n (stateWindow (L+n) z)) :=
      hf.lintegral_kernel.comp (measurable_stateWindow _)
    rw [persistentStep_lintegral choose update hupdate _ hg, residualKernel,
      Kernel.lintegral_comp _ _ _ hf]
    have hgm : Measurable (fun b : Hist × Stack Row S (L+n) =>
        ∫⁻ y, f y ∂residualKernel choose update hupdate L n b) := hf.lintegral_kernel
    calc
      _ = ∫⁻ rh, ∫⁻ y, f y ∂residualKernel choose update hupdate L n
          (consume update (L+n) (stateWindow (L+n+1) x,rh)) ∂choose x.2.2 := by
        apply lintegral_congr_ae
        apply ae_of_all
        intro rh
        exact congrArg (fun b => ∫⁻ y, f y ∂residualKernel choose update hupdate L n b)
          (stateWindow_consume update (L+n) x rh)
      _ = _ := (popKernel_lintegral choose update hupdate (L+n)
        (fun b : Hist × Stack Row S (L+n) => ∫⁻ y, f y ∂residualKernel choose update hupdate L n b)
        hgm (stateWindow (L+(n+1)) x)).symm

end
end Paper36.AdaptiveKernel
