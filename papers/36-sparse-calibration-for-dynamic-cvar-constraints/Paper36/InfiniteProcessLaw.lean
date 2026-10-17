import Paper36.InfiniteProcess

/-! Laws of the persistent process started from the original iid row tapes.
All horizons are marginals of this same Markov process; no fresh-tape sampling
is restarted between episodes. -/
namespace Paper36.AdaptiveKernel
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes

variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

def initialState (h : Hist) (tape : Row × ℕ → S) : InfiniteState Row S Hist :=
  (tape, (fun _ => 0, h))

lemma measurable_initialState (h : Hist) : Measurable (initialState (Row := Row) (S := S) h) :=
  measurable_id.prodMk (measurable_const.prodMk measurable_const)

def initialLaw (P : Row → Law S) (h : Hist) : Measure (InfiniteState Row S Hist) :=
  (InfiniteTapes.infiniteLaw (fun c : Row × ℕ => P c.1)).map (initialState h)

instance initialLaw_probability (P : Row → Law S) (h : Hist) : IsProbabilityMeasure (initialLaw P h) := by
  unfold initialLaw
  exact Measure.isProbabilityMeasure_map (measurable_initialState h).aemeasurable

def persistentLaw (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    (update : Hist × (Row × S) → Hist) (_hupdate : Measurable update) (n : ℕ) (h : Hist) :
    Measure (InfiniteState Row S Hist) := persistentKernel choose update n ∘ₘ initialLaw P h

instance persistentLaw_probability (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (n : ℕ) (h : Hist) : IsProbabilityMeasure (persistentLaw P choose update hupdate n h) := by
  haveI := persistentKernel_markov choose update hupdate n
  unfold persistentLaw
  infer_instance

@[simp] theorem stateWindow_initialState (L : ℕ) (h : Hist) (tape : Row × ℕ → S) :
    stateWindow L (initialState h tape) = (h, fullPrefix L tape) := by
  apply Prod.ext
  · rfl
  · funext c
    simp only [stateWindow, initialState, window, fullPrefix, Nat.zero_add]

/-- The same persistent process, after any finite number of row reads, has the
online learner history law times independent fresh unused rows. -/
theorem persistentLaw_window (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (n L : ℕ) (h : Hist) :
    (persistentLaw P choose update hupdate n h).map (stateWindow L) =
      (onlineKernel P choose update n h).prod (lawMeasure (stackLaw P L)) := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  have hfw : Measurable (fun x : InfiniteState Row S Hist => f (stateWindow L x)) := hf.comp (measurable_stateWindow L)
  have hk : Measurable (fun x : InfiniteState Row S Hist =>
      ∫⁻ y, f (stateWindow L y) ∂persistentKernel choose update n x) := hfw.lintegral_kernel
  have hr : Measurable (fun tape : Stack Row S (L+n) => residualLValue choose update L f n h tape) :=
    (measurable_residualLValue choose update hupdate L f hf n).comp (measurable_const.prodMk measurable_id)
  calc
    _ = ∫⁻ x, f (stateWindow L x) ∂persistentLaw P choose update hupdate n h :=
      lintegral_map hf (measurable_stateWindow L)
    _ = ∫⁻ x, ∫⁻ y, f (stateWindow L y) ∂persistentKernel choose update n x ∂initialLaw P h := by
      exact Measure.lintegral_bind (persistentKernel choose update n).aemeasurable hfw.aemeasurable
    _ = ∫⁻ tape, ∫⁻ y, f (stateWindow L y) ∂persistentKernel choose update n (initialState h tape)
        ∂InfiniteTapes.infiniteLaw (fun c : Row × ℕ => P c.1) := lintegral_map hk (measurable_initialState h)
    _ = ∫⁻ tape, residualLValue choose update L f n h (fullPrefix (L+n) tape)
        ∂InfiniteTapes.infiniteLaw (fun c : Row × ℕ => P c.1) := by
      apply lintegral_congr_ae
      apply ae_of_all
      intro tape
      dsimp only
      rw [← lintegral_map hf (measurable_stateWindow L), persistentKernel_window choose update hupdate,
        stateWindow_initialState, residualKernel_lintegral choose update hupdate L f hf]
    _ = ∫⁻ tape, residualLValue choose update L f n h tape ∂lawMeasure (stackLaw P (L+n)) := by
      rw [← fullPrefix_law P (L+n), lintegral_map hr (measurable_fullPrefix _)]
    _ = onlineLValue P choose update (fun h => ∫⁻ tape, f (h,tape) ∂lawMeasure (stackLaw P L)) n h :=
      adaptive_kernel_unused_independent P choose update hupdate L f hf n h
    _ = _ := by
      rw [lintegral_prod f hf.aemeasurable,
        onlineKernel_lintegral P choose update hupdate _ hf.lintegral_prod_right']

theorem persistentLaw_history (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (n : ℕ) (h : Hist) :
    (persistentLaw P choose update hupdate n h).map (fun x => x.2.2) = onlineKernel P choose update n h := by
  have he := congrArg (fun ν : Measure (Hist × Stack Row S 0) => ν.map Prod.fst)
    (persistentLaw_window P choose update hupdate n 0 h)
  simpa only [Measure.map_map measurable_fst (measurable_stateWindow 0), Function.comp_def,
    stateWindow, Measure.map_fst_prod, measure_univ, one_smul] using he

/-- In the persistent, single-tape experiment the entire remaining window is
conditionally fresh given the full learner history. -/
theorem persistentLaw_unused_condDistrib [Nonempty S]
    (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n L : ℕ) (h : Hist) :
    condDistrib (fun x : InfiniteState Row S Hist => (stateWindow L x).2) (fun x => x.2.2)
      (persistentLaw P choose update hupdate n h) =ᵐ[onlineKernel P choose update n h]
        Kernel.const Hist (lawMeasure (stackLaw P L)) := by
  haveI := onlineKernel_markov P choose update hupdate n
  have hjoint : (persistentLaw P choose update hupdate n h).map (fun x => (x.2.2,(stateWindow L x).2)) =
      (persistentLaw P choose update hupdate n h).map (fun x => x.2.2) ⊗ₘ Kernel.const Hist (lawMeasure (stackLaw P L)) := by
    rw [persistentLaw_history, Measure.compProd_const]
    exact persistentLaw_window P choose update hupdate n L h
  have hc := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := persistentLaw P choose update hupdate n h) measurable_snd.snd (measurable_stateWindow L).snd hjoint
  simpa only [persistentLaw_history] using hc

end
end Paper36.AdaptiveKernel
