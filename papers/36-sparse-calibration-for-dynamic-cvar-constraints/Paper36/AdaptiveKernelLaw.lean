import Paper36.AdaptiveKernel

/-! Native probability laws for the general adaptive kernel coupling. The raw
stack, retained learner history and unused stack are sampled by actual Markov
kernels. Their product-law and conditional-distribution conclusions are derived. -/
namespace Paper36.AdaptiveKernel
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes

variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

/-- One actual raw-stack read retains all of the choice kernel's learner state. -/
def consume (update : Hist × (Row × S) → Hist) (n : ℕ) :
    (Hist × Stack Row S (n+1)) × (Row × Hist) → Hist × Stack Row S n :=
  fun x => (update (x.2.2, (x.2.1, head x.2.1 x.1.2)), remaining x.2.1 x.1.2)

lemma measurable_consume (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n : ℕ) :
    Measurable (consume update n) := by
  have hfinite : Measurable (fun x : (Hist × Stack Row S (n+1)) × (Row × Hist) =>
      (x.2.1, x.1.2)) := measurable_snd.fst.prodMk measurable_fst.snd
  have hh := (measurable_of_countable (fun z : Row × Stack Row S (n+1) => head z.1 z.2)).comp hfinite
  have hr := (measurable_of_countable (fun z : Row × Stack Row S (n+1) => remaining z.1 z.2)).comp hfinite
  exact (hupdate.comp (measurable_snd.snd.prodMk (measurable_snd.fst.prodMk hh))).prodMk hr

def popKernel (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n : ℕ) :
    ProbabilityTheory.Kernel (Hist × Stack Row S (n+1)) (Hist × Stack Row S n) :=
  (ProbabilityTheory.Kernel.id ×ₖ choose.comap Prod.fst measurable_fst).map (consume update n)

instance popKernel_markov (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n : ℕ) :
    IsMarkovKernel (popKernel choose update hupdate n) := by
  unfold popKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_consume update hupdate n)

lemma popKernel_lintegral (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n : ℕ)
    (f : Hist × Stack Row S n → ℝ≥0∞) (hf : Measurable f) (x : Hist × Stack Row S (n+1)) :
    (∫⁻ y, f y ∂popKernel choose update hupdate n x) =
      ∫⁻ rh, f (update (rh.2, (rh.1, head rh.1 x.2)), remaining rh.1 x.2) ∂choose x.1 := by
  unfold popKernel
  rw [Kernel.lintegral_map _ (measurable_consume update hupdate n) _ hf]
  have hm : Measurable (fun z : (Hist × Stack Row S (n+1)) × (Row × Hist) => f (consume update n z)) :=
    hf.comp (measurable_consume update hupdate n)
  rw [Kernel.id, Kernel.lintegral_deterministic_prod measurable_id _ _ hm]
  rfl

/-- The complete canonical finite experiment, including its unused stacks. -/
def residualKernel (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (L : ℕ) :
    (n : ℕ) → ProbabilityTheory.Kernel (Hist × Stack Row S (L+n)) (Hist × Stack Row S L)
  | 0 => ProbabilityTheory.Kernel.id
  | n+1 => residualKernel choose update hupdate L n ∘ₖ popKernel choose update hupdate (L+n)

instance residualKernel_markov (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (L n : ℕ) :
    IsMarkovKernel (residualKernel choose update hupdate L n) := by
  induction n with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ n ih =>
    change IsMarkovKernel (residualKernel choose update hupdate L n ∘ₖ popKernel choose update hupdate (L+n))
    infer_instance

/-- The functional coupling is the integral of the constructed execution kernel. -/
theorem residualKernel_lintegral (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (L : ℕ)
    (f : Hist × Stack Row S L → ℝ≥0∞) (hf : Measurable f) (n : ℕ)
    (x : Hist × Stack Row S (L+n)) :
    (∫⁻ y, f y ∂residualKernel choose update hupdate L n x) =
      residualLValue choose update L f n x.1 x.2 := by
  induction n with
  | zero => exact Kernel.lintegral_id' hf x
  | succ n ih =>
    rw [residualKernel, Kernel.lintegral_comp _ _ _ hf]
    simp_rw [ih]
    exact popKernel_lintegral choose update hupdate (L+n) _
      (measurable_residualLValue choose update hupdate L f hf n) x

/-- The online true-row sampling kernel after a general learner choice. -/
def trueRowKernel (P : Row → Law S) : ProbabilityTheory.Kernel (Row × Hist) S :=
  lawKernel (fun rh => P rh.1) (fun s =>
    (measurable_of_countable (fun r => (P r).mass s)).comp measurable_fst)

instance trueRowKernel_markov (P : Row → Law S) : IsMarkovKernel (trueRowKernel (Hist := Hist) P) := by
  unfold trueRowKernel
  infer_instance

def updateKernel (P : Row → Law S) (update : Hist × (Row × S) → Hist) :
    ProbabilityTheory.Kernel (Row × Hist) Hist :=
  (ProbabilityTheory.Kernel.id ×ₖ trueRowKernel P).map (fun z => update (z.1.2, (z.1.1, z.2)))

instance updateKernel_markov (P : Row → Law S) (update : Hist × (Row × S) → Hist)
    (hupdate : Measurable update) : IsMarkovKernel (updateKernel P update) := by
  unfold updateKernel
  exact Kernel.IsMarkovKernel.map _ (hupdate.comp (measurable_fst.snd.prodMk (measurable_fst.fst.prodMk measurable_snd)))

def onlineKernel (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    (update : Hist × (Row × S) → Hist) : ℕ → ProbabilityTheory.Kernel Hist Hist
  | 0 => ProbabilityTheory.Kernel.id
  | n+1 => onlineKernel P choose update n ∘ₖ updateKernel P update ∘ₖ choose

instance onlineKernel_markov (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n : ℕ) :
    IsMarkovKernel (onlineKernel P choose update n) := by
  induction n with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ n ih =>
    haveI := updateKernel_markov P update hupdate
    change IsMarkovKernel (onlineKernel P choose update n ∘ₖ updateKernel P update ∘ₖ choose)
    infer_instance

lemma updateKernel_lintegral (P : Row → Law S) (update : Hist × (Row × S) → Hist)
    (hupdate : Measurable update) (f : Hist → ℝ≥0∞) (hf : Measurable f) (rh : Row × Hist) :
    (∫⁻ h, f h ∂updateKernel P update rh) =
      ∫⁻ y, f (update (rh.2, (rh.1,y))) ∂lawMeasure (P rh.1) := by
  unfold updateKernel
  have hu : Measurable (fun z : (Row × Hist) × S => update (z.1.2, (z.1.1, z.2))) :=
    hupdate.comp (measurable_fst.snd.prodMk (measurable_fst.fst.prodMk measurable_snd))
  rw [Kernel.lintegral_map _ hu _ hf]
  have hm : Measurable (fun z : (Row × Hist) × S => f (update (z.1.2, (z.1.1, z.2)))) := hf.comp hu
  rw [Kernel.id, Kernel.lintegral_deterministic_prod measurable_id _ _ hm]
  rfl

theorem onlineKernel_lintegral (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (f : Hist → ℝ≥0∞) (hf : Measurable f) (n : ℕ) (h : Hist) :
    (∫⁻ h', f h' ∂onlineKernel P choose update n h) = onlineLValue P choose update f n h := by
  induction n generalizing h with
  | zero => exact Kernel.lintegral_id' hf h
  | succ n ih =>
    rw [onlineKernel, Kernel.lintegral_comp _ _ _ hf]
    simp_rw [Kernel.lintegral_comp _ _ _ hf]
    simp_rw [updateKernel_lintegral P update hupdate _ hf.lintegral_kernel, ih]
    rfl

/-- The original raw stack is retained alongside the actual execution output. -/
def rawExecution (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (L n : ℕ) (h : Hist) :
    Measure (Stack Row S (L+n) × (Hist × Stack Row S L)) :=
  lawMeasure (stackLaw P (L+n)) ⊗ₘ
    (residualKernel choose update hupdate L n).comap (fun tape => (h,tape))
      (measurable_const.prodMk measurable_id)

instance rawExecution_probability (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L n : ℕ) (h : Hist) : IsProbabilityMeasure (rawExecution P choose update hupdate L n h) := by
  unfold rawExecution
  infer_instance

/-- Adding the complete learner execution preserves the original iid tape marginal. -/
theorem rawExecution_tape (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L n : ℕ) (h : Hist) :
    (rawExecution P choose update hupdate L n h).map Prod.fst = lawMeasure (stackLaw P (L+n)) :=
  Measure.fst_compProd _ _

theorem rawExecution_lintegral (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L n : ℕ) (h : Hist) (f : Hist × Stack Row S L → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, f y ∂(rawExecution P choose update hupdate L n h).map Prod.snd) =
      ∫⁻ y, f y ∂(onlineKernel P choose update n h).prod (lawMeasure (stackLaw P L)) := by
  calc
    _ = ∫⁻ z, f z.2 ∂rawExecution P choose update hupdate L n h := lintegral_map hf measurable_snd
    _ = ∫⁻ tape, residualLValue choose update L f n h tape ∂lawMeasure (stackLaw P (L+n)) := by
      have hfs : Measurable (fun z : Stack Row S (L+n) × (Hist × Stack Row S L) => f z.2) := hf.comp measurable_snd
      rw [rawExecution, Measure.lintegral_compProd hfs]
      simp only [Kernel.comap_apply, residualKernel_lintegral choose update hupdate L f hf]
    _ = onlineLValue P choose update (fun h => ∫⁻ tape, f (h,tape) ∂lawMeasure (stackLaw P L)) n h :=
      adaptive_kernel_unused_independent P choose update hupdate L f hf n h
    _ = _ := by
      rw [lintegral_prod_of_measurable f hf,
        onlineKernel_lintegral P choose update hupdate _ hf.lintegral_prod_right']

/-- Exact equality of the native joint laws. The history is the original online
history and every unused row still has its independent original product law. -/
theorem rawExecution_joint (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L n : ℕ) (h : Hist) :
    (rawExecution P choose update hupdate L n h).map Prod.snd =
      (onlineKernel P choose update n h).prod (lawMeasure (stackLaw P L)) := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  exact rawExecution_lintegral P choose update hupdate L n h f hf

theorem rawExecution_history (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L n : ℕ) (h : Hist) :
    (rawExecution P choose update hupdate L n h).map (fun z => z.2.1) = onlineKernel P choose update n h := by
  rw [show (fun z : Stack Row S (L+n) × (Hist × Stack Row S L) => z.2.1) = Prod.fst ∘ Prod.snd from rfl,
    ← Measure.map_map measurable_fst measurable_snd, rawExecution_joint, Measure.map_fst_prod,
    measure_univ, one_smul]

/-- The canonical process has the exact fresh-unused-stack conditional law after
arbitrary continuous posterior choices and adaptive observations. -/
theorem rawExecution_unused_condDistrib [Nonempty S]
    (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (L n : ℕ) (h : Hist) :
    condDistrib (fun z : Stack Row S (L+n) × (Hist × Stack Row S L) => z.2.2)
      (fun z => z.2.1) (rawExecution P choose update hupdate L n h) =ᵐ[onlineKernel P choose update n h]
        Kernel.const Hist (lawMeasure (stackLaw P L)) := by
  haveI := onlineKernel_markov P choose update hupdate n
  have hjoint : (rawExecution P choose update hupdate L n h).map (fun z => (z.2.1,z.2.2)) =
      (rawExecution P choose update hupdate L n h).map (fun z => z.2.1) ⊗ₘ
        Kernel.const Hist (lawMeasure (stackLaw P L)) := by
    rw [rawExecution_history, Measure.compProd_const]
    exact rawExecution_joint P choose update hupdate L n h
  have hc := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := rawExecution P choose update hupdate L n h) measurable_snd.fst measurable_snd.snd hjoint
  simpa only [rawExecution_history] using hc


end
end Paper36.AdaptiveKernel
