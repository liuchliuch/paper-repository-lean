import Paper36.InfiniteProcessLaw

/-! Mixing the persistent raw-tape experiment over an arbitrary latent prior.
The fresh-unused-row conditional law is proved given both the true model and the
entire continuous learner history. No factorization of the model prior is used. -/
namespace Paper36.AdaptiveKernel
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes

variable {S Row Hist M : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist] [MeasurableSpace M]

/-- The measurable true-model-indexed law of the same persistent learner process. -/
def processKernel (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) (update : Hist × (Row × S) → Hist)
    (n : ℕ) (h : Hist) : ProbabilityTheory.Kernel M (InfiniteState Row S Hist) :=
  persistentKernel choose update n ∘ₖ (InfiniteTapes.rowKernel P hP).map (initialState h)

instance processKernel_markov (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n : ℕ) (h : Hist) :
    IsMarkovKernel (processKernel P hP choose update n h) := by
  haveI := persistentKernel_markov choose update hupdate n
  haveI := Kernel.IsMarkovKernel.map (InfiniteTapes.rowKernel P hP) (measurable_initialState h)
  unfold processKernel
  infer_instance

lemma processKernel_apply (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) (update : Hist × (Row × S) → Hist)
    (hupdate : Measurable update) (n : ℕ) (h : Hist) (m : M) :
    processKernel P hP choose update n h m = persistentLaw (P m) choose update hupdate n h := by
  unfold processKernel
  rw [Kernel.comp_apply, Kernel.map_apply _ (measurable_initialState h)]
  rfl

def historyKernel (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) (update : Hist × (Row × S) → Hist)
    (n : ℕ) (h : Hist) : ProbabilityTheory.Kernel M Hist :=
  (processKernel P hP choose update n h).map (fun x => x.2.2)

instance historyKernel_markov (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n : ℕ) (h : Hist) :
    IsMarkovKernel (historyKernel P hP choose update n h) := by
  haveI := processKernel_markov P hP choose update hupdate n h
  exact Kernel.IsMarkovKernel.map _ measurable_snd.snd

lemma historyKernel_apply (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n : ℕ) (h : Hist) (m : M) :
    historyKernel P hP choose update n h m = onlineKernel (P m) choose update n h := by
  rw [historyKernel, Kernel.map_apply _ measurable_snd.snd, processKernel_apply P hP choose update hupdate,
    persistentLaw_history]

/-- The measurable fresh product-row kernel, indexed only by the latent model. -/
def freshKernel (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (L : ℕ) : ProbabilityTheory.Kernel M (Stack Row S L) :=
  lawKernel (fun m => stackLaw (P m) L) (fun tape =>
    Finset.measurable_prod _ (fun c _ => hP c.1 (tape c)))

instance freshKernel_markov (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) (L : ℕ) :
    IsMarkovKernel (freshKernel P hP L) := lawKernel_markov _ _

/-- Product kernels are composition-products when the second component ignores history. -/
lemma kernel_compProd_prodMkRight {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (κ : ProbabilityTheory.Kernel X Y) [IsSFiniteKernel κ] (η : ProbabilityTheory.Kernel X Z) [IsSFiniteKernel η] :
    (κ ⊗ₖ η.prodMkRight Y) = κ ×ₖ η := by
  ext x : 1
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  rw [Kernel.lintegral_compProd _ _ _ hf, Kernel.lintegral_prod _ _ _ hf]
  rfl

/-- Pointwise fresh-unused independence is an equality of measurable model-indexed kernels. -/
theorem processKernel_window (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n L : ℕ) (h : Hist) :
    (processKernel P hP choose update n h).map (stateWindow L) =
      historyKernel P hP choose update n h ⊗ₖ (freshKernel P hP L).prodMkRight Hist := by
  haveI := processKernel_markov P hP choose update hupdate n h
  haveI := historyKernel_markov P hP choose update hupdate n h
  rw [kernel_compProd_prodMkRight]
  ext m : 1
  rw [Kernel.map_apply _ (measurable_stateWindow L), processKernel_apply P hP choose update hupdate,
    persistentLaw_window, Kernel.prod_apply, historyKernel_apply P hP choose update hupdate]
  rfl

def mixedLaw (ν : Measure M) (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) (update : Hist × (Row × S) → Hist)
    (_hupdate : Measurable update) (n : ℕ) (h : Hist) : Measure (M × InfiniteState Row S Hist) :=
  ν ⊗ₘ processKernel P hP choose update n h

instance mixedLaw_probability (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n : ℕ) (h : Hist) :
    IsProbabilityMeasure (mixedLaw ν P hP choose update hupdate n h) := by
  haveI := processKernel_markov P hP choose update hupdate n h
  unfold mixedLaw
  infer_instance

theorem mixedLaw_history (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n : ℕ) (h : Hist) :
    (mixedLaw ν P hP choose update hupdate n h).map (fun z => (z.1,z.2.2.2)) =
      ν ⊗ₘ historyKernel P hP choose update n h := by
  haveI := processKernel_markov P hP choose update hupdate n h
  exact (Measure.compProd_map measurable_snd.snd).symm

theorem mixedLaw_joint (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n L : ℕ) (h : Hist) :
    (mixedLaw ν P hP choose update hupdate n h).map (fun z => ((z.1,z.2.2.2),(stateWindow L z.2).2)) =
      (ν ⊗ₘ historyKernel P hP choose update n h) ⊗ₘ (freshKernel P hP L).prodMkRight Hist := by
  haveI := processKernel_markov P hP choose update hupdate n h
  haveI := historyKernel_markov P hP choose update hupdate n h
  calc
    _ = (ν ⊗ₘ (processKernel P hP choose update n h).map (stateWindow L)).map MeasurableEquiv.prodAssoc.symm := by
      rw [Measure.compProd_map (measurable_stateWindow L), Measure.map_map (by fun_prop) (measurable_id.prodMap (measurable_stateWindow L))]
      rfl
    _ = _ := by rw [processKernel_window P hP choose update hupdate, Measure.compProd_assoc]

/-- The arbitrary-prior conditional-unused-stack theorem at the exact analyst
information (latent model, full learner history). -/
theorem mixedLaw_unused_condDistrib [Nonempty S]
    (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → Row → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsMarkovKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (n L : ℕ) (h : Hist) :
    condDistrib (fun z : M × InfiniteState Row S Hist => (stateWindow L z.2).2)
      (fun z => (z.1,z.2.2.2)) (mixedLaw ν P hP choose update hupdate n h) =ᵐ[ν ⊗ₘ historyKernel P hP choose update n h]
        (freshKernel P hP L).prodMkRight Hist := by
  haveI := mixedLaw_probability ν P hP choose update hupdate n h
  have hjoint := mixedLaw_joint ν P hP choose update hupdate n L h
  rw [← mixedLaw_history ν P hP choose update hupdate n h] at hjoint
  have hc := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := mixedLaw ν P hP choose update hupdate n h) (measurable_fst.prodMk measurable_snd.snd.snd)
    ((measurable_stateWindow L).snd.comp measurable_snd) hjoint
  simpa only [mixedLaw_history ν P hP choose update hupdate] using hc

end
end Paper36.AdaptiveKernel
