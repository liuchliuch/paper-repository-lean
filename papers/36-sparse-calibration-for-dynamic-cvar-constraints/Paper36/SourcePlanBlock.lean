import Paper36.SourceBlockReplay
import Paper36.SourceBlockKernel
import Paper36.SourceHistory

/-! Arbitrary continuous posterior/planner choices commute with fresh original
row stacks. The actual whole-episode local factorization used by the concrete
source induction is proved here. -/
namespace Paper36.SourcePlanBlock
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes

section Generic
variable {H Meta R O : Type*} [MeasurableSpace H] [MeasurableSpace Meta]
  [MeasurableSpace R] [MeasurableSpace O]

def plannedKernel (planner : ProbabilityTheory.Kernel H Meta)
    (block : ProbabilityTheory.Kernel ((H × Meta) × R) O) : ProbabilityTheory.Kernel (H × R) (Meta × O) :=
  planner.comap Prod.fst measurable_fst ⊗ₖ block.comap
    (fun z : (H × R) × Meta => ((z.1.1,z.2),z.1.2))
    ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

instance plannedKernel_markov (planner : ProbabilityTheory.Kernel H Meta) [IsMarkovKernel planner]
    (block : ProbabilityTheory.Kernel ((H × Meta) × R) O) [IsMarkovKernel block] :
    IsMarkovKernel (plannedKernel planner block) := by unfold plannedKernel; infer_instance

/-- Fubini for the learner's arbitrary continuous choice and the fresh row
window, followed by the proved native block average. -/
theorem averaged_plannedKernel (fresh : ProbabilityTheory.Kernel H R) [IsMarkovKernel fresh]
    (planner : ProbabilityTheory.Kernel H Meta) [IsMarkovKernel planner]
    (block : ProbabilityTheory.Kernel ((H × Meta) × R) O) [IsMarkovKernel block]
    (average : ProbabilityTheory.Kernel (H × Meta) O) [IsMarkovKernel average]
    (haverage : (fresh.comap Prod.fst measurable_fst ⊗ₖ block).map Prod.snd = average) :
    (fresh ⊗ₖ plannedKernel planner block).map Prod.snd = planner ⊗ₖ average := by
  ext h : 1
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  have hfs : Measurable (fun z : R × (Meta × O) => f z.2) := hf.comp measurable_snd
  rw [Kernel.lintegral_map _ measurable_snd _ hf,Kernel.lintegral_compProd _ _ _ hfs]
  simp_rw [plannedKernel,Kernel.lintegral_compProd _ _ _ hf]
  change (∫⁻ r, ∫⁻ m, ∫⁻ o, f (m,o) ∂block ((h,m),r) ∂planner h ∂fresh h) =
    ∫⁻ m, ∫⁻ o, f (m,o) ∂average (h,m) ∂planner h
  let η : ProbabilityTheory.Kernel (R × Meta) O := block.comap
    (fun z => ((h,z.2),z.1)) ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
  have hfo : Measurable (fun z : (R × Meta) × O => f (z.1.2,z.2)) :=
    hf.comp (measurable_fst.snd.prodMk measurable_snd)
  have hint : Measurable (fun z : R × Meta => ∫⁻ o, f (z.2,o) ∂block ((h,z.2),z.1)) :=
    hfo.lintegral_kernel_prod_right' (κ := η)
  rw [lintegral_lintegral_swap hint.aemeasurable]
  apply lintegral_congr_ae
  apply ae_of_all
  intro m
  have hfm : Measurable (fun o => f (m,o)) := hf.comp measurable_prodMk_left
  have he := congrArg (fun κ : ProbabilityTheory.Kernel (H × Meta) O => ∫⁻ o, f (m,o) ∂κ (h,m)) haverage
  have hfg : Measurable (fun z : R × O => f (m,z.2)) := hfm.comp measurable_snd
  dsimp only at he ⊢
  rw [Kernel.lintegral_map _ measurable_snd _ hfm,Kernel.lintegral_compProd _ _ _ hfg] at he
  exact he

end Generic

universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta]

abbrev Ctx (M Meta : Type*) (S A : Type u) (T k : ℕ) := M × SourceHistory.Data Meta S A T k

def ctxHistory (T k : ℕ) (x : Ctx M Meta S A T k) : SourceReplay.History Meta S A T := ⟨k,x.2⟩

lemma measurable_ctxHistory (T k : ℕ) : Measurable (ctxHistory (M := M) (Meta := Meta) (S := S) (A := A) T k) :=
  (SourceReplay.measurable_history_mk k).comp measurable_snd

def plannerAt (planner : ProbabilityTheory.Kernel (SourceReplay.History Meta S A T) Meta) (k : ℕ) :
    ProbabilityTheory.Kernel (Ctx M Meta S A T k) Meta :=
  planner.comap (ctxHistory T k) (measurable_ctxHistory T k)

instance plannerAt_markov (planner : ProbabilityTheory.Kernel (SourceReplay.History Meta S A T) Meta)
    [IsMarkovKernel planner] (k : ℕ) : IsMarkovKernel (plannerAt (M := M) planner k) := by
  unfold plannerAt
  infer_instance

def freshCtx (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (T k L : ℕ) : ProbabilityTheory.Kernel (Ctx M Meta S A T k) (Stack (S × A) S L) :=
  (AdaptiveKernel.freshKernel P hP L).comap Prod.fst measurable_fst

instance freshCtx_markov (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (T k L : ℕ) : IsMarkovKernel (freshCtx (Meta := Meta) P hP T k L) := by
  unfold freshCtx
  infer_instance

def appendCtx (T k : ℕ) (x : Ctx M Meta S A T k) (z : Meta × Trajectory S A T) : Ctx M Meta S A T (k+1) :=
  (x.1,SourceHistory.append T k x.2 z)

lemma measurable_appendCtx (T k : ℕ) :
    Measurable (fun z : Ctx M Meta S A T k × (Meta × Trajectory S A T) => appendCtx T k z.1 z.2) :=
  measurable_fst.fst.prodMk ((SourceHistory.measurable_append T k).comp (measurable_fst.snd.prodMk measurable_snd))

def physicalBlock (π : Meta → Policy S A)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (T k L : ℕ) (s₀ : S) :
    ProbabilityTheory.Kernel ((Ctx M Meta S A T k × Meta) × Stack (S × A) S (L+T))
      (Trajectory S A T × Stack (S × A) S L) :=
  SourceBlockKernel.blockKernel (fun z : Ctx M Meta S A T k × Meta => π z.2)
    (fun h s a => (hπ h s a).comp measurable_snd) L T s₀

instance physicalBlock_markov (π : Meta → Policy S A)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (T k L : ℕ) (s₀ : S) : IsMarkovKernel (physicalBlock (M := M) π hπ T k L s₀) := by
  unfold physicalBlock
  infer_instance

def localBlock (π : Meta → Policy S A)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (SourceReplay.History Meta S A T) Meta)
    (s₀ : S) (k L : ℕ) :
    ProbabilityTheory.Kernel (Ctx M Meta S A T k × Stack (S × A) S (L+T))
      (Ctx M Meta S A T (k+1) × Stack (S × A) S L) :=
  (ProbabilityTheory.Kernel.id ×ₖ plannedKernel (plannerAt planner k) (physicalBlock π hπ T k L s₀)).map
    (fun z => (appendCtx T k z.1.1 (z.2.1,z.2.2.1),z.2.2.2))

lemma measurable_localOutput (T k L : ℕ) : Measurable
    (fun z : (Ctx M Meta S A T k × Stack (S × A) S (L+T)) × (Meta × (Trajectory S A T × Stack (S × A) S L)) =>
      (appendCtx T k z.1.1 (z.2.1,z.2.2.1),z.2.2.2)) :=
  ((measurable_appendCtx T k).comp (measurable_fst.fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.fst))).prodMk
    measurable_snd.snd.snd

instance localBlock_markov (π : Meta → Policy S A)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (SourceReplay.History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (k L : ℕ) : IsMarkovKernel (localBlock (M := M) π hπ planner s₀ k L) := by
  unfold localBlock
  exact Kernel.IsMarkovKernel.map _ (measurable_localOutput T k L)

def trueTrajectory (π : Meta → Policy S A) (P : M → S × A → Law S)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) (T k : ℕ) (s₀ : S) :
    ProbabilityTheory.Kernel (Ctx M Meta S A T k × Meta) (Trajectory S A T) :=
  trajectoryKernel (fun z : Ctx M Meta S A T k × Meta => π z.2)
    (fun z : Ctx M Meta S A T k × Meta => fun s a => P z.1.1 (s,a))
    (fun h s a => (hπ h s a).comp measurable_snd)
    (fun s a t => (hP (s,a) t).comp measurable_fst.fst) T s₀

instance trueTrajectory_markov (π : Meta → Policy S A) (P : M → S × A → Law S)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) (T k : ℕ) (s₀ : S) :
    IsMarkovKernel (trueTrajectory (Meta := Meta) π P hπ hP T k s₀) := by
  unfold trueTrajectory
  infer_instance

def onlineNext (π : Meta → Policy S A) (P : M → S × A → Law S)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (planner : ProbabilityTheory.Kernel (SourceReplay.History Meta S A T) Meta)
    (s₀ : S) (k : ℕ) : ProbabilityTheory.Kernel (Ctx M Meta S A T k) (Ctx M Meta S A T (k+1)) :=
  (ProbabilityTheory.Kernel.id ×ₖ (plannerAt planner k ⊗ₖ trueTrajectory π P hπ hP T k s₀)).map
    (fun z => appendCtx T k z.1 z.2)

instance onlineNext_markov (π : Meta → Policy S A) (P : M → S × A → Law S)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (planner : ProbabilityTheory.Kernel (SourceReplay.History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (k : ℕ) : IsMarkovKernel (onlineNext π P hπ hP planner s₀ k) := by
  unfold onlineNext
  exact Kernel.IsMarkovKernel.map _ (measurable_appendCtx T k)

/-- The local physical average uses the exact true transition rows at the
retained latent model; planner metadata can have any measurable type. -/
lemma averaged_physicalBlock (π : Meta → Policy S A) (P : M → S × A → Law S)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) (T k L : ℕ) (s₀ : S) :
    ((freshCtx (Meta := Meta) P hP T k (L+T)).comap Prod.fst measurable_fst ⊗ₖ physicalBlock π hπ T k L s₀).map Prod.snd =
      trueTrajectory π P hπ hP T k s₀ ×ₖ (freshCtx P hP T k L).comap Prod.fst measurable_fst := by
  exact SourceBlockKernel.averaged_blockKernel
    (fun z : Ctx M Meta S A T k × Meta => π z.2)
    (fun z : Ctx M Meta S A T k × Meta => fun s a => P z.1.1 (s,a))
    (fun h s a => (hπ h s a).comp measurable_snd)
    (fun s a t => (hP (s,a) t).comp measurable_fst.fst) L T s₀

lemma localBlock_lintegral (π : Meta → Policy S A)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (SourceReplay.History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (k L : ℕ) (f : Ctx M Meta S A T (k+1) × Stack (S × A) S L → ℝ≥0∞) (hf : Measurable f)
    (x : Ctx M Meta S A T k × Stack (S × A) S (L+T)) :
    (∫⁻ o, f o ∂localBlock π hπ planner s₀ k L x) =
      ∫⁻ o, f (appendCtx T k x.1 (o.1,o.2.1),o.2.2)
        ∂plannedKernel (plannerAt planner k) (physicalBlock π hπ T k L s₀) x := by
  unfold localBlock
  rw [Kernel.lintegral_map _ (measurable_localOutput T k L) _ hf]
  have hm : Measurable (fun z : (Ctx M Meta S A T k × Stack (S × A) S (L+T)) × (Meta × (Trajectory S A T × Stack (S × A) S L)) =>
      f (appendCtx T k z.1.1 (z.2.1,z.2.2.1),z.2.2.2)) := hf.comp (measurable_localOutput T k L)
  rw [Kernel.id,Kernel.lintegral_deterministic_prod measurable_id _ _ hm]
  rfl

lemma onlineNext_lintegral (π : Meta → Policy S A) (P : M → S × A → Law S)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (planner : ProbabilityTheory.Kernel (SourceReplay.History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (k : ℕ) (f : Ctx M Meta S A T (k+1) → ℝ≥0∞) (hf : Measurable f) (x : Ctx M Meta S A T k) :
    (∫⁻ o, f o ∂onlineNext π P hπ hP planner s₀ k x) =
      ∫⁻ m, ∫⁻ path, f (appendCtx T k x (m,path)) ∂trueTrajectory π P hπ hP T k s₀ (x,m)
        ∂plannerAt planner k x := by
  unfold onlineNext
  rw [Kernel.lintegral_map _ (measurable_appendCtx T k) _ hf]
  have hm : Measurable (fun z : Ctx M Meta S A T k × (Meta × Trajectory S A T) => f (appendCtx T k z.1 z.2)) :=
    hf.comp (measurable_appendCtx T k)
  rw [Kernel.id,Kernel.lintegral_deterministic_prod measurable_id _ _ hm]
  have hg : Measurable (fun z : Meta × Trajectory S A T => f (appendCtx T k x z)) :=
    hm.comp measurable_prodMk_left
  exact Kernel.lintegral_compProd _ _ _ hg

/-- The actual one-episode local factorization. After the arbitrary posterior/
planner choice and real episode, the appended observed history has its true
online law and every unconsumed original row is independently fresh. -/
theorem local_factorization (π : Meta → Policy S A) (P : M → S × A → Law S)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (planner : ProbabilityTheory.Kernel (SourceReplay.History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (k L : ℕ) :
    (freshCtx P hP T k (L+T) ⊗ₖ localBlock π hπ planner s₀ k L).map Prod.snd =
      onlineNext π P hπ hP planner s₀ k ⊗ₖ
        (freshCtx P hP T (k+1) L).prodMkLeft (Ctx M Meta S A T k) := by
  have hplan := averaged_plannedKernel (freshCtx P hP T k (L+T)) (plannerAt planner k)
    (physicalBlock π hπ T k L s₀)
    (trueTrajectory π P hπ hP T k s₀ ×ₖ (freshCtx P hP T k L).comap Prod.fst measurable_fst)
    (averaged_physicalBlock π P hπ hP T k L s₀)
  ext x : 1
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  have hfs : Measurable (fun z : Stack (S × A) S (L+T) × (Ctx M Meta S A T (k+1) × Stack (S × A) S L) => f z.2) :=
    hf.comp measurable_snd
  have ha : Measurable (fun o : Meta × (Trajectory S A T × Stack (S × A) S L) =>
      f (appendCtx T k x (o.1,o.2.1),o.2.2)) := by
    apply hf.comp
    exact ((measurable_appendCtx T k).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd.fst))).prodMk measurable_snd.snd
  have he := congrArg (fun κ : ProbabilityTheory.Kernel (Ctx M Meta S A T k) (Meta × (Trajectory S A T × Stack (S × A) S L)) =>
    ∫⁻ o, f (appendCtx T k x (o.1,o.2.1),o.2.2) ∂κ x) hplan
  dsimp only at he
  have has : Measurable (fun z : Stack (S × A) S (L+T) × (Meta × (Trajectory S A T × Stack (S × A) S L)) =>
      f (appendCtx T k x (z.2.1,z.2.2.1),z.2.2.2)) := ha.comp measurable_snd
  rw [Kernel.lintegral_map _ measurable_snd _ ha,Kernel.lintegral_compProd _ _ _ has,
    Kernel.lintegral_compProd _ _ _ ha] at he
  rw [Kernel.lintegral_map _ measurable_snd _ hf,Kernel.lintegral_compProd _ _ _ hfs]
  simp_rw [localBlock_lintegral π hπ planner s₀ k L f hf]
  rw [he,Kernel.lintegral_compProd _ _ _ hf]
  have hnext : Measurable (fun c : Ctx M Meta S A T (k+1) =>
      ∫⁻ r, f (c,r) ∂freshCtx P hP T (k+1) L c) := hf.lintegral_kernel_prod_right'
  change _ = ∫⁻ c, (∫⁻ r, f (c,r) ∂freshCtx P hP T (k+1) L c) ∂onlineNext π P hπ hP planner s₀ k x
  rw [onlineNext_lintegral π P hπ hP planner s₀ k _ hnext]
  apply lintegral_congr_ae
  apply ae_of_all
  intro m
  dsimp only
  have hm : Measurable (fun z : Trajectory S A T × Stack (S × A) S L => f (appendCtx T k x (m,z.1),z.2)) :=
    ha.comp (measurable_const.prodMk measurable_id)
  rw [Kernel.lintegral_prod _ _ _ hm]
  rfl


end
end Paper36.SourcePlanBlock
