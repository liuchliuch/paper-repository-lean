import Paper36.SourcePlanBlock
import Paper36.SourceSummary
import Paper36.SourceFresh

/-! The concrete conditional physical dynamics are recovered from the proved
online law of the complete indexed observed history. Current metadata and the
actual new path are retained by the history append; no physical-law premise is
used in the final source specialization. -/
namespace Paper36.SourceNativeConditional
noncomputable section
open scoped ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay Paper36.SourcePlanBlock

section Transport
variable {H I Y : Type*} [MeasurableSpace H] [MeasurableSpace I] [MeasurableSpace Y]

lemma compProd_summary (ν : Measure H) [SFinite ν] (summary : H → I) (hs : Measurable summary)
    (κ : ProbabilityTheory.Kernel I Y) [IsMarkovKernel κ] :
    (ν ⊗ₘ κ.comap summary hs).map (fun z => (summary z.1,z.2)) = ν.map summary ⊗ₘ κ := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  have hfs : Measurable (fun z : H × Y => f (summary z.1,z.2)) :=
    hf.comp ((hs.comp measurable_fst).prodMk measurable_snd)
  have hi : Measurable (fun i => ∫⁻ y, f (i,y) ∂κ i) := hf.lintegral_kernel_prod_right'
  rw [lintegral_map hf (by fun_prop),Measure.lintegral_compProd hfs,
    Measure.lintegral_compProd hf,lintegral_map hi hs]
  rfl

end Transport

universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta]

def priorCtx (T k : ℕ) (x : Ctx M Meta S A T (k+1)) : Ctx M Meta S A T k :=
  (x.1,((fun i => x.2.1 i.castSucc),(fun i => x.2.2 i.castSucc)))

def lastRecord (T k : ℕ) (x : Ctx M Meta S A T (k+1)) : Meta × Trajectory S A T :=
  (x.2.1 (Fin.last k),x.2.2 (Fin.last k))

def splitCtx (T k : ℕ) (x : Ctx M Meta S A T (k+1)) : Ctx M Meta S A T k × (Meta × Trajectory S A T) :=
  (priorCtx T k x,lastRecord T k x)

lemma measurable_splitCtx (T k : ℕ) : Measurable (splitCtx (M := M) (Meta := Meta) (S := S) (A := A) T k) := by
  apply Measurable.prodMk
  · apply measurable_fst.prodMk
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ fun i => (measurable_pi_apply i.castSucc).comp measurable_snd.fst
    · exact measurable_pi_lambda _ fun i => (measurable_pi_apply i.castSucc).comp measurable_snd.snd
  · exact ((measurable_pi_apply _).comp measurable_snd.fst).prodMk
      ((measurable_pi_apply _).comp measurable_snd.snd)

@[simp] theorem splitCtx_append (T k : ℕ) (x : Ctx M Meta S A T k) (z : Meta × Trajectory S A T) :
    splitCtx T k (appendCtx T k x z) = (x,z) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext <;> funext i <;> simp [splitCtx,priorCtx,appendCtx,SourceHistory.append]
  · simp [splitCtx,lastRecord,appendCtx,SourceHistory.append]

lemma onlineNext_split (π : Meta → Policy S A) (P : M → S × A → Law S)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (k : ℕ) :
    (onlineNext π P hπ hP planner s₀ k).map (splitCtx T k) =
      ProbabilityTheory.Kernel.id ×ₖ (plannerAt planner k ⊗ₖ trueTrajectory π P hπ hP T k s₀) := by
  ext x : 1
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  have hfc : Measurable (fun y : Ctx M Meta S A T (k+1) => f (splitCtx T k y)) := hf.comp (measurable_splitCtx T k)
  rw [Kernel.lintegral_map _ (measurable_splitCtx T k) _ hf,
    onlineNext_lintegral π P hπ hP planner s₀ k _ hfc]
  simp_rw [splitCtx_append]
  rw [Kernel.lintegral_id_prod hf]
  have hm : Measurable (fun z : Meta × Trajectory S A T => f (x,z)) := hf.comp measurable_prodMk_left
  exact (Kernel.lintegral_compProd _ _ _ hm).symm

/-- The actual source context: true model and every actually observed metadata/path. -/
def actualCtx (T k : ℕ) (s₀ : S) (ω : SourceProtocol.Sample M Meta S A T) : Ctx M Meta S A T k :=
  SourceSummary.context T k s₀ (ω.1,fun i => ω.2 i.val)

lemma measurable_actualCtx (T k : ℕ) (s₀ : S) :
    Measurable (actualCtx (M := M) (Meta := Meta) (S := S) (A := A) T k s₀) :=
  (SourceSummary.measurable_context T k s₀).comp
    (measurable_fst.prodMk (measurable_pi_lambda _ fun i => measurable_snd.eval))

lemma actualCtx_formula (T k : ℕ) (s₀ : S) (ω : SourceProtocol.Sample M Meta S A T) :
    actualCtx T k s₀ ω = (ω.1.1,((fun i : Fin k => (ω.2 i.val).1),
      (fun i : Fin k => SourceProtocol.path s₀ T i.val ω))) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact finitePaths_eq_episodePath _ s₀ ω.2 k

lemma split_actualCtx (T k : ℕ) (s₀ : S) (ω : SourceProtocol.Sample M Meta S A T) :
    splitCtx T k (actualCtx T (k+1) s₀ ω) =
      (actualCtx T k s₀ ω,((ω.2 k).1,SourceProtocol.path s₀ T k ω)) := by
  rw [actualCtx_formula,actualCtx_formula]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext <;> funext i <;> rfl
  · rfl

abbrev AnalystInfo (M Meta : Type*) (S A : Type u) (T : ℕ) := (M × History Meta S A T) × Meta

def analystOf (T k : ℕ) (z : Ctx M Meta S A T k × Meta) : AnalystInfo M Meta S A T :=
  ((z.1.1,⟨k,z.1.2⟩),z.2)

lemma measurable_analystOf (T k : ℕ) : Measurable (analystOf (M := M) (Meta := Meta) (S := S) (A := A) T k) :=
  (measurable_fst.fst.prodMk ((SourceReplay.measurable_history_mk k).comp measurable_fst.snd)).prodMk measurable_snd

def actualInfo (T k : ℕ) (s₀ : S) (ω : SourceProtocol.Sample M Meta S A T) : AnalystInfo M Meta S A T :=
  ((ω.1.1,SourceProtocol.history s₀ T k ω),(ω.2 k).1)

lemma actualInfo_eq (T k : ℕ) (s₀ : S) (ω : SourceProtocol.Sample M Meta S A T) :
    analystOf T k (actualCtx T k s₀ ω,(ω.2 k).1) = actualInfo T k s₀ ω := rfl

lemma measurable_actualInfo (T k : ℕ) (s₀ : S) :
    Measurable (actualInfo (M := M) (Meta := Meta) (S := S) (A := A) T k s₀) :=
  (measurable_fst.fst.prodMk (SourceProtocol.measurable_history s₀ T k)).prodMk
    ((measurable_pi_apply k).comp measurable_snd).fst

def trueInfoTrajectory (π : Meta → Policy S A) (P : M → S × A → Law S)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) (T : ℕ) (s₀ : S) :
    ProbabilityTheory.Kernel (AnalystInfo M Meta S A T) (Trajectory S A T) :=
  trajectoryKernel (fun i : AnalystInfo M Meta S A T => π i.2)
    (fun i : AnalystInfo M Meta S A T => fun s a => P i.1.1 (s,a))
    (fun h s a => (hπ h s a).comp measurable_snd)
    (fun s a t => (hP (s,a) t).comp measurable_fst.fst) T s₀

instance trueInfoTrajectory_markov (π : Meta → Policy S A) (P : M → S × A → Law S)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s)) (T : ℕ) (s₀ : S) :
    IsMarkovKernel (trueInfoTrajectory π P hπ hP T s₀) := by unfold trueInfoTrajectory; infer_instance

/-- Recover the native physical conditional law from the proved one-step law of
complete actual contexts. This is an internal bridge used by the final source
construction, not a replacement physical-law assumption. -/
theorem physical_from_context_succ (μ : Measure (SourceProtocol.Sample M Meta S A T)) [IsProbabilityMeasure μ]
    (π : Meta → Policy S A) (P : M → S × A → Law S)
    (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (k : ℕ)
    (hctx : μ.map (actualCtx T (k+1) s₀) = onlineNext π P hπ hP planner s₀ k ∘ₘ μ.map (actualCtx T k s₀)) :
    condDistrib (SourceProtocol.path (M := M) (Meta := Meta) s₀ T k) (actualInfo T k s₀) μ
      =ᵐ[μ.map (actualInfo T k s₀)] trueInfoTrajectory π P hπ hP T s₀ := by
  have hsplit : μ.map (fun ω => (actualCtx T k s₀ ω,((ω.2 k).1,SourceProtocol.path s₀ T k ω))) =
      μ.map (actualCtx T k s₀) ⊗ₘ (plannerAt planner k ⊗ₖ trueTrajectory π P hπ hP T k s₀) := by
    calc
      _ = (μ.map (actualCtx T (k+1) s₀)).map (splitCtx T k) := by
        rw [Measure.map_map (measurable_splitCtx T k) (measurable_actualCtx T (k+1) s₀)]
        congr 1
        funext ω
        exact (split_actualCtx T k s₀ ω).symm
      _ = _ := by
        rw [hctx,Measure.map_comp _ _ (measurable_splitCtx T k),onlineNext_split,
          ← Measure.compProd_eq_comp_prod]
  let before : SourceProtocol.Sample M Meta S A T → Ctx M Meta S A T k × Meta :=
    fun ω => (actualCtx T k s₀ ω,(ω.2 k).1)
  have hb : Measurable before := (measurable_actualCtx T k s₀).prodMk (((measurable_pi_apply k).comp measurable_snd).fst)
  have hjoint : μ.map (fun ω => (before ω,SourceProtocol.path s₀ T k ω)) =
      (μ.map (actualCtx T k s₀) ⊗ₘ plannerAt planner k) ⊗ₘ trueTrajectory π P hπ hP T k s₀ := by
    calc
      _ = (μ.map (fun ω => (actualCtx T k s₀ ω,((ω.2 k).1,SourceProtocol.path s₀ T k ω)))).map MeasurableEquiv.prodAssoc.symm := by
        have hpre : Measurable (fun ω : SourceProtocol.Sample M Meta S A T =>
            (actualCtx T k s₀ ω,((ω.2 k).1,SourceProtocol.path s₀ T k ω))) :=
          (measurable_actualCtx T k s₀).prodMk
            ((((measurable_pi_apply k).comp measurable_snd).fst).prodMk (SourceProtocol.measurable_path s₀ T k))
        have hAssoc : Measurable (MeasurableEquiv.prodAssoc.symm :
            Ctx M Meta S A T k × (Meta × Trajectory S A T) → (Ctx M Meta S A T k × Meta) × Trajectory S A T) := by fun_prop
        rw [Measure.map_map hAssoc hpre]
        rfl
      _ = _ := by rw [hsplit,Measure.compProd_assoc]
  have hbefore : μ.map before = μ.map (actualCtx T k s₀) ⊗ₘ plannerAt planner k := by
    have he := congrArg (fun ν : Measure ((Ctx M Meta S A T k × Meta) × Trajectory S A T) => ν.map Prod.fst) hjoint
    have hr : (μ.map (actualCtx T k s₀) ⊗ₘ plannerAt planner k ⊗ₘ trueTrajectory π P hπ hP T k s₀).map Prod.fst =
        μ.map (actualCtx T k s₀) ⊗ₘ plannerAt planner k := Measure.fst_compProd _ _
    dsimp only at he
    rw [hr] at he
    simpa only [Measure.map_map measurable_fst (hb.prodMk (SourceProtocol.measurable_path s₀ T k)),Function.comp_def] using he
  have hjoint' : μ.map (fun ω => (before ω,SourceProtocol.path s₀ T k ω)) =
      μ.map before ⊗ₘ (trueInfoTrajectory π P hπ hP T s₀).comap (analystOf T k) (measurable_analystOf T k) := by
    rw [hbefore]
    exact hjoint
  have hcoarse := congrArg (fun ν : Measure ((Ctx M Meta S A T k × Meta) × Trajectory S A T) =>
      ν.map (fun z => (analystOf T k z.1,z.2))) hjoint'
  dsimp only at hcoarse
  rw [compProd_summary] at hcoarse
  have hc : μ.map (fun ω => (actualInfo T k s₀ ω,SourceProtocol.path s₀ T k ω)) =
      μ.map (actualInfo T k s₀) ⊗ₘ trueInfoTrajectory π P hπ hP T s₀ := by
    have hs : Measurable (fun z : (Ctx M Meta S A T k × Meta) × Trajectory S A T => (analystOf T k z.1,z.2)) :=
      ((measurable_analystOf T k).comp measurable_fst).prodMk measurable_snd
    rw [Measure.map_map hs (hb.prodMk (SourceProtocol.measurable_path s₀ T k)),
      Measure.map_map (measurable_analystOf T k) hb] at hcoarse
    simpa only [Function.comp_def,before,actualInfo_eq] using hcoarse
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (measurable_actualInfo T k s₀) (SourceProtocol.measurable_path s₀ T k) hc

/-- The concrete original source protocol has the physical Markov trajectory
conditional law. This final theorem has no freshness, coupling, count,
occupation, or physical-law hypothesis. The arbitrary prior and learner kernel
are the actual inputs of the constructed one-experiment protocol. -/
theorem actual_physicalLaw [MeasurableSingletonClass M]
    (ν : Measure M) [IsProbabilityMeasure ν]
    (P : M → S × A → Law S) (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (dummy : Draw Meta A T) (k : ℕ) :
    condDistrib (SourceProtocol.path (M := M) (Meta := Meta) s₀ T k) (actualInfo T k s₀)
      (SourceProtocol.measure ν P hP π hπ planner s₀ dummy) =ᵐ[
        (SourceProtocol.measure ν P hP π hπ planner s₀ dummy).map (actualInfo T k s₀)]
      trueInfoTrajectory π P hπ hP T s₀ := by
  apply physical_from_context_succ _ π P hπ hP planner s₀ k
  exact SourceFresh.actual_context_succ ν P hP π hπ planner s₀ dummy k


end
end Paper36.SourceNativeConditional
