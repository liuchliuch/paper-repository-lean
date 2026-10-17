import Paper36.AdaptiveKernelLaw

/-! The general adaptive execution run on one original infinite row tape.
Projection to the finite window used by the run is proved to have its product
law; the original infinite tape marginal survives every learner execution. -/
namespace Paper36.AdaptiveKernel
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes

variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

def fullPrefix (n : ℕ) (tape : Row × ℕ → S) : Stack Row S n :=
  fun c => tape (c.1,c.2.val)

lemma measurable_fullPrefix (n : ℕ) : Measurable (fullPrefix (Row := Row) (S := S) n) := by
  apply measurable_pi_lambda
  intro c
  exact measurable_pi_apply _

theorem fullPrefix_law (P : Row → Law S) (n : ℕ) :
    (InfiniteTapes.infiniteLaw (fun c : Row × ℕ => P c.1)).map (fullPrefix n) =
      lawMeasure (stackLaw P n) := by
  let e : Row × Fin n ↪ Row × ℕ := ⟨fun c => (c.1,c.2.val), by
    intro i j hij
    apply Prod.ext
    · exact congrArg (fun c : Row × ℕ => c.1) hij
    · exact Fin.ext (congrArg (fun c : Row × ℕ => c.2) hij)⟩
  exact InfiniteTapes.infinite_projection (fun c : Row × ℕ => P c.1) e

/-- The real execution law retains the complete original infinite tapes. -/
def infiniteExecution (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update) (L n : ℕ) (h : Hist) :
    Measure ((Row × ℕ → S) × (Hist × Stack Row S L)) :=
  InfiniteTapes.infiniteLaw (fun c : Row × ℕ => P c.1) ⊗ₘ
    (residualKernel choose update hupdate L n).comap (fun tape => (h,fullPrefix (L+n) tape))
      (measurable_const.prodMk (measurable_fullPrefix _))

instance infiniteExecution_probability (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L n : ℕ) (h : Hist) : IsProbabilityMeasure (infiniteExecution P choose update hupdate L n h) := by
  unfold infiniteExecution
  infer_instance

theorem infiniteExecution_tape (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L n : ℕ) (h : Hist) :
    (infiniteExecution P choose update hupdate L n h).map Prod.fst =
      InfiniteTapes.infiniteLaw (fun c : Row × ℕ => P c.1) := Measure.fst_compProd _ _

/-- Actual execution on infinite tapes has exactly the online history law and
independent, untouched residual rows. The result holds for every finite run. -/
theorem infiniteExecution_joint (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsMarkovKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L n : ℕ) (h : Hist) :
    (infiniteExecution P choose update hupdate L n h).map Prod.snd =
      (onlineKernel P choose update n h).prod (lawMeasure (stackLaw P L)) := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  have hfs : Measurable (fun z : (Row × ℕ → S) × (Hist × Stack Row S L) => f z.2) := hf.comp measurable_snd
  have hr : Measurable (fun tape : Stack Row S (L+n) => residualLValue choose update L f n h tape) :=
    (measurable_residualLValue choose update hupdate L f hf n).comp (measurable_const.prodMk measurable_id)
  calc
    _ = ∫⁻ z, f z.2 ∂infiniteExecution P choose update hupdate L n h := lintegral_map hf measurable_snd
    _ = ∫⁻ tape, residualLValue choose update L f n h (fullPrefix (L+n) tape)
        ∂InfiniteTapes.infiniteLaw (fun c : Row × ℕ => P c.1) := by
      rw [infiniteExecution, Measure.lintegral_compProd hfs]
      simp only [Kernel.comap_apply, residualKernel_lintegral choose update hupdate L f hf]
    _ = ∫⁻ tape, residualLValue choose update L f n h tape ∂lawMeasure (stackLaw P (L+n)) := by
      rw [← fullPrefix_law P (L+n), lintegral_map hr (measurable_fullPrefix _)]
    _ = onlineLValue P choose update (fun h => ∫⁻ tape, f (h,tape) ∂lawMeasure (stackLaw P L)) n h :=
      adaptive_kernel_unused_independent P choose update hupdate L f hf n h
    _ = _ := by
      rw [lintegral_prod f hf.aemeasurable,
        onlineKernel_lintegral P choose update hupdate _ hf.lintegral_prod_right']

end
end Paper36.AdaptiveKernel

namespace Paper36.InfiniteTapes
noncomputable section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
variable {M Row S Aux : Type*} [MeasurableSpace M] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace Aux]

/-- Every actual learner execution is a Markov extension of the original tapes.
Its addition preserves the iid prefix law given the latent model, including all
prefix lengths that have not yet been read. -/
theorem priorTapes_prefix_after_extension
    (ν : Measure M) [IsProbabilityMeasure ν] (P : M → Row → Law S)
    (hP : ∀ r s, Measurable (fun m => (P m r).mass s))
    (κ : ProbabilityTheory.Kernel (M × (Row × ℕ → S)) Aux) [IsMarkovKernel κ]
    (r : Row) (n : ℕ) :
    condDistrib (fun x : (M × (Row × ℕ → S)) × Aux => tapePrefix r n x.1.2)
      (fun x => x.1.1) (priorTapes ν P hP ⊗ₘ κ) =ᵐ[ν]
        Paper36.RowTapes.iidKernel (fun m => P m r) (hP r) n := by
  let ρ := priorTapes ν P hP ⊗ₘ κ
  have hfst : ρ.map Prod.fst = priorTapes ν P hP := Measure.fst_compProd _ _
  have hlatent : ρ.map (fun x => x.1.1) = ν := by
    change ρ.map (Prod.fst ∘ Prod.fst) = ν
    rw [← Measure.map_map measurable_fst measurable_fst, hfst, priorTapes_latent_law]
  have hc := condDistrib_map (ν := ρ) (f := Prod.fst)
    (X := Prod.fst) (Y := fun x : M × (Row × ℕ → S) => tapePrefix r n x.2)
    measurable_fst.aemeasurable ((measurable_prefix r n).comp measurable_snd).aemeasurable measurable_fst.aemeasurable
  have hc' : condDistrib (fun x : M × (Row × ℕ → S) => tapePrefix r n x.2) Prod.fst (priorTapes ν P hP)
      =ᵐ[ν] condDistrib (fun x : (M × (Row × ℕ → S)) × Aux => tapePrefix r n x.1.2)
        (fun x => x.1.1) ρ := by
    simpa only [hfst, Function.comp_def, hlatent] using hc
  exact hc'.symm.trans (priorTapes_prefix_condDistrib ν P hP r n)

end
end Paper36.InfiniteTapes
