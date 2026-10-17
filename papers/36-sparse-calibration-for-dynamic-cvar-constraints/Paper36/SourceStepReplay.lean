import Paper36.SourceSummary
import Paper36.SourcePlanBlock

/-! The finite source step and the local joint episode/unused-row kernel are
proved to be the same execution on the same original raw tape. -/
namespace Paper36.SourceStepReplay
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

/-- Every local block reads exactly the original raw coordinates consumed by
one step of the actual infinite source protocol. -/
theorem step_summary
    (π : Meta → Policy S A) (hπ : ∀ h s a, Measurable (fun m => (π m h s).mass a))
    (planner : ProbabilityTheory.Kernel (History Meta S A T) Meta) [IsMarkovKernel planner]
    (s₀ : S) (k L : ℕ) (x : Input M Meta S A T k) :
    (SourceMarginals.stepDraw (protocolKernel π hπ planner s₀) k x).map (summary T (k+1) L s₀) =
      SourcePlanBlock.localBlock π hπ planner s₀ k L (summary T k (L+T) s₀ x) := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  have hsum := measurable_summary (M := M) (Meta := Meta) (S := S) (A := A) T (k+1) L s₀
  have happ := SourceMarginals.measurable_appendDraw (Base := M × ((S×A)×ℕ→S))
    (D := Draw Meta A T) k
  have houter : Measurable (fun z : Input M Meta S A T k × Draw Meta A T =>
      f (summary T (k+1) L s₀ (SourceMarginals.appendDraw k z))) :=
    (hf.comp hsum).comp happ
  rw [lintegral_map hf hsum]
  have hleft : (∫⁻ y, f (summary T (k+1) L s₀ y)
      ∂SourceMarginals.stepDraw (protocolKernel π hπ planner s₀) k x) =
      ∫⁻ d, f (summary T (k+1) L s₀ (SourceMarginals.appendDraw k (x,d)))
        ∂protocolKernel π hπ planner s₀ k x := by
    change (∫⁻ y, (f ∘ summary T (k+1) L s₀) y
      ∂(Kernel.id ×ₖ protocolKernel π hπ planner s₀ k).map (SourceMarginals.appendDraw k) x) = _
    calc
      _ = ∫⁻ z, f (summary T (k+1) L s₀ (SourceMarginals.appendDraw k z))
          ∂(Kernel.id ×ₖ protocolKernel π hπ planner s₀ k) x :=
        Kernel.lintegral_map _ happ _ (hf.comp hsum)
      _ = _ := Kernel.lintegral_id_prod houter _ x
  rw [hleft]
  have hright : (∫⁻ o, f o ∂SourcePlanBlock.localBlock π hπ planner s₀ k L
      (summary T k (L+T) s₀ x)) =
      ∫⁻ v, f (SourcePlanBlock.appendCtx T k (context T k s₀ x) (v.1,v.2.1),v.2.2)
        ∂SourcePlanBlock.plannedKernel (SourcePlanBlock.plannerAt planner k)
          (SourcePlanBlock.physicalBlock π hπ T k L s₀) (summary T k (L+T) s₀ x) := by
    let out := fun z : (SourcePlanBlock.Ctx M Meta S A T k × Stack (S×A) S (L+T)) ×
        (Meta × (Trajectory S A T × Stack (S×A) S L)) =>
      (SourcePlanBlock.appendCtx T k z.1.1 (z.2.1,z.2.2.1),z.2.2.2)
    have hout : Measurable out := SourcePlanBlock.measurable_localOutput T k L
    change (∫⁻ o, f o ∂(Kernel.id ×ₖ SourcePlanBlock.plannedKernel (SourcePlanBlock.plannerAt planner k)
      (SourcePlanBlock.physicalBlock π hπ T k L s₀)).map out (summary T k (L+T) s₀ x)) = _
    calc
      _ = ∫⁻ z, f (out z) ∂(Kernel.id ×ₖ SourcePlanBlock.plannedKernel (SourcePlanBlock.plannerAt planner k)
          (SourcePlanBlock.physicalBlock π hπ T k L s₀)) (summary T k (L+T) s₀ x) :=
        Kernel.lintegral_map _ hout _ hf
      _ = _ := Kernel.lintegral_id_prod (hf.comp hout) _ _
  rw [hright]
  have hl : (∫⁻ d, f (summary T (k+1) L s₀ (SourceMarginals.appendDraw k (x,d)))
      ∂protocolKernel π hπ planner s₀ k x) =
      ∫⁻ choice, ∫⁻ actions,
        f (summary T (k+1) L s₀ (SourceMarginals.appendDraw k (x,(choice,actions))))
          ∂lawMeasure (actionLaw (π choice) T s₀ (nextWindow T k s₀ x))
          ∂planner (past T k s₀ x) := by
    exact Kernel.lintegral_compProd _ _ x (houter.comp (measurable_const.prodMk measurable_id))
  have hr : (∫⁻ v, f (SourcePlanBlock.appendCtx T k (context T k s₀ x) (v.1,v.2.1),v.2.2)
      ∂SourcePlanBlock.plannedKernel (SourcePlanBlock.plannerAt planner k)
        (SourcePlanBlock.physicalBlock π hπ T k L s₀) (summary T k (L+T) s₀ x)) =
      ∫⁻ choice, ∫⁻ z,
        f (SourcePlanBlock.appendCtx T k (context T k s₀ x) (choice,z.1),z.2)
          ∂lawMeasure (SourceBlocks.blockLaw (π choice) L T 0 s₀ (summary T k (L+T) s₀ x).2)
          ∂planner (past T k s₀ x) := by
    have hv : Measurable (fun v : Meta × (Trajectory S A T × Stack (S×A) S L) =>
        f (SourcePlanBlock.appendCtx T k (context T k s₀ x) (v.1,v.2.1),v.2.2)) :=
      (hf.comp (SourcePlanBlock.measurable_localOutput T k L)).comp
        ((measurable_const : Measurable (fun _ : Meta × (Trajectory S A T × Stack (S×A) S L) =>
          summary T k (L+T) s₀ x)).prodMk measurable_id)
    exact Kernel.lintegral_compProd _ _ _ hv
  rw [hl,hr]
  apply lintegral_congr_ae
  apply ae_of_all
  intro choice
  dsimp only
  simp_rw [summary_append]
  let g : Trajectory S A T × Stack (S × A) S L → ℝ≥0∞ :=
    fun z => f (SourcePlanBlock.appendCtx T k (context T k s₀ x) (choice,z.1),z.2)
  have hg : Measurable g := by
    apply hf.comp
    exact ((SourcePlanBlock.measurable_appendCtx T k).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_fst))).prodMk measurable_snd
  have hj := SourceBlockReplay.actionLaw_joint_replay (π choice) (fun row j => x.1.2 (row,j))
    (historyCount (past T k s₀ x)) L T s₀
  have he := congrArg (fun ρ => ∫⁻ z, g z ∂ρ) hj
  dsimp only at he
  rw [lintegral_map hg] at he
  · exact he
  · apply Measurable.prodMk
    · exact measurable_replayStep _ measurable_const T _ measurable_const _ measurable_const _ measurable_id
    · apply measurable_pi_lambda
      intro c
      exact Measurable.of_discrete
end
end Paper36.SourceStepReplay
