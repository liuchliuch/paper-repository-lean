import Paper36.FreshChoice
import Paper36.SourceBlocks
import Paper36.SourceReplay

/-! Actual source conditional trajectory laws from fresh unused rows and native
taped execution. These results derive the EpisodeSystem dynamics field from the
primitive sampling protocol, rather than assuming its occupancy conclusion. -/
namespace Paper36.SourceConditional
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceBlocks

universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]

def pointTest {X : Type*} (x : X) : X → ℝ := fun y => @ite ℝ (y=x) (Classical.propDecidable _) 1 0

lemma expect_indicator_point {X : Type*} [Fintype X] (P : Law X) (x : X) :
    expect P.mass (pointTest x) = P.mass x := by
  classical
  simp [expect, pointTest]

/-- The joint episode/unused-stack law is the actual averaged tape execution. -/
theorem averaged_blockLaw_eq (π : Policy S A) (p : Simulation.Kernel S A)
    (L T h : ℕ) (s₀ : S) :
    bindLaw (stackLaw (fun r : S × A => p r.1 r.2) (L+T)) (blockLaw π L T h s₀) =
      joint (trajectoryLaw π p T h s₀) (fun _ => stackLaw (fun r : S × A => p r.1 r.2) L) := by
  apply law_ext
  funext z
  have he := blockLaw_expect_average π p L T h s₀ (pointTest z)
  have he' : expect (bindLaw (stackLaw (fun r : S × A => p r.1 r.2) (L+T))
      (blockLaw π L T h s₀)).mass (pointTest z) =
      expect (joint (trajectoryLaw π p T h s₀)
        (fun _ => stackLaw (fun r : S × A => p r.1 r.2) L)).mass (pointTest z) := by
    simpa only [bindLaw_expect, expect_joint] using he
  exact (expect_indicator_point _ z).symm.trans (he'.trans (expect_indicator_point _ z))

section FiniteNative
variable {X Y : Type*} [Fintype X] [Fintype Y] [MeasurableSpace X] [MeasurableSpace Y]
  [DiscreteMeasurableSpace X] [DiscreteMeasurableSpace Y]

lemma lawMeasure_joint_compProd (P : Law X) (Q : X → Law Y)
    (κ : ProbabilityTheory.Kernel X Y) [IsMarkovKernel κ]
    (hκ : ∀ x, κ x = lawMeasure (Q x)) :
    lawMeasure (joint P Q) = lawMeasure P ⊗ₘ κ := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨x,y⟩
  have hs : ({(x,y)} : Set (X×Y)) = {x} ×ˢ {y} := by ext z; simp
  rw [lawMeasure_singleton, hs, Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _)]
  simp only [lintegral_singleton, hκ, lawMeasure_singleton, joint]
  rw [ENNReal.ofReal_mul (P.nonneg x)]
  exact mul_comm _ _

end FiniteNative

section NativeEpisode
variable {Info : Type*} [MeasurableSpace Info]

def tapedKernel (π : Info → Policy S A)
    (hπ : ∀ h s a, Measurable (fun i => (π i h s).mass a)) (T : ℕ) (s₀ : S) :
    ProbabilityTheory.Kernel (Info × Stack (S × A) S T) (Trajectory S A T) :=
  lawKernel (fun z => tapedTrajectory (π z.1) T 0 s₀ z.2) (fun path =>
    measurable_from_prod_countable_left (fun tape => measurable_tapedTrajectory_mass π hπ T 0 s₀ tape path))

instance tapedKernel_markov (π : Info → Policy S A)
    (hπ : ∀ h s a, Measurable (fun i => (π i h s).mass a)) (T : ℕ) (s₀ : S) :
    IsMarkovKernel (tapedKernel π hπ T s₀) := lawKernel_markov _ _

lemma kernel_compProd_at {I X Y : Type*} [MeasurableSpace I] [MeasurableSpace X] [MeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel I X) [IsSFiniteKernel κ]
    (η : ProbabilityTheory.Kernel (I × X) Y) [IsSFiniteKernel η] (i : I) :
    (κ ⊗ₖ η) i = κ i ⊗ₘ η.comap (fun x => (i,x)) (measurable_const.prodMk measurable_id) := by
  ext B hB
  rw [Kernel.compProd_apply hB, Measure.compProd_apply hB]
  rfl

/-- Fresh original rows followed by the algorithm's actual taped episode have
exactly the physical-state Markov trajectory law. -/
theorem averaged_tapedKernel (π : Info → Policy S A) (p : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (π i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (p i s a).mass t)) (T : ℕ) (s₀ : S) :
    (AdaptiveKernel.freshKernel (fun i => fun r : S × A => p i r.1 r.2) (fun r t => hp r.1 r.2 t) T ⊗ₖ
      tapedKernel π hπ T s₀).map Prod.snd = trajectoryKernel π p hπ hp T s₀ := by
  ext i : 1
  rw [Kernel.map_apply _ measurable_snd]
  have hj : (AdaptiveKernel.freshKernel (fun i => fun r : S × A => p i r.1 r.2) (fun r t => hp r.1 r.2 t) T ⊗ₖ
      tapedKernel π hπ T s₀) i = lawMeasure (tapedEpisodeLaw (π i) (p i) T 0 s₀) := by
    rw [kernel_compProd_at]
    symm
    apply lawMeasure_joint_compProd
    intro tape
    rfl
  rw [hj, tapedEpisodeLaw_trajectory]
  rfl

end NativeEpisode

section Hierarchical
variable {Ω Info Raw Out : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Raw] [StandardBorelSpace Raw] [Nonempty Raw]
  [MeasurableSpace Out] [StandardBorelSpace Out] [Nonempty Out]

/-- Two actual sampling stages compose their conditional kernels. The first
stage is the proved unused-row law; the second is the algorithm's native tape
execution. This derives the physical dynamics conditional law. -/
theorem conditional_two_stage (μ : Measure Ω) [IsProbabilityMeasure μ]
    (info : Ω → Info) (hinfo : Measurable info) (raw : Ω → Raw) (hraw : Measurable raw)
    (out : Ω → Out) (hout : Measurable out)
    (fresh : ProbabilityTheory.Kernel Info Raw) [IsMarkovKernel fresh]
    (execute : ProbabilityTheory.Kernel (Info × Raw) Out) [IsMarkovKernel execute]
    (hfresh : condDistrib raw info μ =ᵐ[μ.map info] fresh)
    (hexecute : condDistrib out (fun ω => (info ω,raw ω)) μ =ᵐ[μ.map (fun ω => (info ω,raw ω))] execute) :
    condDistrib out info μ =ᵐ[μ.map info] (fresh ⊗ₖ execute).map Prod.snd := by
  have hfirst := (condDistrib_ae_eq_iff_measure_eq_compProd info hraw.aemeasurable fresh).mp hfresh
  have hsecond := (condDistrib_ae_eq_iff_measure_eq_compProd (fun ω => (info ω,raw ω)) hout.aemeasurable execute).mp hexecute
  have hmap : μ.map (fun ω => (info ω,out ω)) =
      μ.map info ⊗ₘ (fresh ⊗ₖ execute).map Prod.snd := by
    calc
      _ = (μ.map (fun ω => ((info ω,raw ω),out ω))).map (fun z => (z.1.1,z.2)) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = ((μ.map info ⊗ₘ fresh) ⊗ₘ execute).map (fun z => (z.1.1,z.2)) := by rw [hsecond,hfirst]
      _ = _ := by
        rw [← Measure.compProd_assoc, Measure.map_map (by fun_prop) (by fun_prop),
          Measure.compProd_map measurable_snd]
        rfl
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hinfo hout hmap

end Hierarchical

section ActualConditional
variable [Nonempty S] [Nonempty A]
  {Ω Info : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]

/-- The actual EpisodeSystem dynamics field follows from the raw fresh-window
law and native tape execution. Neither occupation nor a trajectory-law conclusion
is an input. -/
theorem conditional_trajectory_from_fresh (μ : Measure Ω) [IsProbabilityMeasure μ]
    (π : Info → Policy S A) (p : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (π i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (p i s a).mass t)) (T : ℕ) (s₀ : S)
    (info : Ω → Info) (hinfo : Measurable info)
    (raw : Ω → Stack (S × A) S T) (hraw : Measurable raw)
    (path : Ω → Trajectory S A T) (hpath : Measurable path)
    (hfresh : condDistrib raw info μ =ᵐ[μ.map info]
      AdaptiveKernel.freshKernel (fun i => fun r : S × A => p i r.1 r.2) (fun r t => hp r.1 r.2 t) T)
    (hexecute : condDistrib path (fun ω => (info ω,raw ω)) μ =ᵐ[μ.map (fun ω => (info ω,raw ω))]
      tapedKernel π hπ T s₀) :
    condDistrib path info μ =ᵐ[μ.map info] trajectoryKernel π p hπ hp T s₀ := by
  have hc := conditional_two_stage μ info hinfo raw hraw path hpath _ _ hfresh hexecute
  simpa only [averaged_tapedKernel] using hc

end ActualConditional
end
end Paper36.SourceConditional
