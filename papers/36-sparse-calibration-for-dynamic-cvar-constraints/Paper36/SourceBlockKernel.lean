import Paper36.SourceConditional

/-! The complete physical block is a measurable kernel, and averaging its
original fresh input rows gives the true trajectory times the untouched rows. -/
namespace Paper36.SourceBlockKernel
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceBlocks
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Info : Type*} [MeasurableSpace Info]

lemma measurable_blockLaw_mass (π : Info → Policy S A)
    (hπ : ∀ h s a, Measurable (fun i => (π i h s).mass a))
    (L n h : ℕ) (s : S) (tape : Stack (S × A) S (L+n))
    (z : Trajectory S A n × Stack (S × A) S L) :
    Measurable (fun i => (blockLaw (π i) L n h s tape).mass z) := by
  induction n generalizing h s with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun i => ∑ a, (π i h s).mass a *
      ∑ v : Trajectory S A n × Stack (S × A) S L,
        (blockLaw (π i) L n (h+1) (head (s,a) tape) (remaining (s,a) tape)).mass v *
          (dirac ((s,a,v.1),v.2)).mass z)
    apply Finset.measurable_sum
    intro a _
    apply (hπ h s a).mul
    apply Finset.measurable_sum
    intro v _
    exact (ih (h+1) _ _ v).mul_const _

def blockKernel (π : Info → Policy S A)
    (hπ : ∀ h s a, Measurable (fun i => (π i h s).mass a)) (L T : ℕ) (s₀ : S) :
    ProbabilityTheory.Kernel (Info × Stack (S × A) S (L+T))
      (Trajectory S A T × Stack (S × A) S L) :=
  lawKernel (fun z => blockLaw (π z.1) L T 0 s₀ z.2) (fun out =>
    measurable_from_prod_countable_left fun tape => measurable_blockLaw_mass π hπ L T 0 s₀ tape out)

instance blockKernel_markov (π : Info → Policy S A)
    (hπ : ∀ h s a, Measurable (fun i => (π i h s).mass a)) (L T : ℕ) (s₀ : S) :
    IsMarkovKernel (blockKernel π hπ L T s₀) := lawKernel_markov _ _

/-- Local block factorization at arbitrary continuous information. The same
input tape generates both the physical episode and every remaining coordinate. -/
theorem averaged_blockKernel (π : Info → Policy S A) (p : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (π i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (p i s a).mass t)) (L T : ℕ) (s₀ : S) :
    (AdaptiveKernel.freshKernel (fun i => fun r : S × A => p i r.1 r.2)
      (fun r t => hp r.1 r.2 t) (L+T) ⊗ₖ blockKernel π hπ L T s₀).map Prod.snd =
      trajectoryKernel π p hπ hp T s₀ ×ₖ
        AdaptiveKernel.freshKernel (fun i => fun r : S × A => p i r.1 r.2)
          (fun r t => hp r.1 r.2 t) L := by
  ext i : 1
  rw [Kernel.map_apply _ measurable_snd, Kernel.prod_apply]
  have hjoint : (AdaptiveKernel.freshKernel (fun i => fun r : S × A => p i r.1 r.2)
      (fun r t => hp r.1 r.2 t) (L+T) ⊗ₖ blockKernel π hπ L T s₀) i =
      lawMeasure (joint (stackLaw (fun r : S × A => p i r.1 r.2) (L+T))
        (blockLaw (π i) L T 0 s₀)) := by
    rw [SourceConditional.kernel_compProd_at]
    symm
    apply SourceConditional.lawMeasure_joint_compProd
    intro tape
    rfl
  rw [hjoint, lawMeasure_joint_snd, SourceConditional.averaged_blockLaw_eq]
  change lawMeasure (joint (trajectoryLaw (π i) (p i) T 0 s₀)
    (fun _ => stackLaw (fun r : S × A => p i r.1 r.2) L)) =
    (lawMeasure (trajectoryLaw (π i) (p i) T 0 s₀)).prod
      (lawMeasure (stackLaw (fun r : S × A => p i r.1 r.2) L))
  rw [SourceConditional.lawMeasure_joint_compProd _ _
    (Kernel.const _ (lawMeasure (stackLaw (fun r : S × A => p i r.1 r.2) L))) (fun _ => rfl),
    Measure.compProd_const]

end
end Paper36.SourceBlockKernel
