import Paper14.Background.MeasureCompact
import Mathlib.Topology.Sequences

open MeasureTheory Filter Topology Set
open scoped NNReal
namespace Paper14
noncomputable section

/-- A single subsequence simultaneously converges for a countable family
of finite measures with uniformly bounded mass on a compact metric space.
Masses and normalized probability measures are extracted together, so zero
components are allowed. -/
theorem finiteMeasure_simultaneous_subsequence
    {E ι : Type*} [MeasurableSpace E] [MetricSpace E] [CompactSpace E]
    [BorelSpace E] [Nonempty E] [Countable ι]
    (ν : ℕ → ι → FiniteMeasure E) (C : ℝ≥0)
    (hbound : ∀ n j, (ν n j).mass ≤ C) :
    ∃ (η : ι → FiniteMeasure E) (s : ℕ → ℕ), StrictMono s ∧
      (∀ j, Tendsto (fun n => ν (s n) j) atTop (𝓝 (η j))) ∧
      (∀ j, (η j).mass ≤ C) := by
  let K := Set.Icc (0 : ℝ≥0) C × ProbabilityMeasure E
  let u : ℕ → (ι → K) := fun n j =>
    (⟨(ν n j).mass, zero_le _, hbound n j⟩, (ν n j).normalize)
  obtain ⟨a,s,hs,ha⟩ := CompactSpace.tendsto_subseq u
  let η : ι → FiniteMeasure E := fun j => (a j).1.val • (a j).2.toFiniteMeasure
  refine ⟨η,s,hs,?_,?_⟩
  · intro j
    have hj : Tendsto (fun n => u (s n) j) atTop (𝓝 (a j)) :=
      (continuous_apply j).continuousAt.tendsto.comp ha
    have hm : Tendsto (fun n => (ν (s n) j).mass) atTop (𝓝 (a j).1.val) :=
      (continuous_subtype_val.comp continuous_fst).continuousAt.tendsto.comp hj
    have hp : Tendsto (fun n => (ν (s n) j).normalize.toFiniteMeasure) atTop
        (𝓝 (a j).2.toFiniteMeasure) :=
      (ProbabilityMeasure.toFiniteMeasure_continuous).continuousAt.tendsto.comp
        (continuous_snd.continuousAt.tendsto.comp hj)
    rw [FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto]
    intro f
    have hf := (FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto.mp hp) f
    have heq : (fun n => (ν (s n) j).testAgainstNN f) =
        (fun n => (ν (s n) j).mass * (ν (s n) j).normalize.toFiniteMeasure.testAgainstNN f) := by
      funext n
      exact (ν (s n) j).testAgainstNN_eq_mass_mul f
    rw [heq]
    change Tendsto _ atTop (𝓝 (((a j).1.val • (a j).2.toFiniteMeasure).testAgainstNN f))
    rw [FiniteMeasure.smul_testAgainstNN_apply, smul_eq_mul]
    exact hm.mul hf
  · intro j
    change ((a j).1.val • (a j).2.toFiniteMeasure).mass ≤ C
    simpa only [FiniteMeasure.mass,FiniteMeasure.smul_apply,smul_eq_mul,
      ProbabilityMeasure.toFiniteMeasure_apply_eq_apply,
      ProbabilityMeasure.coeFn_univ,mul_one] using (a j).1.property.2

end
end Paper14
