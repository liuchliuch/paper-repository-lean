import Paper29.ObservedQueries
import Paper29.FiniteMeasureBridge
import Paper29.TwoBatchProbability

noncomputable section
open scoped BigOperators Classical ENNReal
open MeasureTheory
namespace Paper29.ProcessTools

/-- The finite product probability and observed-label implementation meet the
actual official nonadaptive model, including output and event measurability. -/
theorem batchProcedure_correct {n d m₀ m : ℕ}
    [MeasurableSpace ((Fin m₀ → Fin n) × (Fin m → Fin n))]
    [MeasurableSingletonClass ((Fin m₀ → Fin n) × (Fin m → Fin n))]
    (A : Matrix (Fin n) (Fin d) ℝ) (π₀ π : Fin n → ℝ)
    (hp₀ : ∀ i, 0 ≤ π₀ i) (hp : ∀ i, 0 ≤ π i)
    (hs₀ : ∑ i,π₀ i = 1) (hs : ∑ i,π i = 1) (ε : ℝ)
    (hgood : ∀ b, (99/100:ℝ) ≤ Sampling.eventMass (batchMass π₀ π)
      (Finset.univ.filter (fun ω : (Fin m₀ → Fin n) × (Fin m → Fin n) => ∀ x,
        Real.sqrt (objective A b (twoBatchOutput A b π₀ π hp₀ hp ω)) ≤
          (1+ε)*Real.sqrt (objective A b x)))) :
    QueryModel.NonadaptiveCorrect
      (finiteMeasure (batchMass (m₀:=m₀) (m:=m) π₀ π) (batchMass_nonneg π₀ π hp₀ hp)
        (batchMass_sum π₀ π hs₀ hs))
      (batchProcedure A π₀ π hp₀ hp) A ε := by
  apply nonadaptiveCorrect_of_finite_probability
  intro b
  simpa only [batchProcedure_answer] using hgood b

/-- Actual official-model existence for a reduced design, before replacing the
explicit batch count by the universal rank/logarithm bound. -/
theorem exists_nonadaptive_batch {n d m₀ m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (π₀ π : Fin n → ℝ) (hp₀ : ∀ i, 0 ≤ π₀ i) (hp : ∀ i, 0 ≤ π i)
    (hs₀ : ∑ i,π₀ i = 1) (hs : ∑ i,π i = 1) (ε : ℝ)
    (hgood : ∀ b, (99/100:ℝ) ≤ Sampling.eventMass (batchMass π₀ π)
      (Finset.univ.filter (fun ω : (Fin m₀ → Fin n) × (Fin m → Fin n) => ∀ x,
        Real.sqrt (objective A b (twoBatchOutput A b π₀ π hp₀ hp ω)) ≤
          (1+ε)*Real.sqrt (objective A b x)))) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ),
      @IsProbabilityMeasure Ω mΩ μ ∧ ∃ p : QueryModel.NonadaptiveProcedure Ω n d,
        @QueryModel.NonadaptiveCorrect Ω mΩ n d μ p A ε ∧
          ∀ ω, ((p.queried ω).card:ℝ) ≤ min (n:ℝ) ((m₀:ℝ)+m) := by
  let Ω := (Fin m₀ → Fin n) × (Fin m → Fin n)
  letI : MeasurableSpace Ω := ⊤
  haveI : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩
  let mass := batchMass (m₀:=m₀) (m:=m) π₀ π
  let hmass := batchMass_nonneg (m₀:=m₀) (m:=m) π₀ π hp₀ hp
  let htotal := batchMass_sum (m₀:=m₀) (m:=m) π₀ π hs₀ hs
  refine ⟨Ω, inferInstance, finiteMeasure mass hmass htotal, inferInstance,
    batchProcedure A π₀ π hp₀ hp, batchProcedure_correct A π₀ π hp₀ hp hs₀ hs ε hgood, ?_⟩
  intro ω
  have hh := batchQueries_card_le ω
  exact_mod_cast hh

end Paper29.ProcessTools
