import Paper29.FiniteRowReduction
import Paper29.FiniteMeasureBridge
import Paper29.Attainment

noncomputable section
open scoped BigOperators Classical ENNReal
open MeasureTheory
namespace Paper29.Reduction

/-- Lift the actual preselected queried set and its observed-label output map. -/
def liftProcedure {n d : ℕ} {Ω : Type*} (A : Matrix (Fin n) (Fin d) ℝ)
    (alg : QueryModel.NonadaptiveProcedure Ω (retainedCount A) A.rank) :
    QueryModel.NonadaptiveProcedure Ω n d where
  queried := fun ω => (alg.queried ω).image (retainedIndex A)
  output := fun ω labels => (OrthonormalReduction.coordinates A).mulVec
    (alg.output ω (fun i => labels ⟨retainedIndex A i,
      Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩))

theorem liftProcedure_answer {n d : ℕ} {Ω : Type*} (A : Matrix (Fin n) (Fin d) ℝ)
    (alg : QueryModel.NonadaptiveProcedure Ω (retainedCount A) A.rank)
    (ω : Ω) (b : Fin n → ℝ) : (liftProcedure A alg).answer ω b =
      (OrthonormalReduction.coordinates A).mulVec (alg.answer ω (fun i => b (retainedIndex A i))) := rfl

theorem liftProcedure_card {n d : ℕ} {Ω : Type*} (A : Matrix (Fin n) (Fin d) ℝ)
    (alg : QueryModel.NonadaptiveProcedure Ω (retainedCount A) A.rank) (ω : Ω) :
    ((liftProcedure A alg).queried ω).card = (alg.queried ω).card :=
  Finset.card_image_of_injective _ (retainedIndex_injective A)

/-- Success for a measurable output map is itself measurable, because the
source objective attains its minimum. This discharges the apparent uncountable
universal quantifier in the official correctness event. -/
theorem measurable_success_event {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (output : Ω → Fin d → ℝ)
    (hout : Measurable output) {ε : ℝ} (hε : 0 ≤ ε) :
    MeasurableSet {ω | ∀ x, Real.sqrt (objective A b (output ω)) ≤
      (1+ε)*Real.sqrt (objective A b x)} := by
  obtain ⟨xstar,hstar⟩ := Attainment.affineHuber_attains A (fun _ => 1) b (fun _ => by norm_num)
  have hstar' : ∀ x, objective A b xstar ≤ objective A b x := by
    simpa only [Attainment.affineHuber, weightedHuber, one_mul, objective] using hstar
  have he : {ω | ∀ x, Real.sqrt (objective A b (output ω)) ≤ (1+ε)*Real.sqrt (objective A b x)} =
      {ω | Real.sqrt (objective A b (output ω)) ≤ (1+ε)*Real.sqrt (objective A b xstar)} := by
    ext ω
    constructor
    · exact fun h => h xstar
    · intro h x
      exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hstar' x)) (by linarith))
  rw [he]
  have hc : Continuous (fun x => objective A b x) := by
    have he : (fun x => objective A b x) = Attainment.affineHuber A (fun _ => 1) b := by
      funext x
      simp [Attainment.affineHuber, weightedHuber, objective]
    rw [he]
    exact Attainment.continuous_affineHuber A (fun _ => 1) b
  exact measurableSet_le (Real.continuous_sqrt.measurable.comp (hc.measurable.comp hout)) measurable_const

/-- Correctness survives actual zero-row deletion and orthonormal rank lifting.
All measurability obligations in the official model are proved here. -/
theorem liftProcedure_correct {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A : Matrix (Fin n) (Fin d) ℝ) (μ : Measure Ω)
    (alg : QueryModel.NonadaptiveProcedure Ω (retainedCount A) A.rank)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorrect : QueryModel.NonadaptiveCorrect μ alg (finiteReducedDesign A) ε) :
    QueryModel.NonadaptiveCorrect μ (liftProcedure A alg) A ε := by
  have houtput (b : Fin n → ℝ) : Measurable (fun ω => (liftProcedure A alg).answer ω b) := by
    simp only [liftProcedure_answer]
    exact (OrthonormalReduction.coordinates A).mulVecLin.continuous_of_finiteDimensional.measurable.comp
      (hcorrect.2.1 (fun i => b (retainedIndex A i)))
  refine ⟨?_, houtput, ?_⟩
  · intro j
    have he : {ω | j ∈ (liftProcedure A alg).queried ω} =
        ⋃ i : Fin (retainedCount A), {ω | i ∈ alg.queried ω ∧ retainedIndex A i = j} := by
      ext ω
      simp [liftProcedure, Finset.mem_image]
    rw [he]
    exact MeasurableSet.iUnion (fun i => (hcorrect.1 i).inter (MeasurableSet.const _))
  · intro b
    refine ⟨measurable_success_event A b _ (houtput b) hε, ?_⟩
    apply (hcorrect.2.2 (fun i => b (retainedIndex A i))).2.trans
    apply measure_mono
    intro ω hω
    rw [Set.mem_setOf_eq] at hω ⊢
    rw [liftProcedure_answer]
    exact finiteReduced_relative_guarantee A b _ hε hω

end Paper29.Reduction
