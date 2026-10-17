import Paper29.ReducedUpper
import Paper29.BudgetMonotonicity
import Paper29.ExactProcedures

noncomputable section
open scoped BigOperators Classical ENNReal
open MeasureTheory
namespace Paper29.ProcessTools

def upperConstant (C G K : ℝ) : ℝ := reducedUpperConstant C G K + 16/(Real.log 2)^6

theorem upperConstant_spec (C G K : ℝ) (hK : 0 ≤ K) :
    0 < upperConstant C G K ∧ reducedUpperConstant C G K ≤ upperConstant C G K ∧
      16/(Real.log 2)^6 ≤ upperConstant C G K := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : 0 ≤ pilotSizeConstant C G K := by unfold pilotSizeConstant; positivity
  have hm : 0 ≤ mainSizeConstant C G K := by unfold mainSizeConstant transferConstant; positivity
  have hsmall : 0 < 16/(Real.log 2)^6 := by positivity
  have hr : 0 ≤ reducedUpperConstant C G K := by unfold reducedUpperConstant; positivity
  unfold upperConstant
  constructor
  · linarith
  constructor <;> linarith

/-- Full-rank upper bound at all positive pool sizes. Small pools use the
actual exact full-query procedure; large pools use the two independently
preselected batches and the finite score construction. -/
theorem full_rank_upper {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℝ)
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hA : A.rank = r) (hrows : ∀ i, A i ≠ 0)
    (C Cₜ Cₑ : ℝ) (hC : 0 < C) (hCₜ : 0 < Cₜ) (hCₑ : 0 < Cₑ)
    (external : ExternalProcess.AnchoredChaining C)
    (stability : WeightConstruction.RadiusLogNonexpansive)
    (transition : ExternalCovering.HuberPrimitive 4 Cₜ)
    (endpoint : ExternalCovering.PowerPrimitive Cₑ) (lewis : ExternalCovering.LewisOneNormalization)
    {ε : ℝ} (hε : 0 < ε) (hεhi : ε < 1/2) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ),
      @IsProbabilityMeasure Ω mΩ μ ∧ ∃ p : QueryModel.NonadaptiveProcedure Ω n r,
        @QueryModel.NonadaptiveCorrect Ω mΩ n r μ p A ε ∧
        ∀ ω, ((p.queried ω).card:ℝ) ≤ QueryModel.upperBudget n r
          (upperConstant C (2*Cₜ+4*Cₑ) (4+26/Real.log 2)) ε := by
  have hK : (0:ℝ) ≤ 4+26/Real.log 2 := by positivity
  have hconst := upperConstant_spec C (2*Cₜ+4*Cₑ) (4+26/Real.log 2) hK
  by_cases hn16 : n ≤ 16
  · refine ⟨Unit,inferInstance,finiteMeasure unitMass (fun _ => by norm_num [unitMass]) unitMass_sum,
      inferInstance,fullQueryProcedure A,fullQueryProcedure_correct A hε.le,?_⟩
    intro ω
    simpa only [fullQueryProcedure, Finset.card_univ, Fintype.card_fin] using
      small_pool_budget (ε:=ε) hn hn16 hr hconst.2.2
  · obtain ⟨Ω,mΩ,μ,hμ,p,hp,hcount⟩ := reduced_upper_large A (by omega) hr hA hrows C Cₜ Cₑ
      hC hCₜ hCₑ external stability transition endpoint lewis hε hεhi
    refine ⟨Ω,mΩ,μ,hμ,p,hp,?_⟩
    intro ω
    exact (hcount ω).trans (upperBudget_mono_constant hconst.2.1)

/-- Theorem2.1 with its exact official model and every original design/rank,
including rank zero, zero rows, zero optimum and small pools. The only explicit
inputs are precisely disclosed published general results; every P29-specific
sampling, localization, rank lifting and query-budget deduction is proved. -/
theorem theorem2_1 (C Cₜ Cₑ : ℝ) (hC : 0 < C) (hCₜ : 0 < Cₜ) (hCₑ : 0 < Cₑ)
    (external : ExternalProcess.AnchoredChaining C)
    (stability : WeightConstruction.RadiusLogNonexpansive)
    (transition : ExternalCovering.HuberPrimitive 4 Cₜ)
    (endpoint : ExternalCovering.PowerPrimitive Cₑ) (lewis : ExternalCovering.LewisOneNormalization) :
    QueryModel.UpperBoundStatement := by
  let Cᵤ := upperConstant C (2*Cₜ+4*Cₑ) (4+26/Real.log 2)
  have hK : (0:ℝ) ≤ 4+26/Real.log 2 := by positivity
  have hconst := (upperConstant_spec C (2*Cₜ+4*Cₑ) (4+26/Real.log 2) hK).1
  refine ⟨Cᵤ,hconst,?_⟩
  intro n d A ε hε hεhi
  by_cases hr0 : A.rank = 0
  · refine ⟨Unit,inferInstance,finiteMeasure unitMass (fun _ => by norm_num [unitMass]) unitMass_sum,
      inferInstance,zeroQueryProcedure n d,zeroQueryProcedure_correct A hr0 hε.le,?_⟩
    intro ω
    simp [zeroQueryProcedure, QueryModel.upperBudget, hr0]
  · have hr : 1 ≤ A.rank := by omega
    have hred := Reduction.finiteReducedDesign_rank A
    have hrows := Reduction.finiteReducedDesign_nozero A
    have hNrank : A.rank ≤ Reduction.retainedCount A := by
      rw [← hred]
      simpa only [Fintype.card_fin] using Matrix.rank_le_card_height (Reduction.finiteReducedDesign A)
    have hN : 1 ≤ Reduction.retainedCount A := hr.trans hNrank
    obtain ⟨Ω,mΩ,μ,hμ,p,hp,hcount⟩ := full_rank_upper (Reduction.finiteReducedDesign A)
      hN hr hred hrows C Cₜ Cₑ hC hCₜ hCₑ external stability transition endpoint lewis hε hεhi
    letI : MeasurableSpace Ω := mΩ
    refine ⟨Ω,mΩ,μ,hμ,Reduction.liftProcedure A p,
      Reduction.liftProcedure_correct A μ p hε.le hp,?_⟩
    intro ω
    rw [Reduction.liftProcedure_card]
    exact (hcount ω).trans (upperBudget_mono_pool hN (Reduction.retained_card_le A) hconst.le)

end Paper29.ProcessTools
