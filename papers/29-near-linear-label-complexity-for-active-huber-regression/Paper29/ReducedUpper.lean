import Paper29.SamplingSizes
import Paper29.NonadaptiveBatch

noncomputable section
open scoped BigOperators Classical ENNReal
open MeasureTheory
namespace Paper29.ProcessTools

def reducedUpperConstant (C G K : ℝ) : ℝ :=
  pilotSizeConstant C G K + mainSizeConstant C G K + 2/(Real.log 2)^6

/-- Main upper-bound construction on a full-column-rank, nonzero-row design
with more than sixteen rows. Both batches and the observed-label procedure are
actual definitions; only known published external general tools are inputs. -/
theorem reduced_upper_large {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℝ)
    (hn : 16 < n) (hr : 1 ≤ r) (hA : A.rank = r) (hrows : ∀ i, A i ≠ 0)
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
          (reducedUpperConstant C (2*Cₜ+4*Cₑ) (4+26/Real.log 2)) ε := by
  have hn1 : 1 ≤ n := by omega
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let τ := Chaining.finiteScores A hA hrows stability
  let G : ℝ := 2*Cₜ+4*Cₑ
  let K : ℝ := 4+26/Real.log 2
  have hG : 0 < G := by dsimp [G]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨hτ,hT,hcover⟩ := Chaining.finiteScores_spec A hn1 hA hrows Cₜ Cₑ hCₜ.le hCₑ.le
    stability transition endpoint lewis
  let m₀ : ℕ := ⌈pilotRawSize C G τ⌉₊
  let m : ℕ := ⌈mainRawSize C G τ ε⌉₊
  let π₀ := scoreProbability (pilotScores τ)
  let π := scoreProbability τ
  have hp₀ := pilotProbability_nonneg hn1 τ hτ
  have hp := scoreProbability_nonneg hn1 τ hτ
  have hs₀ := (scoreProbability_spec hn1 (pilotScores τ) (pilotScores_spec hn1 τ hτ).1).2.2.1
  have hs := (scoreProbability_spec hn1 τ hτ).2.2.1
  have hη := mainAccuracy_spec hε hεhi
  have hgood (b : Fin n → ℝ) : (99/100:ℝ) ≤ Sampling.eventMass (batchMass π₀ π)
      (Finset.univ.filter (fun ω : (Fin m₀ → Fin n) × (Fin m → Fin n) => ∀ x,
        Real.sqrt (objective A b (twoBatchOutput A b π₀ π hp₀ hp ω)) ≤
          (1+ε)*Real.sqrt (objective A b x))) := by
    apply overall_success_probability.trans
    exact two_batch_probability A hn τ hτ C G failureProbability failureProbability (mainAccuracy ε) ε
      hC hG (by norm_num [failureProbability]) (by norm_num [failureProbability])
      (by norm_num [failureProbability]) (by norm_num [failureProbability]) hη.1 hη.2.1 hε.le rfl
      external hcover (Nat.le_ceil _) (Nat.le_ceil _) b
  obtain ⟨Ω,mΩ,μ,hμ,p,hcorrect,hcount⟩ := exists_nonadaptive_batch A π₀ π hp₀ hp hs₀ hs ε hgood
  refine ⟨Ω,mΩ,μ,hμ,p,hcorrect,?_⟩
  have hraw := raw_sizes_rank_bound hn1 C G K hK τ (fun i => (hτ i).le) hT hε hεhi
  have hlog : 0 ≤ Real.log (2*(n:ℝ)) := by
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn1
    exact (Real.log_pos (by linarith : (1:ℝ)<2*n)).le
  have hmass : 0 ≤ ∑ i,τ i := Finset.sum_nonneg (fun i _ => (hτ i).le)
  have ha : 0 ≤ pilotRawSize C G τ := by unfold pilotRawSize; positivity
  have hb : 0 ≤ mainRawSize C G τ ε := by unfold mainRawSize transferConstant; positivity
  have hP : 0 ≤ pilotSizeConstant C G K := by unfold pilotSizeConstant; positivity
  have hM : 0 ≤ mainSizeConstant C G K := by unfold mainSizeConstant transferConstant; positivity
  have hbudget := rounded_size_bound hn1 hr ha hb hP hM hε hraw.1 hraw.2
  intro ω
  apply (hcount ω).trans
  apply min_le_min_left
  simpa only [m₀, m, Nat.cast_add, reducedUpperConstant] using hbudget

end Paper29.ProcessTools
