import Paper34.StandardConcentration
import Paper34.MainStochastic
import Paper34.SourceComplexity

/-! The prescribed least grid, the prescribed sample counts, and Theorem 1.1.
All own-paper premises in the analytic/probabilistic chains are discharged.
Only the published trigonometric Bernstein theorem remains an explicit input.
Both standard concentration interfaces are instantiated from pinned mathlib.
All global verification remains deferred by the user's instruction. -/
namespace Paper34
open MeasureTheory
noncomputable section

/-- Exactly the least positive grid in (2.2), with the proved dimension constant. -/
def sourceGrid (n d : ℕ) (rho eps : ℝ) : ℕ :=
  SourceComplexity.gridSize (arbitraryRepresentativeConstant n) n d rho eps

instance sourceGrid_neZero (n d : ℕ) (rho eps : ℝ) : NeZero (sourceGrid n d rho eps) :=
  ⟨(SourceComplexity.gridSize_pos (arbitraryRepresentativeConstant n) n d rho eps).ne'⟩

def sourceChebyshevSamples (n d : ℕ) (rho eps delta : ℝ) : ℕ :=
  SourceComplexity.chebyshevSamples (arbitraryRepresentativeConstant n) n d rho eps delta

def sourceUniformSamples (n d : ℕ) (rho eps delta : ℝ) : ℕ :=
  SourceComplexity.uniformSamples (arbitraryRepresentativeConstant n) n d rho eps delta

def fixedSourceAnalysis (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n d : ℕ} {rho eps : ℝ} (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (he0 : 0 < eps) (he : eps ≤ 1/2) : RegressionAnalysis n d (sourceGrid n d rho eps) rho :=
  sourceRegressionAnalysis hBernstein hd hr0 hr he0 he
    (SourceComplexity.grid_constraints (arbitraryRepresentativeConstant n) n d rho eps).2.1
    (SourceComplexity.gamma_le_beta_div_six he0)

/-- Main theorem under the exact prescribed product-Chebyshev sample count. -/
theorem theorem_1_1_chebyshev
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} {rho eps sigma delta : ℝ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (hdelta0 : 0 < delta) (hdelta : delta ≤ eps) (he : eps ≤ 1/2)
    (S : GridSamplingModel n (sourceChebyshevSamples n d rho eps delta) rho P (chebyshevLaw n))
    (Y : Fin (sourceChebyshevSamples n d rho eps delta) → Ω → ℝ)
    (O : ExactRegressionLPOracle n d (sourceGrid n d rho eps))
    (p : PolynomialSpace n d) (hs : 0 ≤ sigma)
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p (S.X i ω)| ≤ sigma) :
    1-delta ≤ P.real {ω | supNorm
      (batchEstimate O (fixedSourceAnalysis hBernstein hd hr0 hr (hdelta0.trans_le hdelta) he)
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he)
        (fun i => S.X i ω) (fun i => Y i ω)-p) ≤ (2+eps)*sigma} := by
  letI : NeZero (SourceComplexity.gridSize (arbitraryRepresentativeConstant n) n d rho eps) :=
    sourceGrid_neZero n d rho eps
  have hM := SourceComplexity.sampleCount_threshold n (arbitraryRepresentativeConstant n) n d rho eps delta
  have hM' : gridConcentrationConstant rho*(sourceGrid n d rho eps : ℝ)^n*
      Real.log (2*(((sourceGrid n d rho eps)^n : ℕ) : ℝ)/delta) ≤ sourceChebyshevSamples n d rho eps delta := by
    simpa [gridConcentrationConstant, SourceComplexity.contaminationConstant, sourceGrid,
      sourceChebyshevSamples, SourceComplexity.chebyshevSamples] using hM
  exact theorem_1_1_chebyshev_probability hBernstein S Y (StandardConcentration.bernoulliLowerHalfInput P _) (StandardConcentration.bernoulliSubsetHoeffdingInput P _) hd
    (SourceComplexity.sampleCount_pos n (arbitraryRepresentativeConstant n) n d rho eps delta
      hr hdelta0 (by linarith)) hr0 hr (hdelta0.trans_le hdelta) he hdelta0 hdelta
    (SourceComplexity.grid_constraints (arbitraryRepresentativeConstant n) n d rho eps).2.1
    (SourceComplexity.gamma_le_beta_div_six (hdelta0.trans_le hdelta)) hM' O p hs hnoise

/-- Main theorem under the exact prescribed normalized-uniform sample count. -/
theorem theorem_1_1_uniform
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} {rho eps sigma delta : ℝ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (hdelta0 : 0 < delta) (hdelta : delta ≤ eps) (he : eps ≤ 1/2)
    (S : GridSamplingModel n (sourceUniformSamples n d rho eps delta) rho P (uniformLaw n))
    (Y : Fin (sourceUniformSamples n d rho eps delta) → Ω → ℝ)
    (O : ExactRegressionLPOracle n d (sourceGrid n d rho eps))
    (p : PolynomialSpace n d) (hs : 0 ≤ sigma)
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p (S.X i ω)| ≤ sigma) :
    1-delta ≤ P.real {ω | supNorm
      (batchEstimate O (fixedSourceAnalysis hBernstein hd hr0 hr (hdelta0.trans_le hdelta) he)
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he)
        (fun i => S.X i ω) (fun i => Y i ω)-p) ≤ (2+eps)*sigma} := by
  letI : NeZero (SourceComplexity.gridSize (arbitraryRepresentativeConstant n) n d rho eps) :=
    sourceGrid_neZero n d rho eps
  have hM := SourceComplexity.sampleCount_threshold (2*n) (arbitraryRepresentativeConstant n) n d rho eps delta
  have hM' : gridConcentrationConstant rho*(sourceGrid n d rho eps : ℝ)^(2*n)*
      Real.log (2*(((sourceGrid n d rho eps)^n : ℕ) : ℝ)/delta) ≤ sourceUniformSamples n d rho eps delta := by
    simpa [gridConcentrationConstant, SourceComplexity.contaminationConstant, sourceGrid,
      sourceUniformSamples, SourceComplexity.uniformSamples] using hM
  exact theorem_1_1_uniform_probability hBernstein S Y (StandardConcentration.bernoulliLowerHalfInput P _) (StandardConcentration.bernoulliSubsetHoeffdingInput P _) hd
    (SourceComplexity.sampleCount_pos (2*n) (arbitraryRepresentativeConstant n) n d rho eps delta
      hr hdelta0 (by linarith)) hr0 hr (hdelta0.trans_le hdelta) he hdelta0 hdelta
    (SourceComplexity.grid_constraints (arbitraryRepresentativeConstant n) n d rho eps).2.1
    (SourceComplexity.gamma_le_beta_div_six (hdelta0.trans_le hdelta)) hM' O p hs hnoise

/-- The two sample rates and the call budget, with fixed constants before all
accuracy, degree and confidence quantifiers, exactly as in Theorem 1.1. -/
theorem theorem_1_1_uniform_rates (n : ℕ) (rho : ℝ) (hr0 : 0 ≤ rho) (hr : rho < 1/2) :
    ∃ KC KU CT : ℝ, 0 < KC ∧ 0 < KU ∧ 0 < CT ∧
      ∀ (d : ℕ) (eps delta : ℝ) (hd : 1 ≤ d) (hdelta0 : 0 < delta)
        (hdelta : delta ≤ eps) (he : eps ≤ 1/2),
        (sourceChebyshevSamples n d rho eps delta : ℝ) ≤
          KC*((d : ℝ)/eps)^n*Real.log ((d : ℝ)/delta) ∧
        (sourceUniformSamples n d rho eps delta : ℝ) ≤
          KU*((d : ℝ)/eps)^(2*n)*Real.log ((d : ℝ)/delta) ∧
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he : ℝ) ≤
          CT*Real.log ((d : ℝ)/eps) := by
  obtain ⟨KC, KU, hKC, hKU, hS⟩ := SourceComplexity.source_sample_uniform_bounds
    (arbitraryRepresentativeConstant n) n rho (arbitraryRepresentativeConstant_ge_one n) hr0 hr
  obtain ⟨CT, hCT, hT⟩ := SourceComplexity.source_budget_log_uniform_bound n rho hr0 hr
  refine ⟨KC, KU, CT, hKC, hKU, hCT, ?_⟩
  intro d eps delta hd hdelta0 hdelta he
  exact ⟨(hS d eps delta hd hdelta0 hdelta he).1,
    (hS d eps delta hd hdelta0 hdelta he).2, hT d eps hd (hdelta0.trans_le hdelta) he⟩

/-- All inputs, including empty-cell inputs, satisfy the predetermined call
budget; the parameters in this statement contain no truth or noise scale. -/
theorem theorem_1_1_calls
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n d M : ℕ} {rho eps : ℝ}
    (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (O : ExactRegressionLPOracle n d (sourceGrid n d rho eps))
    (X : Fin M → Point n) (Y : Fin M → ℝ) :
    (runRegression O (fixedSourceAnalysis hBernstein hd hr0 hr he0 he)
      (observedGridOfBatch X Y) (refinementBudget n d rho eps he0 he)).oracleCalls ≤
        1+refinementBudget n d rho eps he0 he :=
  runRegression_calls_le O _ _ _

end
end Paper34
