import Paper34.SourceTheorem
import Paper34.OtherDesigns

/-! Source appendix A.3 with all own analytic inputs instantiated, and the
zero-noise specialization of the exact prescribed source estimator. -/
namespace Paper34
open MeasureTheory
noncomputable section

theorem theorem_1_1_chebyshev_exact
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} {rho eps delta : ℝ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (hdelta0 : 0 < delta) (hdelta : delta ≤ eps) (he : eps ≤ 1/2)
    (S : GridSamplingModel n (sourceChebyshevSamples n d rho eps delta) rho P (chebyshevLaw n))
    (Y : Fin (sourceChebyshevSamples n d rho eps delta) → Ω → ℝ)
    (O : ExactRegressionLPOracle n d (sourceGrid n d rho eps))
    (p : PolynomialSpace n d)
    (hnoise : ∀ ω i, S.O i ω = false → Y i ω = polyEval p (S.X i ω)) :
    1-delta ≤ P.real {ω |
      batchEstimate O (fixedSourceAnalysis hBernstein hd hr0 hr (hdelta0.trans_le hdelta) he)
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he)
        (fun i => S.X i ω) (fun i => Y i ω) = p} := by
  apply exact_recovery_probability_of_zero_error
  simpa only [mul_zero] using theorem_1_1_chebyshev hBernstein hn hd hr0 hr
    hdelta0 hdelta he S Y O p (le_refl 0)
      (fun ω i hi => by simp only [hnoise ω i hi, sub_self, abs_zero, le_refl])

theorem theorem_1_1_uniform_exact
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} {rho eps delta : ℝ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (hdelta0 : 0 < delta) (hdelta : delta ≤ eps) (he : eps ≤ 1/2)
    (S : GridSamplingModel n (sourceUniformSamples n d rho eps delta) rho P (uniformLaw n))
    (Y : Fin (sourceUniformSamples n d rho eps delta) → Ω → ℝ)
    (O : ExactRegressionLPOracle n d (sourceGrid n d rho eps))
    (p : PolynomialSpace n d)
    (hnoise : ∀ ω i, S.O i ω = false → Y i ω = polyEval p (S.X i ω)) :
    1-delta ≤ P.real {ω |
      batchEstimate O (fixedSourceAnalysis hBernstein hd hr0 hr (hdelta0.trans_le hdelta) he)
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he)
        (fun i => S.X i ω) (fun i => Y i ω) = p} := by
  apply exact_recovery_probability_of_zero_error
  simpa only [mul_zero] using theorem_1_1_uniform hBernstein hn hd hr0 hr
    hdelta0 hdelta he S Y O p (le_refl 0)
      (fun ω i hi => by simp only [hnoise ω i hi, sub_self, abs_zero, le_refl])

/-- Appendix A.3 for the same fixed grid and fixed budget as the main
algorithm. Only the design law's true half-open cell mass lower bound changes. -/
theorem source_other_design_recovery
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d M : ℕ} {rho eps sigma delta pmin : ℝ} {law : Measure (Point n)}
    (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (he0 : 0 < eps) (he : eps ≤ 1/2) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (S : GridSamplingModel n M rho P law) (Y : Fin M → Ω → ℝ)
    (hpmin : 0 < pmin)
    (hcell : ∀ j : CellIndex n (sourceGrid n d rho eps), pmin ≤ law.real (halfOpenCell j))
    (hM : gridConcentrationConstant rho * pmin⁻¹ *
      Real.log (2*(((sourceGrid n d rho eps)^n : ℕ) : ℝ)/delta) ≤ M)
    (O : ExactRegressionLPOracle n d (sourceGrid n d rho eps))
    (p : PolynomialSpace n d) (hs : 0 ≤ sigma)
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p (S.X i ω)| ≤ sigma) :
    1-delta ≤ P.real {ω | supNorm
      (batchEstimate O (fixedSourceAnalysis hBernstein hd hr0 hr he0 he)
        (refinementBudget n d rho eps he0 he) (fun i => S.X i ω) (fun i => Y i ω)-p) ≤
          (2+eps)*sigma} := by
  let C : RegressionAnalysis n d (sourceGrid n d rho eps) rho :=
    fixedSourceAnalysis hBernstein hd hr0 hr he0 he
  have hgamma : C.gamma ≤ beta eps/(2+beta eps) :=
    grid_implies_contraction (by unfold beta; positivity) (by unfold beta; linarith)
      (SourceComplexity.gamma_le_beta_div_six he0)
  exact other_design_regression_probability S Y (StandardConcentration.bernoulliLowerHalfInput P _) (StandardConcentration.bernoulliSubsetHoeffdingInput P _) hr0 hr he0 he
    hdelta0 hdelta1 hpmin hcell hM O C p hs
    (oscillationFactor_nonneg n d (sourceGrid n d rho eps)) hgamma hnoise

/-- The no-empty-cell branch attains the exact advertised number of calls. -/
theorem source_calls_of_nonempty
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n d M : ℕ} {rho eps : ℝ}
    (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (O : ExactRegressionLPOracle n d (sourceGrid n d rho eps))
    (X : Fin M → Point n) (Y : Fin M → ℝ)
    (hN : ∀ j : CellIndex n (sourceGrid n d rho eps),
      ((observedGridOfBatch X Y).samples j).Nonempty) :
    (runRegression O (fixedSourceAnalysis hBernstein hd hr0 hr he0 he)
      (observedGridOfBatch X Y) (refinementBudget n d rho eps he0 he)).oracleCalls =
        1+refinementBudget n d rho eps he0 he :=
  runRegression_calls_of_nonempty O _ _ _ hN

end
end Paper34
