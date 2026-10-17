import Paper34.SourceTheorem
import Paper34.AppendixSpaces

/-!
# Statistical recovery in the actual restricted polynomial space

Appendix A.3 uses exactly the prescribed source grid, samples, and refinement
budget. Optimizer queries and the returned estimator take values in the chosen
submodule. The probability event depends only on the same locations and outlier
indicators, so it transfers to the restricted estimator without changing either
sampling rate. No extra published input is introduced by the restriction.
-/
namespace Paper34.AppendixSpaces
open Set MeasureTheory
noncomputable section

/-- The complete batch estimator with values in the actual restricted space. -/
def restrictedBatchEstimate {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (T : ℕ) (X : Fin M → Point n) (Y : Fin M → ℝ) : R :=
  (runRestricted R O C (observedGridOfBatch X Y) T).estimate

/-- The same fixed half-open good event supplies every deterministic premise
for the restricted estimator on the actual observed batch. -/
theorem restrictedBatch_error_of_halfOpenGoodEvent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n d m M : ℕ} [NeZero m] {rho eps sigma : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (Y : Fin M → Ω → ℝ)
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (p : R)
    (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hs : 0 ≤ sigma) (hg0 : 0 ≤ C.gamma) (hg : C.gamma ≤ beta eps/(2+beta eps))
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p.1 (S.X i ω)| ≤ sigma)
    {ω : Ω} (hω : ω ∈ halfOpenGoodEvent (m := m) S) :
    supNorm ((restrictedBatchEstimate R O C (refinementBudget n d rho eps he0 he)
      (fun i => S.X i ω) (fun i => Y i ω)).1-p.1) ≤ (2+eps)*sigma := by
  classical
  let D : ObservedGrid n m M := observedGridOfBatch (fun i => S.X i ω) (fun i => Y i ω)
  let inlier : Fin M → Prop := fun i => S.O i ω = false
  have hN : ∀ j, (D.samples j).Nonempty := fun j => (halfOpenGoodEvent_cell_spec S hω j).1
  have hbad : ∀ j, (D.toGood hN inlier).bad j = halfOpenOutliers S ω j := by
    intro j
    ext i
    simp only [GoodSampleGrid.bad, ObservedGrid.toGood, D, observedGridOfBatch,
      halfOpenOutliers, halfOpenSamples, Finset.mem_filter, Finset.mem_univ, true_and, inlier]
    cases S.O i ω <;> simp
  have hgood : (D.toGood hN inlier).GoodAt rho := by
    intro j
    have hNc : (0 : ℝ) < (D.samples j).card := by exact_mod_cast Finset.card_pos.mpr (hN j)
    apply (div_le_iff₀ hNc).mpr
    rw [hbad]
    exact (halfOpenGoodEvent_cell_spec S hω j).2
  have hn : ∀ j, ∀ i ∈ D.samples j, inlier i →
      |polyEval p.1 (D.location i)-D.label i| ≤ sigma := by
    intro j i hi hg
    simpa only [D, observedGridOfBatch, abs_sub_comm] using hnoise ω i hg
  exact runRestricted_error_on_good_grid R O C D hN inlier p hr0 hr he0 he hs hg0 hg hgood hn

/-- The original measurable good-grid probability transfers to recovery by
any actual restricted exact oracle, including arbitrary adversarial labels. -/
theorem restricted_probability_of_good_grid
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d m M : ℕ} [NeZero m] {rho eps sigma delta : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (Y : Fin M → Ω → ℝ)
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (p : R)
    (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hs : 0 ≤ sigma) (hg0 : 0 ≤ C.gamma) (hg : C.gamma ≤ beta eps/(2+beta eps))
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p.1 (S.X i ω)| ≤ sigma)
    (hgoodprob : 1-delta ≤ P.real (halfOpenGoodEvent (m := m) S)) :
    1-delta ≤ P.real {ω | supNorm
      ((restrictedBatchEstimate R O C (refinementBudget n d rho eps he0 he)
        (fun i => S.X i ω) (fun i => Y i ω)).1-p.1) ≤ (2+eps)*sigma} := by
  apply probability_of_event_containing_halfOpenGoodEvent S hgoodprob
  intro ω hω
  exact restrictedBatch_error_of_halfOpenGoodEvent S Y R O C p hr0 hr he0 he hs hg0 hg hnoise hω

/-- The prescribed source Chebyshev sample count works in every actual
subspace. The internal analysis package is fully instantiated. -/
theorem restricted_source_chebyshev
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} {rho eps sigma delta : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d))
    (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (hdelta0 : 0 < delta) (hdelta : delta ≤ eps) (he : eps ≤ 1/2)
    (S : GridSamplingModel n (sourceChebyshevSamples n d rho eps delta) rho P (chebyshevLaw n))
    (Y : Fin (sourceChebyshevSamples n d rho eps delta) → Ω → ℝ)
    (O : RestrictedLPOracle R (sourceGrid n d rho eps)) (p : R) (hs : 0 ≤ sigma)
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p.1 (S.X i ω)| ≤ sigma) :
    1-delta ≤ P.real {ω | supNorm
      ((restrictedBatchEstimate R O (fixedSourceAnalysis hBernstein hd hr0 hr (hdelta0.trans_le hdelta) he)
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he)
        (fun i => S.X i ω) (fun i => Y i ω)).1-p.1) ≤ (2+eps)*sigma} := by
  have he0 : 0 < eps := hdelta0.trans_le hdelta
  let C := fixedSourceAnalysis (n := n) hBernstein hd hr0 hr (hdelta0.trans_le hdelta) he
  have hgc : C.gamma ≤ beta eps/(2+beta eps) :=
    grid_implies_contraction (by unfold beta; positivity) (by unfold beta; linarith)
      (SourceComplexity.gamma_le_beta_div_six (hdelta0.trans_le hdelta))
  have hM := SourceComplexity.sampleCount_threshold n (arbitraryRepresentativeConstant n) n d rho eps delta
  have hM' : gridConcentrationConstant rho*(sourceGrid n d rho eps : ℝ)^n*
      Real.log (2*(((sourceGrid n d rho eps)^n : ℕ) : ℝ)/delta) ≤ sourceChebyshevSamples n d rho eps delta := by
    simpa [gridConcentrationConstant, SourceComplexity.contaminationConstant, sourceGrid,
      sourceChebyshevSamples, SourceComplexity.chebyshevSamples] using hM
  exact restricted_probability_of_good_grid S Y R O C p hr0 hr (hdelta0.trans_le hdelta) he hs
    (oscillationFactor_nonneg n d _) hgc hnoise
    (chebyshev_halfOpen_good_grid_probability S (StandardConcentration.bernoulliLowerHalfInput P _) (StandardConcentration.bernoulliSubsetHoeffdingInput P _) (NeZero.pos _)
      (SourceComplexity.sampleCount_pos n (arbitraryRepresentativeConstant n) n d rho eps delta
        hr hdelta0 (by linarith)) hr0 hr hdelta0 (by linarith) hM')

/-- The prescribed normalized-uniform sample count works in every actual
subspace, with the source exponent 2n and unchanged refinement budget. -/
theorem restricted_source_uniform
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} {rho eps sigma delta : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d))
    (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (hdelta0 : 0 < delta) (hdelta : delta ≤ eps) (he : eps ≤ 1/2)
    (S : GridSamplingModel n (sourceUniformSamples n d rho eps delta) rho P (uniformLaw n))
    (Y : Fin (sourceUniformSamples n d rho eps delta) → Ω → ℝ)
    (O : RestrictedLPOracle R (sourceGrid n d rho eps)) (p : R) (hs : 0 ≤ sigma)
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p.1 (S.X i ω)| ≤ sigma) :
    1-delta ≤ P.real {ω | supNorm
      ((restrictedBatchEstimate R O (fixedSourceAnalysis hBernstein hd hr0 hr (hdelta0.trans_le hdelta) he)
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he)
        (fun i => S.X i ω) (fun i => Y i ω)).1-p.1) ≤ (2+eps)*sigma} := by
  have he0 : 0 < eps := hdelta0.trans_le hdelta
  let C := fixedSourceAnalysis (n := n) hBernstein hd hr0 hr (hdelta0.trans_le hdelta) he
  have hgc : C.gamma ≤ beta eps/(2+beta eps) :=
    grid_implies_contraction (by unfold beta; positivity) (by unfold beta; linarith)
      (SourceComplexity.gamma_le_beta_div_six (hdelta0.trans_le hdelta))
  have hM := SourceComplexity.sampleCount_threshold (2*n) (arbitraryRepresentativeConstant n) n d rho eps delta
  have hM' : gridConcentrationConstant rho*(sourceGrid n d rho eps : ℝ)^(2*n)*
      Real.log (2*(((sourceGrid n d rho eps)^n : ℕ) : ℝ)/delta) ≤ sourceUniformSamples n d rho eps delta := by
    simpa [gridConcentrationConstant, SourceComplexity.contaminationConstant, sourceGrid,
      sourceUniformSamples, SourceComplexity.uniformSamples] using hM
  exact restricted_probability_of_good_grid S Y R O C p hr0 hr (hdelta0.trans_le hdelta) he hs
    (oscillationFactor_nonneg n d _) hgc hnoise
    (uniform_halfOpen_good_grid_probability S (StandardConcentration.bernoulliLowerHalfInput P _) (StandardConcentration.bernoulliSubsetHoeffdingInput P _) (NeZero.pos _)
      (SourceComplexity.sampleCount_pos (2*n) (arbitraryRepresentativeConstant n) n d rho eps delta
        hr hdelta0 (by linarith)) hr0 hr hdelta0 (by linarith) hM')

/-- A total-degree restricted output is a total-degree polynomial on every
input batch, including batches with empty cells. -/
theorem restrictedBatchEstimate_totalDegree {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : RestrictedLPOracle (totalDegreeSubspace n d) m)
    (C : RegressionAnalysis n d m rho) (T : ℕ) (X : Fin M → Point n) (Y : Fin M → ℝ) :
    (restrictedBatchEstimate (totalDegreeSubspace n d) O C T X Y).1.1.totalDegree ≤ d :=
  (mem_totalDegreeSubspace _).mp (restrictedBatchEstimate (totalDegreeSubspace n d) O C T X Y).2

/-- At zero noise the success event is actual equality in R. -/
theorem restricted_exact_probability_of_zero_error
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} (R : Submodule ℝ (PolynomialSpace n d)) (output : Ω → R) (p : R) {delta : ℝ}
    (h : 1-delta ≤ P.real {ω | supNorm ((output ω).1-p.1) ≤ 0}) :
    1-delta ≤ P.real {ω | output ω = p} := by
  apply h.trans (measureReal_mono _)
  intro ω hω
  change supNorm ((output ω).1-p.1) ≤ 0 at hω
  change output ω = p
  apply Subtype.ext
  rw [← norm_eq_supNorm] at hω
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hω (norm_nonneg _)))

/-- Both sample rates and the call budget are literally the same source
functions; restriction only replaces the coefficient-block dimension. -/
theorem restricted_source_rates (n : ℕ) (rho : ℝ) (hr0 : 0 ≤ rho) (hr : rho < 1/2) :
    ∃ KC KU CT : ℝ, 0 < KC ∧ 0 < KU ∧ 0 < CT ∧
      ∀ (d : ℕ) (eps delta : ℝ) (_hd : 1 ≤ d) (hdelta0 : 0 < delta)
        (hdelta : delta ≤ eps) (he : eps ≤ 1/2),
        (sourceChebyshevSamples n d rho eps delta : ℝ) ≤
          KC*((d : ℝ)/eps)^n*Real.log ((d : ℝ)/delta) ∧
        (sourceUniformSamples n d rho eps delta : ℝ) ≤
          KU*((d : ℝ)/eps)^(2*n)*Real.log ((d : ℝ)/delta) ∧
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he : ℝ) ≤
          CT*Real.log ((d : ℝ)/eps) := theorem_1_1_uniform_rates n rho hr0 hr

end
end Paper34.AppendixSpaces
