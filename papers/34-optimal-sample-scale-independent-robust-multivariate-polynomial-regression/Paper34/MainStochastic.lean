import Paper34.CompleteAnalysis
import Paper34.SourceSamplingBridge

/-! Statistical correctness of the actual batch estimator. Label functions may
be arbitrary, including nonmeasurable adversarial choices; the measurable good
location/outlier event is contained in the recovery event for every such label
choice satisfying the inlier bound. -/
namespace Paper34
open Set MeasureTheory
noncomputable section

/-- The estimator's inputs contain neither the truth, sigma, nor outlier flags. -/
def batchEstimate {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho) (T : ℕ)
    (X : Fin M → Point n) (Y : Fin M → ℝ) : PolynomialSpace n d :=
  (runRegression O C (observedGridOfBatch X Y) T).estimate

/-- The source fixed half-open good event supplies the actual deterministic
hypotheses for the same observed batch used by the estimator. -/
theorem batch_error_of_halfOpenGoodEvent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n d m M : ℕ} [NeZero m] {rho eps sigma : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (Y : Fin M → Ω → ℝ)
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (p : PolynomialSpace n d)
    (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hs : 0 ≤ sigma) (hg0 : 0 ≤ C.gamma) (hg : C.gamma ≤ beta eps/(2+beta eps))
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p (S.X i ω)| ≤ sigma)
    {ω : Ω} (hω : ω ∈ halfOpenGoodEvent (m := m) S) :
    supNorm (batchEstimate O C (refinementBudget n d rho eps he0 he)
      (fun i => S.X i ω) (fun i => Y i ω)-p) ≤ (2+eps)*sigma := by
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
      |polyEval p (D.location i)-D.label i| ≤ sigma := by
    intro j i hi hg
    simpa only [D, observedGridOfBatch, abs_sub_comm] using hnoise ω i hg
  exact runRegression_error_on_good_grid O C D hN inlier p hr0 hr he0 he hs hg0 hg hgood hn

/-- Any good-grid probability bound transfers to the recovery event, uniformly
for all permitted adversarial labels and all exact-oracle optimizers. -/
theorem regression_probability_of_good_grid
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d m M : ℕ} [NeZero m] {rho eps sigma delta : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (Y : Fin M → Ω → ℝ)
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (p : PolynomialSpace n d)
    (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hs : 0 ≤ sigma) (hg0 : 0 ≤ C.gamma) (hg : C.gamma ≤ beta eps/(2+beta eps))
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p (S.X i ω)| ≤ sigma)
    (hgoodprob : 1-delta ≤ P.real (halfOpenGoodEvent (m := m) S)) :
    1-delta ≤ P.real {ω | supNorm
      (batchEstimate O C (refinementBudget n d rho eps he0 he)
        (fun i => S.X i ω) (fun i => Y i ω)-p) ≤ (2+eps)*sigma} := by
  apply probability_of_event_containing_halfOpenGoodEvent S hgoodprob
  intro ω hω
  exact batch_error_of_halfOpenGoodEvent S Y O C p hr0 hr he0 he hs hg0 hg hnoise hω

/-- Theorem 1.1, statistical/error portion under product-Chebyshev locations,
with its source mesh and exact finite sample threshold. Every own analytic
module is instantiated; only the three named standard published inputs remain. -/
theorem theorem_1_1_chebyshev_probability
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d m M : ℕ} [NeZero m] {rho eps sigma delta : ℝ}
    (S : GridSamplingModel n M rho P (chebyshevLaw n)) (Y : Fin M → Ω → ℝ)
    (hChernoff : BernoulliLowerHalfInput P M) (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hd : 1 ≤ d) (hMpos : 0 < M) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (he0 : 0 < eps) (he : eps ≤ 1/2) (hdelta0 : 0 < delta) (hdelta : delta ≤ eps)
    (hmesh : arbitraryRepresentativeConstant n*(d : ℝ)/zeta rho ≤ m)
    (hgamma : oscillationFactor n d m ≤ beta eps/6)
    (hM : gridConcentrationConstant rho*(m : ℝ)^n*
      Real.log (2*((m^n : ℕ) : ℝ)/delta) ≤ M)
    (O : ExactRegressionLPOracle n d m) (p : PolynomialSpace n d) (hs : 0 ≤ sigma)
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p (S.X i ω)| ≤ sigma) :
    1-delta ≤ P.real {ω | supNorm
      (batchEstimate O (sourceRegressionAnalysis hBernstein hd hr0 hr he0 he hmesh hgamma)
        (refinementBudget n d rho eps he0 he) (fun i => S.X i ω) (fun i => Y i ω)-p) ≤
          (2+eps)*sigma} := by
  let C := sourceRegressionAnalysis hBernstein hd hr0 hr he0 he hmesh hgamma
  have hgc : C.gamma ≤ beta eps/(2+beta eps) :=
    grid_implies_contraction (by unfold beta; positivity) (by unfold beta; linarith) hgamma
  exact regression_probability_of_good_grid S Y O C p hr0 hr he0 he hs
    (oscillationFactor_nonneg n d m) hgc hnoise (chebyshev_halfOpen_good_grid_probability S hChernoff hHoeffding (NeZero.pos m)
      hMpos hr0 hr hdelta0 (by linarith) hM)

/-- The same source estimator and target error under normalized-uniform
locations. Only the occupancy exponent and sample count change. -/
theorem theorem_1_1_uniform_probability
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d m M : ℕ} [NeZero m] {rho eps sigma delta : ℝ}
    (S : GridSamplingModel n M rho P (uniformLaw n)) (Y : Fin M → Ω → ℝ)
    (hChernoff : BernoulliLowerHalfInput P M) (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hd : 1 ≤ d) (hMpos : 0 < M) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (he0 : 0 < eps) (he : eps ≤ 1/2) (hdelta0 : 0 < delta) (hdelta : delta ≤ eps)
    (hmesh : arbitraryRepresentativeConstant n*(d : ℝ)/zeta rho ≤ m)
    (hgamma : oscillationFactor n d m ≤ beta eps/6)
    (hM : gridConcentrationConstant rho*(m : ℝ)^(2*n)*
      Real.log (2*((m^n : ℕ) : ℝ)/delta) ≤ M)
    (O : ExactRegressionLPOracle n d m) (p : PolynomialSpace n d) (hs : 0 ≤ sigma)
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p (S.X i ω)| ≤ sigma) :
    1-delta ≤ P.real {ω | supNorm
      (batchEstimate O (sourceRegressionAnalysis hBernstein hd hr0 hr he0 he hmesh hgamma)
        (refinementBudget n d rho eps he0 he) (fun i => S.X i ω) (fun i => Y i ω)-p) ≤
          (2+eps)*sigma} := by
  let C := sourceRegressionAnalysis hBernstein hd hr0 hr he0 he hmesh hgamma
  have hgc : C.gamma ≤ beta eps/(2+beta eps) :=
    grid_implies_contraction (by unfold beta; positivity) (by unfold beta; linarith) hgamma
  exact regression_probability_of_good_grid S Y O C p hr0 hr he0 he hs
    (oscillationFactor_nonneg n d m) hgc hnoise (uniform_halfOpen_good_grid_probability S hChernoff hHoeffding (NeZero.pos m)
      hMpos hr0 hr hdelta0 (by linarith) hM)

/-- Zero noise gives exact identity on the same success event. -/
theorem exact_recovery_probability_of_zero_error
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} (output : Ω → PolynomialSpace n d) (p : PolynomialSpace n d) {delta : ℝ}
    (h : 1-delta ≤ P.real {ω | supNorm (output ω-p) ≤ 0}) :
    1-delta ≤ P.real {ω | output ω = p} := by
  apply h.trans (measureReal_mono _)
  intro ω hω
  change supNorm (output ω-p) ≤ 0 at hω
  change output ω = p
  rw [← norm_eq_supNorm] at hω
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hω (norm_nonneg _)))

end
end Paper34
