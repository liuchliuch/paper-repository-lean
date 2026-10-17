import Paper34.MainAlgorithm
import Mathlib.Tactic.Module

/-! The deterministic correctness of every actual oracle trajectory, uniformly
over all admissible labels and all minimizers returned by the exact oracle. -/
namespace Paper34
noncomputable section

theorem initialEstimate_optimal {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (hN : ∀ j, (D.samples j).Nonempty) :
    ∀ r : PolynomialSpace n d, weightedLAD D.samples D.location D.label (initialEstimate O C D hN) ≤
      weightedLAD D.samples D.location D.label r :=
  O.solveLAD_optimal M D.samples D.location D.label (initialMinimumExists C D hN)

theorem correction_optimal {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (hN : ∀ j, (D.samples j).Nonempty) (q : PolynomialSpace n d) :
    ∀ r : PolynomialSpace n d,
      representativeResidual (D.representative hN) (D.residualMedians hN q) (correction O C D hN q) ≤
      representativeResidual (D.representative hN) (D.residualMedians hN q) r :=
  O.solveMinimax_optimal _ _ (correctionMinimumExists C D hN q)

/-- Proposition 5.3 for the actual median/optimizer correction chosen by the
algorithm. There is no assumed median witness or assumed contraction. -/
theorem correction_contracts {n d m M : ℕ} [NeZero m] {rho eps sigma : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (hN : ∀ j, (D.samples j).Nonempty)
    (inlier : Fin M → Prop) [DecidablePred inlier] (p q : PolynomialSpace n d)
    (hr : rho < 1/2) (hs : 0 ≤ sigma) (hb : 0 ≤ beta eps)
    (hg0 : 0 ≤ C.gamma) (hg : C.gamma ≤ beta eps/(2+beta eps))
    (hgood : (D.toGood hN inlier).GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, inlier i → |polyEval p (D.location i)-D.label i| ≤ sigma) :
    supNorm (q+correction O C D hN q-p) ≤
      (2+beta eps)*sigma+beta eps*supNorm (q-p) := by
  let E := D.toGood hN inlier
  let Z : Fin M → ℝ := fun i => D.label i-polyEval q (D.location i)
  have hn : ∀ j, ∀ i ∈ E.good j, |Z i-polyEval (p-q) (D.location i)| ≤ sigma := by
    intro j i hi
    have hh := hnoise j i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
    dsimp [Z]
    rw [polyEval_sub]
    rw [show (D.label i-polyEval q (D.location i))-
      (polyEval p (D.location i)-polyEval q (D.location i)) =
      -(polyEval p (D.location i)-D.label i) by ring, abs_neg]
    exact hh
  have hmed : ∀ j, IsSampleMedian (D.samples j) Z (D.residualMedians hN q j) := by
    intro j
    exact enumeratedMedian_spec (D.samples j) Z (hN j)
  have h := refinement_of_oscillation (p-q) (correction O C D hN q) (D.representative hN)
    D.samples E.good D.location Z (D.residualMedians hN q)
    (D.representative_inside hN) (fun j => Finset.filter_subset _ _)
    (E.good_strict_majority hr hgood) D.inside hn hmed C.oscillation
    (correction_optimal O C D hN q) hs hb hg0 hg
  have heq : q+correction O C D hN q-p = correction O C D hN q-(p-q) := by module
  rw [heq]
  have hrev : supNorm (p-q) = supNorm (q-p) := by
    simpa only [← norm_eq_supNorm] using norm_sub_rev p q
  simpa only [hrev] using h

/-- Fixed-budget deterministic recovery on a good sample set. The budget is
specified without p or sigma and the same sample is reused at every iterate. -/
theorem iterationState_error {n d m M : ℕ} [NeZero m] {rho eps sigma : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (hN : ∀ j, (D.samples j).Nonempty)
    (inlier : Fin M → Prop) [DecidablePred inlier] (p : PolynomialSpace n d)
    (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hs : 0 ≤ sigma) (hg0 : 0 ≤ C.gamma) (hg : C.gamma ≤ beta eps/(2+beta eps))
    (hgood : (D.toGood hN inlier).GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, inlier i → |polyEval p (D.location i)-D.label i| ≤ sigma)
    (T : ℕ) (hT : beta eps ^ T * initializationFactor n d rho ≤ eps/2) :
    supNorm ((iterationState O C D hN T).estimate-p) ≤ (2+eps)*sigma := by
  let error : ℕ → ℝ := fun t => supNorm ((iterationState O C D hN t).estimate-p)
  have hinit : error 0 ≤ initializationFactor n d rho*sigma := by
    exact (lad_initializer_error (D.toGood hN inlier) D.label p (initialEstimate O C D hN)
      hr0 hr hs hgood hnoise C.norming C.l1_to_sup (initialEstimate_optimal O C D hN)).2
  have hb : 0 ≤ beta eps := by unfold beta; positivity
  have hstep : ∀ t, error (t+1) ≤ (2+beta eps)*sigma+beta eps*error t := by
    intro t
    exact correction_contracts O C D hN inlier p (iterationState O C D hN t).estimate
      hr hs hb hg0 hg hgood hnoise
  exact target_of_recurrence error hs he0 he hinit hstep T hT

/-- The source least budget (2.7) gives the promised pure multiplicative error. -/
theorem runRegression_error_on_good_grid {n d m M : ℕ} [NeZero m] {rho eps sigma : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (hN : ∀ j, (D.samples j).Nonempty)
    (inlier : Fin M → Prop) [DecidablePred inlier] (p : PolynomialSpace n d)
    (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hs : 0 ≤ sigma) (hg0 : 0 ≤ C.gamma) (hg : C.gamma ≤ beta eps/(2+beta eps))
    (hgood : (D.toGood hN inlier).GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, inlier i → |polyEval p (D.location i)-D.label i| ≤ sigma) :
    supNorm ((runRegression O C D (refinementBudget n d rho eps he0 he)).estimate-p) ≤ (2+eps)*sigma := by
  classical
  simp only [runRegression, dif_pos hN]
  exact iterationState_error O C D hN inlier p hr0 hr he0 he hs hg0 hg hgood hnoise _
    (refinementBudget_spec n d rho eps he0 he)

/-- The same algorithm recovers the exact polynomial at sigma=0. -/
theorem runRegression_exact_on_good_grid {n d m M : ℕ} [NeZero m] {rho eps : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (hN : ∀ j, (D.samples j).Nonempty)
    (inlier : Fin M → Prop) [DecidablePred inlier] (p : PolynomialSpace n d)
    (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hg0 : 0 ≤ C.gamma) (hg : C.gamma ≤ beta eps/(2+beta eps))
    (hgood : (D.toGood hN inlier).GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, inlier i → polyEval p (D.location i) = D.label i) :
    (runRegression O C D (refinementBudget n d rho eps he0 he)).estimate = p := by
  have h := runRegression_error_on_good_grid O C D hN inlier p hr0 hr he0 he (le_refl 0)
    hg0 hg hgood (fun j i hi hg => by simp [hnoise j i hi hg])
  simp only [mul_zero] at h
  rw [← norm_eq_supNorm] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

end
end Paper34
