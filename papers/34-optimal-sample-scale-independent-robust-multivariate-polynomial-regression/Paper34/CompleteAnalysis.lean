import Paper34.MainDeterministic
import Paper34.CosineFourierLift
import Paper34.HaarChebyshev
import Paper34.TensorNorming
import Paper34.ArbitraryRepresentatives

/-! Discharge every internal analytic premise of the source algorithm. The
only external input remaining in this package is the published, fully general
classical trigonometric Bernstein theorem; the paper's norming chain and the
L1-to-sup estimate are proved by actual Fourier convolution. -/
namespace Paper34
noncomputable section

/-- Equation (4.7) for the actual source multivariate polynomial space. -/
theorem polynomial_l1_to_sup (n d : ℕ) : L1ToSup n d := by
  intro q
  obtain ⟨x, hx, hmax⟩ := supNorm_attained q
  let theta : Point n := fun k => Real.arccos (x k)
  have h := TensorNorming.nikolskii (CosineFourierLift.toTrigPolynomial q)
    (TensorNorming.angularPoint theta)
  rw [HaarChebyshev.toTrigPolynomial_haar_l1] at h
  rw [CosineFourierLift.toTrigPolynomial_angular] at h
  have heq : angularEval q theta = polyEval q x := angularEval_arccos q x hx
  rw [heq, Complex.norm_real, Real.norm_eq_abs, hmax] at h
  exact h

/-- The original cell-oscillation factor (2.4). -/
def oscillationFactor (n d m : ℕ) : ℝ := Real.pi*n*d/m

theorem oscillationFactor_nonneg (n d m : ℕ) : 0 ≤ oscillationFactor n d m := by
  unfold oscillationFactor
  positivity

/-- The original mesh hypotheses instantiate all proved analytic modules.
No own-paper norming estimate is assumed as an external input. -/
def sourceRegressionAnalysis
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n d m : ℕ} [NeZero m] {rho eps : ℝ}
    (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hmesh : arbitraryRepresentativeConstant n*(d : ℝ)/zeta rho ≤ m)
    (hgamma : oscillationFactor n d m ≤ beta eps/6) : RegressionAnalysis n d m rho where
  norming := corollary_3_4 hd
    (by dsimp [zeta, alpha]; linarith) (by dsimp [zeta, alpha]; linarith) hmesh
  accuracy_lt_one := by dsimp [zeta, alpha]; linarith
  l1_to_sup := polynomial_l1_to_sup n d
  gamma := oscillationFactor n d m
  gamma_lt_one := by
    have hb : beta eps ≤ 1/24 := by unfold beta; linarith
    linarith
  oscillation := fun q j x z hx hz => lemma_5_1_pointwise hBernstein q (NeZero.pos m) j x z hx hz

/-- Deterministic source guarantee on a mesh satisfying (2.2), with all own
analytic dependencies instantiated, uniformly over labels and oracle choices. -/
theorem source_good_grid_recovery
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n d m M : ℕ} [NeZero m] {rho eps sigma : ℝ}
    (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hmesh : arbitraryRepresentativeConstant n*(d : ℝ)/zeta rho ≤ m)
    (hgamma : oscillationFactor n d m ≤ beta eps/6)
    (O : ExactRegressionLPOracle n d m) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) (inlier : Fin M → Prop) [DecidablePred inlier]
    (p : PolynomialSpace n d) (hs : 0 ≤ sigma)
    (hgood : (D.toGood hN inlier).GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, inlier i → |polyEval p (D.location i)-D.label i| ≤ sigma) :
    supNorm ((runRegression O (sourceRegressionAnalysis hBernstein hd hr0 hr he0 he hmesh hgamma)
      D (refinementBudget n d rho eps he0 he)).estimate-p) ≤ (2+eps)*sigma := by
  apply runRegression_error_on_good_grid O _ D hN inlier p hr0 hr he0 he hs
    (oscillationFactor_nonneg n d m) _ hgood hnoise
  apply grid_implies_contraction (by unfold beta; positivity)
    (by unfold beta; linarith) hgamma

end
end Paper34
