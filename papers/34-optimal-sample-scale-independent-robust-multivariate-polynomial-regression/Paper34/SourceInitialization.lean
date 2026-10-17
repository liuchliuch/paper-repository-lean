import Paper34.CompleteAnalysis

/-! Proposition 4.1 with all own norming and Nikolskii inputs discharged.
No external theorem argument is needed for LAD initialization. -/
namespace Paper34
noncomputable section

/-- The complete source coercivity, attainment, every-minimizer error bounds,
and exact-zero-noise assertion, under the source mesh constraint. -/
theorem proposition_4_1
    {n m d : ℕ} [NeZero m] {ι : Type*}
    (D : GoodSampleGrid n m ι) (Y : ι → ℝ) (p : PolynomialSpace n d)
    {rho sigma : ℝ} (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2) (hs : 0 ≤ sigma)
    (hmesh : arbitraryRepresentativeConstant n*(d : ℝ)/zeta rho ≤ m)
    (hgood : D.GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, D.inlier i → |polyEval p (D.location i)-Y i| ≤ sigma) :
    (∀ e : PolynomialSpace n d, gap rho/2*l1Norm e-2*sigma ≤
      weightedLAD D.samples D.location Y (p+e)-weightedLAD D.samples D.location Y p) ∧
    Filter.Tendsto (weightedLAD D.samples D.location Y)
      (Filter.cocompact (PolynomialSpace n d)) Filter.atTop ∧
    (∃ q : PolynomialSpace n d, ∀ r : PolynomialSpace n d,
      weightedLAD D.samples D.location Y q ≤ weightedLAD D.samples D.location Y r) ∧
    (∀ q : PolynomialSpace n d, (∀ r : PolynomialSpace n d,
      weightedLAD D.samples D.location Y q ≤ weightedLAD D.samples D.location Y r) →
      l1Norm (q-p) ≤ 4*sigma/gap rho ∧
      supNorm (q-p) ≤ initializationFactor n d rho*sigma ∧
      (sigma = 0 → q = p)) := by
  have hnorm := corollary_3_4 hd
    (by dsimp [zeta, alpha]; linarith : 0 < zeta rho)
    (by dsimp [zeta, alpha]; linarith : zeta rho < 1) hmesh
  have hnik := polynomial_l1_to_sup n d
  refine ⟨fun e => coercive_lad_lower D Y p e hr0 hr hs hgood hnoise hnorm,
    weightedLAD_coercive D Y p hr0 hr hs hgood hnoise hnorm hnik,
    weightedLAD_attains_minimum D Y p hr0 hr hs hgood hnoise hnorm hnik, ?_⟩
  intro q hmin
  have h := lad_initializer_error D Y p q hr0 hr hs hgood hnoise hnorm hnik hmin
  refine ⟨h.1, h.2, ?_⟩
  intro hz
  have hh := h.2
  rw [hz, mul_zero, ← norm_eq_supNorm] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))


/-- Source Proposition 5.3 for the actual residual medians and actual minimax
correction, after instantiating every internal analytic module. -/
theorem proposition_5_3
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n d m M : ℕ} [NeZero m] {rho eps sigma : ℝ}
    (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hmesh : arbitraryRepresentativeConstant n*(d : ℝ)/zeta rho ≤ m)
    (hgamma : oscillationFactor n d m ≤ beta eps/6)
    (O : ExactRegressionLPOracle n d m) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) (inlier : Fin M → Prop) [DecidablePred inlier]
    (p q : PolynomialSpace n d) (hs : 0 ≤ sigma)
    (hgood : (D.toGood hN inlier).GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, inlier i → |polyEval p (D.location i)-D.label i| ≤ sigma) :
    supNorm (q+correction O (sourceRegressionAnalysis hBernstein hd hr0 hr he0 he hmesh hgamma)
      D hN q-p) ≤ (2+beta eps)*sigma+beta eps*supNorm (q-p) := by
  exact correction_contracts O _ D hN inlier p q hr hs
    (by unfold beta; positivity) (oscillationFactor_nonneg n d m)
    (grid_implies_contraction (by unfold beta; positivity) (by unfold beta; linarith) hgamma)
    hgood hnoise

end
end Paper34
