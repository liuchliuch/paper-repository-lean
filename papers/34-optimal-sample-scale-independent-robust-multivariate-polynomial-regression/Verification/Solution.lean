import Paper34
open scoped BigOperators ComplexConjugate
open Set MeasureTheory ProbabilityTheory Paper34
/- Fixed full quantified source contracts. The challenge intentionally contains
proof placeholders and is never imported by the production library or audit.
All whole-library checks and official runs are verification_deferred_by_user. -/
noncomputable section
namespace Verification
section
theorem lemma_5_2 :
    ∀ {n d m : ℕ} {ι : Type*} {I G : Finset ι}
    (j : Paper34.CellIndex n m) (e : Paper34.PolynomialSpace n d)
    (X : ι → Paper34.Point n) (Z : ι → ℝ) {sigma y : ℝ},
    G ⊆ I → I.card < 2*G.card →
    (∀ i ∈ I, X i ∈ Paper34.closedCell j) →
    (∀ i ∈ G, |Z i - Paper34.polyEval e (X i)| ≤ sigma) →
    Paper34.IsSampleMedian I Z y →
    ∃ z ∈ Paper34.closedCell j, |Paper34.polyEval e z-y| ≤ sigma := @Paper34.median_witness
end
section
theorem remark_3_5 :
    ∀ (d : ℕ), 1 ≤ d →
    ∃ q : Polynomial ℝ, q ≠ 0 ∧ q.natDegree ≤ d ∧
      ∃ representatives : Fin d → ℝ,
        (∀ j, representatives j ∈ Paper34.ChebyshevCounterexample.cell d j) ∧
        (∀ j, q.eval (representatives j) = 0) := Paper34.ChebyshevCounterexample.remark_3_5
end
section
theorem uniform_cell_width_lower_bound :
    ∀ (m : ℕ), 1 ≤ m → ∀ j : Fin m,
    ((m : ℝ)⁻¹)^2 ≤
      (Real.cos ((j : ℕ) * Real.pi / m) - Real.cos (((j : ℕ)+1 : ℝ)*Real.pi/m))/2 := Paper34.ChebyshevCounterexample.uniform_cell_width_lower_bound
end
section
theorem finrank_polynomialSpace :
    ∀ (n d : ℕ),
    Module.finrank ℝ (Paper34.PolynomialSpace n d) = (d+1)^n := Paper34.finrank_polynomialSpace
end
section
theorem lp_description_counts :
    ∀ (n d m M : ℕ),
    Fintype.card (Paper34.InitializerVariable n d M) = (d+1)^n + M ∧
    Fintype.card (Paper34.InitializerRow M) = 2*M ∧
    Fintype.card (Paper34.RefinementVariable n d) = (d+1)^n + 1 ∧
    Fintype.card (Paper34.RefinementRow n m) = 2*m^n := Paper34.lp_description_counts
end
section
theorem scalar_target_of_recurrence :
    ∀ (E : ℕ → ℝ) {sigma eps K : ℝ},
    0 ≤ sigma → 0 < eps → eps ≤ 1/2 → E 0 ≤ K*sigma →
    (∀ t, E (t+1) ≤ (2+Paper34.beta eps)*sigma + Paper34.beta eps * E t) →
    ∀ T : ℕ, Paper34.beta eps ^ T * K ≤ eps/2 →
    E T ≤ (2+eps)*sigma := @Paper34.target_of_recurrence
end
section
theorem grid_cover :
    ∀ {n m : ℕ}, 0 < m → ∀ x : Paper34.Point n,
    x ∈ Paper34.cube n → ∃ j : Paper34.CellIndex n m, x ∈ Paper34.closedCell j := @Paper34.cube_covered_by_closedCells
end
section
theorem multiset_cell_representatives :
    ∀ {n d m : ℕ} (q : Paper34.PolynomialSpace n d)
    (A : Paper34.CellIndex n m → Multiset (Paper34.Point n)),
    (∀ j, A j ≠ 0) → (∀ j x, x ∈ A j → x ∈ Paper34.closedCell j) →
    ∃ xi : Paper34.CellIndex n m → Paper34.Point n, ∀ j,
      xi j ∈ Paper34.closedCell j ∧ |Paper34.polyEval q (xi j)| =
        Paper34.multisetAverage (A j) (fun x => |Paper34.polyEval q x|) := by
  intro n d m q A hA hAC
  exact Paper34.mvPolynomial_abs_multiset_representatives Paper34.closedCell A q.1 hA hAC
    Paper34.isCompact_closedCell Paper34.convex_closedCell
end
section
theorem lad_finite_sum_bound :
    ∀ {κ ι : Type*} [Fintype κ] [Nonempty κ] {n d : ℕ}
    (S : κ → Finset ι), (∀ c, (S c).Nonempty) →
    ∀ (X : ι → Paper34.Point n) (Y : ι → ℝ) (p e : Paper34.PolynomialSpace n d)
    (good : ι → Prop) [DecidablePred good] {sigma : ℝ}, 0 ≤ sigma →
    (∀ c, ∀ i ∈ S c, good i → |Paper34.polyEval p (X i)-Y i| ≤ sigma) →
    Paper34.weightedAverage S (fun _ i => if good i then |Paper34.polyEval e (X i)|
      else -|Paper34.polyEval e (X i)|)-2*sigma ≤
      Paper34.weightedLAD S X Y (p+e)-Paper34.weightedLAD S X Y p := @Paper34.lad_signed_mass_lower
end
section
theorem six_observation_counterexample :
    ∀ (K : ℝ), 0 < K →
    Fintype.card (Paper34.LADCounterexample.Cell × Paper34.LADCounterexample.Observation) = 6 ∧
    (∀ j i, Paper34.LADCounterexample.location j i ∈ Paper34.LADCounterexample.chebyshevCell j) ∧
    (∀ j, (Paper34.LADCounterexample.cellSamples j).card = 3 ∧
      (Paper34.LADCounterexample.badCellSamples j).card = 1 ∧
      (Paper34.LADCounterexample.goodCellSamples j).card = 2 ∧
      ((Paper34.LADCounterexample.badCellSamples j).card : ℝ) /
        ((Paper34.LADCounterexample.cellSamples j).card : ℝ) = 1/3) ∧
    (Paper34.LADCounterexample.badIndices.card : ℝ) /
      (Fintype.card Paper34.LADCounterexample.Observation : ℝ) = 1/3 ∧
    Paper34.LADCounterexample.badIndices.card < Paper34.LADCounterexample.goodIndices.card ∧
    (∀ j i, ¬ Paper34.LADCounterexample.corrupted i →
      |Paper34.LADCounterexample.truth.eval (Paper34.LADCounterexample.location j i) -
        Paper34.LADCounterexample.label K j i| ≤ Paper34.LADCounterexample.sigma) ∧
    (Paper34.LADCounterexample.quadratic K).natDegree = 2 ∧
    Paper34.LADCounterexample.quadratic K ≠ Paper34.LADCounterexample.truth ∧
    Paper34.LADCounterexample.weightedLAD K (Paper34.LADCounterexample.quadratic K) = 0 ∧
    Paper34.LADCounterexample.weightedLAD K Paper34.LADCounterexample.truth = K/4 ∧
    0 < Paper34.LADCounterexample.weightedLAD K Paper34.LADCounterexample.truth := Paper34.LADCounterexample.six_observation_counterexample
end
section
theorem lemma_3_1 :
    ∀ (d : ℕ), 1 ≤ d →
    (∀ k : ℤ, k.natAbs ≤ d → fourierCoeff (Paper34.Kernel.valleePoussin d) k = 1) ∧
    (∫ x : Paper34.Kernel.Torus, ‖Paper34.Kernel.valleePoussin d x‖ ∂Paper34.Kernel.haar) ≤ 3 ∧
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => Paper34.Kernel.valleePoussin d (s : Paper34.Kernel.Torus))
      (Paper34.Kernel.valleePoussinDerivative d (t : Paper34.Kernel.Torus)) t) ∧
    (∫ x : Paper34.Kernel.Torus, ‖Paper34.Kernel.valleePoussinDerivative d x‖ ∂Paper34.Kernel.haar)
      ≤ 10*d := Paper34.Kernel.one_dimensional_kernel_bounds
end
section
theorem fejer_source_identity :
    ∀ (N : ℕ), 1 ≤ N → ∀ x : Paper34.Kernel.Torus,
    Paper34.Kernel.fejer N x = ∑ k ∈ Finset.Ioo (-(N : ℤ)) (N : ℤ),
      ((1 : ℂ)-(k.natAbs : ℂ)/N)*fourier k x := Paper34.Kernel.fejer_fourier_expansion
end
section
theorem chebyshev_cell_mass :
    ∀ {n m : ℕ}, 0 < m → ∀ j : Paper34.CellIndex n m,
    Paper34.chebyshevLaw n (Paper34.closedCell j) = ENNReal.ofReal ((m : ℝ)⁻¹ ^ n) := @Paper34.chebyshevLaw_closedCell
end
section
theorem uniform_cell_mass :
    ∀ {n m : ℕ}, 0 < m → ∀ j : Paper34.CellIndex n m,
    ENNReal.ofReal ((m : ℝ)⁻¹ ^ (2*n)) ≤ Paper34.uniformLaw n (Paper34.closedCell j) := @Paper34.uniformLaw_closedCell_lower_bound
end
section
theorem constant_median_error :
    ∀ {ι : Type*} {I G : Finset ι} (Z : ι → ℝ) {p sigma y : ℝ},
    G ⊆ I → I.card < 2*G.card → (∀ i ∈ G, |Z i-p| ≤ sigma) →
    Paper34.IsSampleMedian I Z y → |y-p| ≤ sigma := @Paper34.constant_median_error
end
section
open Paper34.Kernel Paper34.LocalSupremum Paper34.TensorNorming
theorem local_supremum_and_endpoint_Bernstein :
    ∀ {n d m : ℕ} (H : TrigPolynomial n d)
    (hd : 1 ≤ d) (hm : d ≤ m),
    let B : ℝ := (3 + 10 * Real.pi) ^ n + 10 * 3 ^ (n - 1)
    (gridWeight m ^ n * ∑ j : GridIndex n m, cellSup H.toContinuousMap j ≤
      B * ∫ u : TorusN n, ‖H.eval u‖ ∂haarN n) ∧
    (∀ i : Fin n, (∫ x : TorusN n, ‖(H.partial i).eval x‖ ∂haarN n) ≤
      B * d * ∫ u : TorusN n, ‖H.eval u‖ ∂haarN n) := @Paper34.TensorNorming.local_supremum_and_endpoint_Bernstein
end
section
theorem lemma_3_3_dimension_constant :
    ∀ (n : ℕ),
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (d m : ℕ), 1 ≤ d → d ≤ m →
      ∀ (q : PolynomialSpace n d) (xi : CellIndex n m → Point n),
        IsCellRepresentative xi →
          (∫ x, |polyEval q x - representativeStep q xi x| ∂chebyshevLaw n) ≤
            A * (d : ℝ) / m * l1Norm q := @Paper34.lemma_3_3_dimension_constant
end
section
theorem corollary_3_4 :
    ∀ {n d m : ℕ} (hd : 1 ≤ d)
    {zeta : ℝ} (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hmesh : arbitraryRepresentativeConstant n * (d : ℝ) / zeta ≤ m),
    MultisetNorming n d m zeta := @Paper34.corollary_3_4
end
section
theorem polynomial_l1_to_sup :
    ∀ (n d : ℕ),
    L1ToSup n d := @Paper34.polynomial_l1_to_sup
end
section
theorem proposition_4_1 :
    ∀ {n m d : ℕ} [NeZero m] {ι : Type*}
    (D : GoodSampleGrid n m ι) (Y : ι → ℝ) (p : PolynomialSpace n d)
    {rho sigma : ℝ} (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2) (hs : 0 ≤ sigma)
    (hmesh : arbitraryRepresentativeConstant n*(d : ℝ)/zeta rho ≤ m)
    (hgood : D.GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, D.inlier i → |polyEval p (D.location i)-Y i| ≤ sigma),
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
      (sigma = 0 → q = p)) := @Paper34.proposition_4_1
end
section
theorem lemma_5_1 :
    ∀ (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n d m : ℕ} (q : PolynomialSpace n d) (hm : 0 < m) (j : CellIndex n m),
    cellOscillation q j ≤ (Real.pi * n * d / m) * supNorm q := @Paper34.lemma_5_1
end
section
theorem proposition_5_3 :
    ∀ (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n d m M : ℕ} [NeZero m] {rho eps sigma : ℝ}
    (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hmesh : arbitraryRepresentativeConstant n*(d : ℝ)/zeta rho ≤ m)
    (hgamma : oscillationFactor n d m ≤ beta eps/6)
    (O : ExactRegressionLPOracle n d m) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) (inlier : Fin M → Prop) [DecidablePred inlier]
    (p q : PolynomialSpace n d) (hs : 0 ≤ sigma)
    (hgood : (D.toGood hN inlier).GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, inlier i → |polyEval p (D.location i)-D.label i| ≤ sigma),
    supNorm (q+correction O (sourceRegressionAnalysis hBernstein hd hr0 hr he0 he hmesh hgamma)
      D hN q-p) ≤ (2+beta eps)*sigma+beta eps*supNorm (q-p) := @Paper34.proposition_5_3
end
section
theorem random_subset_hoeffding_transfer :
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {M : ℕ} (b : Ω → (Fin M → Bool)) (O : Fin M → Ω → Bool)
    (hb : Measurable b) (hindep : IndepFun b (fun ω i => O i ω) P)
    {rho a r : ℝ}
    (hfixed : ∀ S : Finset (Fin M),
      P.real {ω | a * (S.card : ℝ) < boolCount (fun i => O i ω) S} ≤
        Real.exp (-2 * (a - rho) ^ 2 * (S.card : ℝ))),
    P.real {ω | a * boolCount (b ω) Finset.univ <
        boolCount (fun i => O i ω) (selectedIndices (b ω)) ∧
        r ≤ boolCount (b ω) Finset.univ} ≤
      Real.exp (-2 * (a - rho) ^ 2 * r) := @Paper34.random_subset_hoeffding_transfer
end
section
theorem lemma_6_1_good_product_grid :
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m M : ℕ} {rho δ pmin : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hChernoff : BernoulliLowerHalfInput P M)
    (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hm : 0 < m) (hMpos : 0 < M) (hrho0 : 0 ≤ rho) (hrho : rho < 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hpmin : 0 < pmin)
    (hcell : ∀ j : CellIndex n m, pmin ≤ law.real (closedCell j))
    (hM : gridConcentrationConstant rho * pmin⁻¹ *
      Real.log (2 * ((m ^ n : ℕ) : ℝ) / δ) ≤ M),
    1 - δ ≤ P.real (goodGridEvent (m := m) S) := @Paper34.lemma_6_1_good_product_grid
end
section
theorem halfOpenGoodEvent_ae_eq_closed :
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n m M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hcell : ∀ j : CellIndex n m, halfOpenCell j =ᵐ[law] closedCell j),
    halfOpenGoodEvent (m := m) S =ᵐ[P] goodGridEvent (m := m) S := @Paper34.halfOpenGoodEvent_ae_eq_closed
end
section
open Paper34.ProductChebyshevDensity
theorem source_density_1_1 :
    ∀ (n : ℕ),
    chebyshevLaw n = (volume : Measure (Point n)).withDensity
      ((cube n).indicator (fun x : Point n =>
        ENNReal.ofReal (∏ k, 1 / (Real.pi * Real.sqrt (1 - x k ^ 2))))) := @Paper34.ProductChebyshevDensity.source_density_1_1
end
section
theorem runRegression_calls_le :
    ∀ {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (T : ℕ),
    (runRegression O C D T).oracleCalls ≤ 1+T := @Paper34.runRegression_calls_le
end
section
theorem runRegression_calls_of_nonempty :
    ∀ {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (D : ObservedGrid n m M) (T : ℕ) (hN : ∀ j, (D.samples j).Nonempty),
    (runRegression O C D T).oracleCalls = 1+T := @Paper34.runRegression_calls_of_nonempty
end
section
theorem theorem_1_1_chebyshev :
    ∀ (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} {rho eps sigma delta : ℝ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (hdelta0 : 0 < delta) (hdelta : delta ≤ eps) (he : eps ≤ 1/2)
    (S : GridSamplingModel n (sourceChebyshevSamples n d rho eps delta) rho P (chebyshevLaw n))
    (Y : Fin (sourceChebyshevSamples n d rho eps delta) → Ω → ℝ)
    (O : ExactRegressionLPOracle n d (sourceGrid n d rho eps))
    (p : PolynomialSpace n d) (hs : 0 ≤ sigma)
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p (S.X i ω)| ≤ sigma),
    1-delta ≤ P.real {ω | supNorm
      (batchEstimate O (fixedSourceAnalysis hBernstein hd hr0 hr (hdelta0.trans_le hdelta) he)
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he)
        (fun i => S.X i ω) (fun i => Y i ω)-p) ≤ (2+eps)*sigma} := @Paper34.theorem_1_1_chebyshev
end
section
theorem theorem_1_1_uniform :
    ∀ (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} {rho eps sigma delta : ℝ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (hdelta0 : 0 < delta) (hdelta : delta ≤ eps) (he : eps ≤ 1/2)
    (S : GridSamplingModel n (sourceUniformSamples n d rho eps delta) rho P (uniformLaw n))
    (Y : Fin (sourceUniformSamples n d rho eps delta) → Ω → ℝ)
    (O : ExactRegressionLPOracle n d (sourceGrid n d rho eps))
    (p : PolynomialSpace n d) (hs : 0 ≤ sigma)
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p (S.X i ω)| ≤ sigma),
    1-delta ≤ P.real {ω | supNorm
      (batchEstimate O (fixedSourceAnalysis hBernstein hd hr0 hr (hdelta0.trans_le hdelta) he)
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he)
        (fun i => S.X i ω) (fun i => Y i ω)-p) ≤ (2+eps)*sigma} := @Paper34.theorem_1_1_uniform
end
section
theorem theorem_1_1_uniform_rates :
    ∀ (n : ℕ) (rho : ℝ) (hr0 : 0 ≤ rho) (hr : rho < 1/2),
    ∃ KC KU CT : ℝ, 0 < KC ∧ 0 < KU ∧ 0 < CT ∧
      ∀ (d : ℕ) (eps delta : ℝ) (hd : 1 ≤ d) (hdelta0 : 0 < delta)
        (hdelta : delta ≤ eps) (he : eps ≤ 1/2),
        (sourceChebyshevSamples n d rho eps delta : ℝ) ≤
          KC*((d : ℝ)/eps)^n*Real.log ((d : ℝ)/delta) ∧
        (sourceUniformSamples n d rho eps delta : ℝ) ≤
          KU*((d : ℝ)/eps)^(2*n)*Real.log ((d : ℝ)/delta) ∧
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he : ℝ) ≤
          CT*Real.log ((d : ℝ)/eps) := @Paper34.theorem_1_1_uniform_rates
end
section
theorem theorem_1_1_calls :
    ∀ (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n d M : ℕ} {rho eps : ℝ}
    (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (O : ExactRegressionLPOracle n d (sourceGrid n d rho eps))
    (X : Fin M → Point n) (Y : Fin M → ℝ),
    (runRegression O (fixedSourceAnalysis hBernstein hd hr0 hr he0 he)
      (observedGridOfBatch X Y) (refinementBudget n d rho eps he0 he)).oracleCalls ≤
        1+refinementBudget n d rho eps he0 he := @Paper34.theorem_1_1_calls
end
section
theorem theorem_1_1_chebyshev_exact :
    ∀ (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} {rho eps delta : ℝ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (hdelta0 : 0 < delta) (hdelta : delta ≤ eps) (he : eps ≤ 1/2)
    (S : GridSamplingModel n (sourceChebyshevSamples n d rho eps delta) rho P (chebyshevLaw n))
    (Y : Fin (sourceChebyshevSamples n d rho eps delta) → Ω → ℝ)
    (O : ExactRegressionLPOracle n d (sourceGrid n d rho eps))
    (p : PolynomialSpace n d)
    (hnoise : ∀ ω i, S.O i ω = false → Y i ω = polyEval p (S.X i ω)),
    1-delta ≤ P.real {ω |
      batchEstimate O (fixedSourceAnalysis hBernstein hd hr0 hr (hdelta0.trans_le hdelta) he)
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he)
        (fun i => S.X i ω) (fun i => Y i ω) = p} := @Paper34.theorem_1_1_chebyshev_exact
end
section
theorem theorem_1_1_uniform_exact :
    ∀ (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} {rho eps delta : ℝ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (hdelta0 : 0 < delta) (hdelta : delta ≤ eps) (he : eps ≤ 1/2)
    (S : GridSamplingModel n (sourceUniformSamples n d rho eps delta) rho P (uniformLaw n))
    (Y : Fin (sourceUniformSamples n d rho eps delta) → Ω → ℝ)
    (O : ExactRegressionLPOracle n d (sourceGrid n d rho eps))
    (p : PolynomialSpace n d)
    (hnoise : ∀ ω i, S.O i ω = false → Y i ω = polyEval p (S.X i ω)),
    1-delta ≤ P.real {ω |
      batchEstimate O (fixedSourceAnalysis hBernstein hd hr0 hr (hdelta0.trans_le hdelta) he)
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he)
        (fun i => S.X i ω) (fun i => Y i ω) = p} := @Paper34.theorem_1_1_uniform_exact
end
section
theorem source_other_design_recovery :
    ∀ (hBernstein : TrigBernstein.ClassicalTrigBernstein)
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
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p (S.X i ω)| ≤ sigma),
    1-delta ≤ P.real {ω | supNorm
      (batchEstimate O (fixedSourceAnalysis hBernstein hd hr0 hr he0 he)
        (refinementBudget n d rho eps he0 he) (fun i => S.X i ω) (fun i => Y i ω)-p) ≤
          (2+eps)*sigma} := @Paper34.source_other_design_recovery
end
section
theorem other_design_halfOpen_good_grid_probability_of_threshold :
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m M : ℕ} {rho δ pmin : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hChernoff : BernoulliLowerHalfInput P M) (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hm : 0 < m) (hrho0 : 0 ≤ rho) (hrho : rho < 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hpmin : 0 < pmin)
    (hcell : ∀ j : CellIndex n m, pmin ≤ law.real (halfOpenCell j))
    (hM : gridConcentrationConstant rho * pmin⁻¹ *
      Real.log (2 * ((m ^ n : ℕ) : ℝ) / δ) ≤ M),
    1 - δ ≤ P.real (halfOpenGoodEvent (m := m) S) := @Paper34.other_design_halfOpen_good_grid_probability_of_threshold
end
section
theorem densePolynomial_encoding_complete :
    ∀ {n d : ℕ} (q : PolynomialSpace n d),
    ∃ c : Exponent n d → ℝ, densePolynomial c = q.1 := @Paper34.densePolynomial_encoding_complete
end
section
theorem initializerMatrix_row_iff :
    ∀ {n d M : ℕ} (X : Fin M → Point n)
    (Y : Fin M → ℝ) (v : InitializerVariable n d M → ℝ) (row : InitializerRow M),
    lpRowAction (initializerMatrix X) v row ≤ initializerRHS Y row ↔
      initializerConstraint X Y v row := @Paper34.initializerMatrix_row_iff
end
section
theorem refinementMatrix_row_iff :
    ∀ {n d m : ℕ} (a : CellIndex n m → Point n)
    (y : CellIndex n m → ℝ) (v : RefinementVariable n d → ℝ) (row : RefinementRow n m),
    lpRowAction (refinementMatrix a) v row ≤ refinementRHS y row ↔
      refinementConstraint a y v row := @Paper34.refinementMatrix_row_iff
end
section
theorem initializerMatrix_nonzeros_le :
    ∀ {n d M : ℕ} (X : Fin M → Point n),
    matrixNonzeroCount (initializerMatrix (d := d) X) ≤ 2*M*((d+1)^n+1) ∧
      matrixNonzeroCount (initializerMatrix (d := d) X) ≤ 4*M*(d+1)^n := @Paper34.initializerMatrix_nonzeros_le
end
section
theorem refinementMatrix_nonzeros_le :
    ∀ {n d m : ℕ} (a : CellIndex n m → Point n),
    matrixNonzeroCount (refinementMatrix (d := d) a) ≤ 2*m^n*((d+1)^n+1) ∧
      matrixNonzeroCount (refinementMatrix (d := d) a) ≤ 4*m^n*(d+1)^n := @Paper34.refinementMatrix_nonzeros_le
end
section
theorem batchResidualOperations_le :
    ∀ {n d M : ℕ} (c : Exponent n d → ℝ)
    (X : Fin M → Point n),
    batchResidualOperations c X ≤ (2*n+3)*M*(d+1)^n := @Paper34.batchResidualOperations_le
end
section
theorem gridScanOperations_eq :
    ∀ {n m M : ℕ} (X : Fin M → Point n),
    gridScanOperations (m := m) X = 2*n*M*m^n := @Paper34.gridScanOperations_eq
end
section
theorem enumeratedMedian_spec :
    ∀ {M : ℕ} (I : Finset (Fin M)) (Z : Fin M → ℝ) (hI : I.Nonempty),
    IsSampleMedian I Z (enumeratedMedian I Z hI) := @Paper34.enumeratedMedian_spec
end
section
open Paper34.AppendixSpaces
theorem degree_zero_minimizer_iff_median :
    ∀ {n M : ℕ} (hM : 0 < M)
    (X : Fin M → Point n) (Y : Fin M → ℝ) (q : PolynomialSpace n 0),
    (∀ r : PolynomialSpace n 0, weightedLAD (oneCellSamples n M) X Y q ≤
      weightedLAD (oneCellSamples n M) X Y r) ↔
      IsSampleMedian Finset.univ Y (q.1.coeff 0) := @Paper34.AppendixSpaces.degree_zero_minimizer_iff_median
end
section
open Paper34.AppendixSpaces
theorem totalDegree_dimension :
    ∀ (n d : ℕ),
    Module.finrank ℝ (totalDegreeSubspace n d) = (n+d).choose n := @Paper34.AppendixSpaces.totalDegree_dimension
end
section
open Paper34.AppendixSpaces
theorem runRestricted_error_on_good_grid :
    ∀ {n d m M : ℕ} [NeZero m] {rho eps sigma : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty)
    (inlier : Fin M → Prop) [DecidablePred inlier] (p : R)
    (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hs : 0 ≤ sigma) (hg0 : 0 ≤ C.gamma) (hg : C.gamma ≤ beta eps/(2+beta eps))
    (hgood : (D.toGood hN inlier).GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, inlier i → |polyEval p.1 (D.location i)-D.label i| ≤ sigma),
    supNorm ((runRestricted R O C D (refinementBudget n d rho eps he0 he)).estimate.1-p.1) ≤
      (2+eps)*sigma := @Paper34.AppendixSpaces.runRestricted_error_on_good_grid
end
section
open Paper34.AppendixSpaces
theorem runRestricted_exact_on_good_grid :
    ∀ {n d m M : ℕ} [NeZero m] {rho eps : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty)
    (inlier : Fin M → Prop) [DecidablePred inlier] (p : R)
    (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hg0 : 0 ≤ C.gamma) (hg : C.gamma ≤ beta eps/(2+beta eps))
    (hgood : (D.toGood hN inlier).GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, inlier i → polyEval p.1 (D.location i) = D.label i),
    (runRestricted R O C D (refinementBudget n d rho eps he0 he)).estimate = p := @Paper34.AppendixSpaces.runRestricted_exact_on_good_grid
end
section
open Paper34.ConstantSampling Paper34.AppendixSpaces
theorem appendix_A_1_probability :
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n M : ℕ} {rho sigma delta : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (Y : Fin M → Ω → ℝ)
    (hr0 : 0 ≤ rho) (hr : rho < 1 / 2) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hM : gridConcentrationConstant rho * Real.log (2 / delta) ≤ (M : ℝ))
    (p : PolynomialSpace n 0) (_hs : 0 ≤ sigma)
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω - polyEval p (S.X i ω)| ≤ sigma),
    1 - delta ≤ P.real {ω | supNorm
      (AppendixSpaces.constantEstimator n M (constant_samples_positive hr hdelta hdelta1 hM)
        (fun i => Y i ω) - p) ≤ sigma} := @Paper34.ConstantSampling.appendix_A_1_probability
end
section
open Paper34.ConstantSampling Paper34.AppendixSpaces
theorem appendix_A_1_exact_probability :
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n M : ℕ} {rho delta : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (Y : Fin M → Ω → ℝ)
    (hr0 : 0 ≤ rho) (hr : rho < 1 / 2) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hM : gridConcentrationConstant rho * Real.log (2 / delta) ≤ (M : ℝ))
    (p : PolynomialSpace n 0)
    (hnoise : ∀ ω i, S.O i ω = false → Y i ω = polyEval p (S.X i ω)),
    1 - delta ≤ P.real {ω |
      AppendixSpaces.constantEstimator n M (constant_samples_positive hr hdelta hdelta1 hM)
        (fun i => Y i ω) = p} := @Paper34.ConstantSampling.appendix_A_1_exact_probability
end
section
open Paper34.ConstantSampling Paper34.AppendixSpaces
theorem constant_sample_uniform_rate :
    ∀ (rho : ℝ) (hr : rho < 1 / 2),
    ∃ C : ℝ, 0 < C ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 2 →
      (constantSampleCount rho delta : ℝ) ≤ C * Real.log (1 / delta) := @Paper34.ConstantSampling.constant_sample_uniform_rate
end
section
open Paper34.AnisotropicRepresentatives
theorem anisotropic_dimension_constant :
    ∀ (n : ℕ),
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (d m : Fin n → ℕ) (q : Anisotropic.BoxPolynomial d),
      (∀ i, max 1 (d i) ≤ m i) → ∀ (xi : CellIndex m → Point n),
        (∀ j, xi j ∈ closedCell j) →
          (∫ x, |polyEval q.toUniform x - representativeStep q.toUniform xi x| ∂chebyshevLaw n) ≤
            A * (∑ k, (d k : ℝ) / m k) * l1Norm q.toUniform := @Paper34.AnisotropicRepresentatives.anisotropic_dimension_constant
end
section
open Paper34.AnisotropicRepresentatives
theorem anisotropic_cellOscillation :
    ∀ (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n : ℕ} {d m : Fin n → ℕ} (q : Anisotropic.BoxPolynomial d)
    (hm : ∀ i, 0 < m i) (j : CellIndex m),
    cellOscillation q j ≤ (Real.pi * ∑ k, (d k : ℝ) / m k) * supNorm q.toUniform := @Paper34.AnisotropicRepresentatives.anisotropic_cellOscillation
end
section
open Paper34.SecondaryComparisons
theorem lebesgue_proxy_composition :
    ∀ {E S L A B d m : ℝ} (n : ℕ)
    (hA : 0 ≤ A) (hd : 0 ≤ d) (hm : 0 < m)
    (hproxy : E ≤ (2 : ℝ) ^ n * (A * (d * (n : ℝ) / m) * S))
    (hnorm : S ≤ B * d ^ (2 * n) * L),
    E ≤ ((2 : ℝ) ^ n * A * B * (n : ℝ)) * (d ^ (2 * n + 1) / m) * L := @Paper34.SecondaryComparisons.lebesgue_proxy_composition
end
section
open Paper34.Kernel
theorem fejer_eq_sourceFejerSine :
    ∀ (N : ℕ) (t : ℝ),
    fejer N (t : Torus) = (sourceFejerSine N t : ℂ) := @Paper34.Kernel.fejer_eq_sourceFejerSine
end
section
open Paper34.Kernel
theorem sourceFejerSine_fourier_expansion :
    ∀ (N : ℕ) (hN : 1 ≤ N) (t : ℝ),
    (sourceFejerSine N t : ℂ) =
      ∑ k ∈ Finset.Ioo (-(N : ℤ)) (N : ℤ),
        ((1 : ℂ) - (k.natAbs : ℂ) / N) * fourier k (t : Torus) := @Paper34.Kernel.sourceFejerSine_fourier_expansion
end
section
theorem initializerObjective_eval :
    ∀ {n d m M : ℕ}
    (samples : CellIndex n m → Finset (Fin M)) (v : InitializerVariable n d M → ℝ),
    (∑ col, initializerObjective samples col * v col) =
      ((m^n : ℕ) : ℝ)⁻¹ * ∑ j, ((samples j).card : ℝ)⁻¹ *
        ∑ i ∈ samples j, initSlacks v i := @Paper34.initializerObjective_eval
end
section
theorem nonempty_halfOpen_grid_card_le_samples :
    ∀ {n m M : ℕ}
    (X : Fin M → Point n) (hm : 0 < m)
    (hN : ∀ j : CellIndex n m,
      (Finset.univ.filter (fun i => X i ∈ halfOpenCell j)).Nonempty),
    m^n ≤ M := @Paper34.nonempty_halfOpen_grid_card_le_samples
end
section
theorem source_outside_finite_loop_polynomial :
    ∀ (n : ℕ) (rho : ℝ)
    (hn : 1 ≤ n) (hrho0 : 0 ≤ rho) (hrho : rho < 1/2),
    ∃ K : ℕ, 0 < K ∧ ∀ (A : ℝ) (d : ℕ) (eps : ℝ) (_hd : 1 ≤ d)
      (he0 : 0 < eps) (he : eps ≤ 1/2), 1 ≤ A →
      ∀ (M : ℕ) (X : Fin M → Point n)
        (representatives : CellIndex n (SourceComplexity.gridSize A n d rho eps) → Point n)
        (coefficients : Fin (refinementBudget n d rho eps he0 he) → Exponent n d → ℝ),
        (∀ j : CellIndex n (SourceComplexity.gridSize A n d rho eps),
          (Finset.univ.filter (fun i => X i ∈ halfOpenCell j)).Nonempty) →
        outsideFiniteLoopWork X (fun j => Finset.univ.filter (fun i => X i ∈ halfOpenCell j))
          representatives coefficients ≤ K*M^4 := @Paper34.source_outside_finite_loop_polynomial
end
section
open Paper34.AppendixSpaces
theorem totalDegree_lp_counts :
    ∀ (n d m M : ℕ),
    Fintype.card (RestrictedInitializerVariable (totalDegreeSubspace n d) M) = (n+d).choose n+M ∧
    Fintype.card (InitializerRow M) = 2*M ∧
    Fintype.card (RestrictedRefinementVariable (totalDegreeSubspace n d)) = (n+d).choose n+1 ∧
    Fintype.card (RefinementRow n m) = 2*m^n := @Paper34.AppendixSpaces.totalDegree_lp_counts
end
section
open Paper34.AppendixSpaces
theorem restricted_source_chebyshev :
    ∀ (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} {rho eps sigma delta : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d))
    (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (hdelta0 : 0 < delta) (hdelta : delta ≤ eps) (he : eps ≤ 1/2)
    (S : GridSamplingModel n (sourceChebyshevSamples n d rho eps delta) rho P (chebyshevLaw n))
    (Y : Fin (sourceChebyshevSamples n d rho eps delta) → Ω → ℝ)
    (O : RestrictedLPOracle R (sourceGrid n d rho eps)) (p : R) (hs : 0 ≤ sigma)
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p.1 (S.X i ω)| ≤ sigma),
    1-delta ≤ P.real {ω | supNorm
      ((restrictedBatchEstimate R O (fixedSourceAnalysis hBernstein hd hr0 hr (hdelta0.trans_le hdelta) he)
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he)
        (fun i => S.X i ω) (fun i => Y i ω)).1-p.1) ≤ (2+eps)*sigma} := @Paper34.AppendixSpaces.restricted_source_chebyshev
end
section
open Paper34.AppendixSpaces
theorem restricted_source_uniform :
    ∀ (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} {rho eps sigma delta : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d))
    (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1/2)
    (hdelta0 : 0 < delta) (hdelta : delta ≤ eps) (he : eps ≤ 1/2)
    (S : GridSamplingModel n (sourceUniformSamples n d rho eps delta) rho P (uniformLaw n))
    (Y : Fin (sourceUniformSamples n d rho eps delta) → Ω → ℝ)
    (O : RestrictedLPOracle R (sourceGrid n d rho eps)) (p : R) (hs : 0 ≤ sigma)
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p.1 (S.X i ω)| ≤ sigma),
    1-delta ≤ P.real {ω | supNorm
      ((restrictedBatchEstimate R O (fixedSourceAnalysis hBernstein hd hr0 hr (hdelta0.trans_le hdelta) he)
        (refinementBudget n d rho eps (hdelta0.trans_le hdelta) he)
        (fun i => S.X i ω) (fun i => Y i ω)).1-p.1) ≤ (2+eps)*sigma} := @Paper34.AppendixSpaces.restricted_source_uniform
end
section
open Paper34.AppendixSpaces
theorem restrictedBatchEstimate_totalDegree :
    ∀ {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : RestrictedLPOracle (totalDegreeSubspace n d) m)
    (C : RegressionAnalysis n d m rho) (T : ℕ) (X : Fin M → Point n) (Y : Fin M → ℝ),
    (restrictedBatchEstimate (totalDegreeSubspace n d) O C T X Y).1.1.totalDegree ≤ d := @Paper34.AppendixSpaces.restrictedBatchEstimate_totalDegree
end
section
theorem source_lemma_6_1 :
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m M : ℕ} {rho δ pmin : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hm : 0 < m) (hMpos : 0 < M) (hrho0 : 0 ≤ rho) (hrho : rho < 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hpmin : 0 < pmin)
    (hcell : ∀ j : CellIndex n m, pmin ≤ law.real (closedCell j))
    (hM : gridConcentrationConstant rho * pmin⁻¹ *
      Real.log (2 * ((m ^ n : ℕ) : ℝ) / δ) ≤ M),
    1 - δ ≤ P.real (goodGridEvent (m := m) S) := @Paper34.source_lemma_6_1
end
section
open Paper34.StandardConcentration
theorem bernoulliLowerHalfInput :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (M : ℕ),
    BernoulliLowerHalfInput P M := @Paper34.StandardConcentration.bernoulliLowerHalfInput
end
section
open Paper34.StandardConcentration
theorem bernoulliSubsetHoeffdingInput :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (M : ℕ),
    BernoulliSubsetHoeffdingInput P M := @Paper34.StandardConcentration.bernoulliSubsetHoeffdingInput
end

end Verification
