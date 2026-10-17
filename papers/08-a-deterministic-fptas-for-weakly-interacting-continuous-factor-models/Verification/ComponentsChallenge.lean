import Paper08

noncomputable section
open scoped BigOperators
namespace Paper08.VerifiedComponents

theorem cube_factorization {k l : ℕ}
    (f : (Fin k → ℝ) → ℝ) (g : (Fin l → ℝ) → ℝ) :
    Integral.cubeIntegral (fun x : Fin (k + l) → ℝ =>
      f (Integral.leftCoords k l x) * g (Integral.rightCoords k l x)) =
      Integral.cubeIntegral f * Integral.cubeIntegral g :=
  by
  sorry

theorem euclidean_step_error {k level : ℕ} {f : LocalFunc k} {K : ℝ}
    (hK : 0 ≤ K) (hf : f.LipLe K) {x : Fin k → ℝ} (hx : x ∈ Integral.cube k) :
    |(Dyadic.step f level).toFun x - f.toFun x| ≤
      Real.sqrt k * K * ((2 : ℝ) ^ level)⁻¹ :=
  by
  sorry

theorem dyadic_increment_bound {k r : ℕ} {f : LocalFunc k} {A K : ℝ}
    (hkr : k ≤ r) (hK : 0 ≤ K) (hA : f.BoundBy A) (hf : f.LipLe K)
    (level : ℕ) {x : Fin k → ℝ} (hx : x ∈ Integral.cube k) :
    |(Dyadic.increment f level).toFun x| ≤
      Dyadic.budget r A K * ((2 : ℝ) ^ level)⁻¹ :=
  by
  sorry

theorem factor_intersection_degree {n r m c : ℕ} (E : FactorFamily n r m)
    (hc : FamilyBoundedOccurrence E c) (e : Fin m) :
    (Interaction.graph E).degree e ≤ r * (c - 1) :=
  by
  sorry

theorem connected_support_count {n r m c : ℕ} (E : FactorFamily n r m)
    (hc : FamilyBoundedOccurrence E c) (a : ℕ) :
    (Enumeration.connectedSets (Interaction.graph E) a).card ≤
      m * (4 * max 1 (r * (c - 1))) ^ (a - 1) :=
  by
  sorry

theorem local_coefficient_count {n r m c : ℕ} (E : FactorFamily n r m)
    (hc : FamilyBoundedOccurrence E c) (s : ℕ) :
    (Connected.localCoefficients (Interaction.graph E) s).card ≤
      s * m * Connected.A₀ (r * (c - 1)) ^ s :=
  by
  sorry

theorem primitive_sample_error (P b a : ℕ) (answer : ℚ) (z : ℝ)
    (hz1 : 1 ≤ z) (hz2 : z ≤ 2)
    (herr : |(answer : ℝ) - z| ≤ (2 : ℝ) ^ (-(b : ℝ))) :
    |(Oracle.primitiveSampleQ P a answer : ℝ) - (Real.log z) ^ a| ≤
      (a : ℝ) * ((2 : ℝ) ^ (-(b : ℝ)) + (2 : ℝ) ^ (-(P : ℝ))) +
        (2 : ℝ) ^ (-(P : ℝ)) :=
  by
  sorry

theorem rational_recurrence_denominator (M : ℕ → ℚ) (D : ℕ) (j : ℕ)
    (hD : 1 ≤ D) (hM : ∀ i, 1 ≤ i → i ≤ j → (M i).den ∣ D) :
    (Moments.rationalLogCoeff M j).den ∣ Moments.coefficientDenominator D j :=
  by
  sorry

theorem rational_exponential_accuracy (L ε : ℚ) (hε : 0 < ε) (hεu : ε ≤ 1 / 2) :
    0 < Algorithm.rationalExp L ε ∧
      |Real.log (Algorithm.rationalExp L ε : ℝ) - (L : ℝ)| ≤ (ε : ℝ) / 3 :=
  by
  sorry

theorem bump_integral : ∫ x in (0 : ℝ)..1, Appendix.bump x = 8 / 15 :=
  by
  sorry

theorem support_series_coefficient {α R : Type*} [DecidableEq α] [CommRing R]
    (A : Finset α) (G : MvPowerSeries α R) (d : α →₀ ℕ) :
    MvPowerSeries.coeff d (Support.supportSeries A G) =
      if d.support = A then MvPowerSeries.coeff d G else 0 :=
  by
  sorry

theorem caratheodory_coefficient_bound {f : ℂ → ℂ} {R A : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) R, DifferentiableAt ℂ f z)
    (hzero : f 0 = 0) (hre : ∀ z ∈ Metric.closedBall (0 : ℂ) R, (f z).re ≤ A)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖Analytic.cauchyCoeff f R n‖ ≤ 2 * A * R⁻¹ ^ n :=
  by
  sorry

theorem stored_sample_quadrature_perturbation {n t r J : ℕ}
    (scopes : Fin t → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (f : (i : Fin t) → LocalFunc (scopes i).card) (A K : Fin t → ℝ)
    (hK : ∀ i, 0 ≤ K i) (hA : ∀ i, (f i).BoundBy (A i))
    (hf : ∀ i, (f i).LipLe (K i))
    (samples : (i : Fin t) → ℕ → LocalFunc (scopes i).card)
    (ζ : Fin t → ℝ) (ζmax : ℝ) (hζ : ∀ i, 0 ≤ ζ i) (hζmax : ∀ i, ζ i ≤ ζmax)
    (hprecision : ∀ i, 2 * (J + 1 : ℝ) * ζ i ≤ Dyadic.budget r (A i) (K i))
    (hsamples : ∀ i l, l ≤ J → ∀ y, y ∈ Integral.cube (scopes i).card →
      |(samples i l).toFun (Dyadic.corner l y) - (f i).toFun (Dyadic.corner l y)| ≤ ζ i) :
    |Quadrature.totalLevelRule (Quadrature.storedScopedIncrement scopes samples) J -
        Quadrature.totalLevelRule (Quadrature.scopedIncrement scopes f) J| ≤
      2 * (J + 1 : ℝ) * 3 ^ (t - 1) * (∏ i, Dyadic.budget r (A i) (K i)) *
        (∑ i, ζ i / Dyadic.budget r (A i) (K i)) ∧
    |Quadrature.totalLevelRule (Quadrature.storedScopedIncrement scopes samples) J -
        Quadrature.totalLevelRule (Quadrature.scopedIncrement scopes f) J| ≤
      2 * (t : ℝ) * (J + 1 : ℝ) * 3 ^ (t - 1) *
        (∏ i, Dyadic.budget r (A i) (K i)) * ζmax :=
  by
  sorry

theorem adaptive_exact_query_lower_bound {r m : ℕ} {K U ε : ℝ}
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hK : 0 < K) (hU : 1 < U)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (A : LowerBound.ValuePolicy (LowerBound.BlockQuery m r))
    (hcorrect : LowerBound.BlockAccurate A K U ε)
    (n : ℕ) (z : ℝ)
    (hhalt : A (LowerBound.valueTranscript A (fun _ => 1) n) = .inr z) :
    ((LowerBound.valueTranscript A (fun _ => 1) n).length : ℝ) ≥
      (LowerBound.c0 r K U / (2 * U * ε)) ^ r * (m : ℝ) ^ (r + 1) - m :=
  by
  sorry

theorem actual_multinomial_moments {n r m : ℕ} (E : FactorFamily n r m)
    (B : Finset (Fin m)) {q K : ℝ}
    (hE : ∀ e ∈ B, (E e).RangeOk q) (hLip : ∀ e ∈ B, (E e).LipOk K) (j : ℕ) :
    PrimitiveMomentsQ.multinomialMoment E B j = MomentSeries.realMoment E B j :=
  by
  sorry

theorem actual_connected_support_identity {n r m c s j : ℕ} (E : FactorFamily n r m)
    (hc : FamilyBoundedOccurrence E c) (hj : j ≤ s) :
    ModelSupport.logCoeff E Finset.univ j =
      ∑ AB ∈ FPTASAlgorithm.pairs (fun e => (E e).scope) r c s j,
        (-1 : ℝ) ^ (AB.1.card - AB.2.card) * ModelSupport.logCoeff E AB.2 j :=
  by
  sorry

theorem actual_analytic_formal_log_bridge {n r m : ℕ} (E : FactorFamily n r m)
    (B : Finset (Fin m)) {q K R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hE : ∀ e ∈ B, (E e).RangeOk q) (hLip : ∀ e ∈ B, (E e).LipOk K)
    {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L (Metric.closedBall 0 R)) (hzero : L 0 = 0)
    (hlog : (fun z => Complex.exp (L z)) =ᶠ[nhds 0] ZeroFree.Q E B) (j : ℕ) :
    (ModelSupport.logCoeff E B j : ℂ) = Analytic.cauchyCoeff L R j :=
  by
  sorry

theorem computed_rational_moment_error {n r m s C j : ℕ} (E : FactorFamily n r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (B : Finset (Fin m)) (hB : B.card ≤ s) (hj : j ≤ s) (hs : 1 ≤ s)
    {q K : ℝ} (hq : 0 ≤ q) (hqthird : q < 1/3) (hK : 0 ≤ K)
    (hE : ∀ e, (E e).RangeOk q) (hLip : ∀ e, (E e).LipOk K)
    (hC : 2 ≤ C) (hqC : 2*q ≤ (C : ℝ)) (hKC : 6*Real.sqrt r*K ≤ (C : ℝ))
    (τ : ℚ) (hτ : 0 < τ) :
    |(PrimitiveMomentsQ.momentQ (fun e => (E e).scope) (fun e => (O e).query) B j s C τ : ℝ) -
      MomentSeries.realMoment E B j| ≤ (4 : ℝ)^s*(τ : ℝ) :=
  by
  sorry

theorem constructed_rational_algorithm_accuracy {n m : ℕ} (p : FPTAS.Params)
    (fixed : Parameters.Fixed) (hb : FPTASCorrectness.FixedBounds p fixed)
    (E : FactorFamily n p.r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hc : FamilyBoundedOccurrence E p.c)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
    (hne : FPTASCorrectness.CommonNonvanishing p E) {ε : ℚ}
    (hε : 0 < ε) (hεu : ε ≤ 1/2) :
    FPTAS.Accurate
      (FPTASAlgorithm.run fixed (fun e => (E e).scope) (fun e => (O e).query) p.r p.c ε : ℝ)
      (Integral.partitionFunctionFactor E) (ε : ℝ) :=
  by
  sorry

theorem existence_of_fixed_program_constants (p : FPTAS.Params) :
    ∃ fixed : Parameters.Fixed, FPTASCorrectness.FixedBounds p fixed :=
  by
  sorry

theorem exact_polynomial_query_bound {n m r c : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ e, (scopes e).card ≤ r)
    (hocc : m ≤ c*n) (query : PrimitiveMomentsQ.Queries scopes)
    {ε : ℚ} (hn : 1 ≤ n) (hε : 0 < ε) (hεu : ε ≤ 1/2) :
    ((FPTASCost.runWithCost fixed scopes query r c ε).2 : ℚ) ≤
      ((n : ℚ)/ε)^((Parameters.binaryLog ((8*(c+1):ℕ):ℚ)+1)*
        FPTASCost.queryDegree fixed r c) :=
  by
  sorry

theorem complete_program_refinement {n m : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (query : PrimitiveMomentsQ.Queries scopes)
    (r c : ℕ) (ε : ℚ) :
    (FPTASProgram.runProgram fixed scopes query r c ε).eval =
      FPTASAlgorithm.run fixed scopes query r c ε :=
  by
  sorry

theorem implemented_rational_arithmetic_cost (e : RationalProgram.Expr) :
    SchoolbookArithmetic.exprBitCost e ≤ 10000*e.work :=
  by
  sorry

theorem generic_primitive_precision {s C : ℕ} (hs : 1 ≤ s) (hC : 1 ≤ C)
    (τ : ℚ) (hτ : 0 < τ) :
    let b := Parameters.binaryLog ((4*C:ℕ):ℚ)
    let T := Parameters.binaryLog (1/τ)
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    J ≤ (2*b+4)*(s+T) ∧ P ≤ (3*b+14)*(s+T) :=
  by
  sorry

theorem low_degree_constructed_algorithm {n r m Δ : ℕ} (E : FactorFamily n r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    {U K : ℝ} (hU : 1 < U) (hK : 0 < K)
    (hrange : ∀ e x, x ∈ Integral.cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U)
    (hLip : ∀ e, (E e).LipOk K) (ε : ℚ) (hε : 0 < ε) :
    FPTAS.Accurate
      (LowDegreeAlgorithm.runQ E (fun e => (O e).query) Δ
        (LowDegreeAlgorithm.rangeBound U) (LowDegreeAlgorithm.lipBudget Δ K U) ε : ℝ)
      (Integral.partitionFunctionFactor E) ε :=
  by
  sorry

theorem finite_precision_adaptive_lower_bound {r : ℕ} {K U : ℝ}
    (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (ε : ℝ), 1 ≤ m → 0 < ε → ε ≤ 1 →
      ∀ (A : LowerBound.ValuePolicy (LowerBound.FiniteValueQuery m r)),
        LowerBound.FiniteBlockAccurate A K U ε →
      ∀ (n : ℕ) (z : ℝ), A (LowerBound.valueTranscript A (fun _ => 1) n) = .inr z →
        ((LowerBound.valueTranscript A (fun _ => 1) n).length : ℝ) ≥
          (c/(2*U*ε))^r*(m:ℝ)^(r+1)-m :=
  by
  sorry

theorem constructive_disjoint_surrogate_algorithm {n M r : ℕ}
    (scopes : Fin M → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (hdis : Pairwise fun i j => Disjoint (scopes i) (scopes j))
    (Ψ : (i : Fin M) → LocalFunc (scopes i).card)
    (O : (i : Fin M) → Oracle.Oracle (scopes i).card (Ψ i).toFun)
    {K U : ℝ} (hK : 0 ≤ K) (hLip : ∀ i, (Ψ i).LipLe K)
    (hΨ : ∀ i x, x ∈ Integral.cube (scopes i).card →
      1 ≤ (Ψ i).toFun x ∧ (Ψ i).toFun x ≤ U)
    {T ε : ℚ} (hM : 1 ≤ M) (hT : 0 < T) (hε : 0 < ε)
    (hTK : Real.sqrt r*K ≤ (T : ℝ)) :
    FPTAS.Accurate (GridSurrogate.disjointRuleQ scopes (fun i => (O i).query) T ε : ℝ)
      (Integral.partitionFunction n (fun i => Integral.pullback (scopes i) (Ψ i))) (ε : ℝ) :=
  by
  sorry

theorem primitive_binary_execution_bound {n m r A degree L s C : ℕ}
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (Ψ : (i : Fin m) → (Fin (scopes i).card → ℝ) → ℝ) (labels : Fin m → ℕ)
    (O : (i : Fin m) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labels i))
    (hlabels : ∀ i, labels i ≤ L) (d : Fin m →₀ ℕ) (hd : d.degree ≤ s) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    let N := PrimitiveIntegralProgram.primitiveNodes r s P J
    let H := PrimitiveInputHeight.inputBound A degree L r J P s
    (PrimitiveAlgorithm.execute scopes (fun i => (O i).valueOracle.query) d s C τ).1 =
      PrimitiveMomentsQ.primitiveQ scopes (fun i => (O i).valueOracle.query) d s C τ ∧
    (PrimitiveAlgorithm.execute scopes (fun i => (O i).valueOracle.query) d s C τ).2 ≤
      10000*N*(4*((H+2)*(N+1))+3)^3 :=
  by
  sorry

theorem uniform_low_degree_bit_algorithm (Δ : ℕ) {U K : ℝ} (hU : 1 < U) (hK : 0 < K) :
    ∃ C : ℕ, ∀ A degree : ℕ, ∃ B D : ℕ, 0 < B ∧ ∀ (n r m H : ℕ) (E : FactorFamily n r m)
      (labels : Fin m → ℕ)
      (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labels e)),
      (∀ e, labels e ≤ H) → FamilyPrimalDegreeLe E 1 → FamilyBoundedOccurrence E Δ →
      (∀ e x, x ∈ Integral.cube (E e).scope.card →
        1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U) →
      (∀ e, (E e).LipOk K) → ∀ (ε : ℚ), 1 ≤ n → 0 < ε → ε ≤ 1/2 →
      BitComplexity.rationalBits ε ≤ H →
      FPTAS.Accurate
        ((SchoolbookArithmetic.execute (LowDegreeAlgorithm.runProgram E (fun e => (O e).valueOracle.query)
          Δ (LowDegreeAlgorithm.rangeBound U) (LowDegreeAlgorithm.lipBudget Δ K U) ε)).1 : ℝ)
        (Integral.partitionFunctionFactor E) ε ∧
      (LowDegreePolynomial.fullActualWork E labels O Δ (LowDegreeAlgorithm.rangeBound U)
        (LowDegreeAlgorithm.lipBudget Δ K U) ε : ℝ) ≤
        (B:ℝ)*((H+1:ℕ):ℝ)^D*((n:ℝ)/(ε:ℝ))^C :=
  by
  sorry

theorem uniform_complete_main_algorithm (p : FPTAS.Params) :
    ∃ fixed : Parameters.Fixed, FPTASCorrectness.FixedBounds p fixed ∧
      ∃ C : ℕ, ∀ A degree : ℕ, ∃ B D : ℕ, 0 < B ∧
        ∀ {n m L : ℕ} (E : FactorFamily n p.r m) (labels : Fin m → ℕ)
        (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labels e))
        (_hlabels : ∀ e, labels e ≤ L) (_hc : FamilyBoundedOccurrence E p.c)
        (_hE : ∀ e, (E e).RangeOk p.q) (_hLip : ∀ e, (E e).LipOk p.K)
        {ε : ℚ}
        (_hn : 1 ≤ n) (_hε : 0 < ε) (_hεu : ε ≤ 1/2)
        (_hbits : BitComplexity.rationalBits ε ≤ L),
        FPTAS.Accurate
          ((FullAlgorithm.execute fixed (fun e => (E e).scope)
            (fun e => (O e).valueOracle.query) p.r p.c ε).1 : ℝ)
          (Integral.partitionFunctionFactor E) (ε : ℝ) ∧
        ((FPTASCost.runWithCost fixed (fun e => (E e).scope)
          (fun e => (O e).valueOracle.query) p.r p.c ε).2 : ℚ) ≤ ((n:ℚ)/ε)^C ∧
        (1 ≤ m → Parameters.level fixed m ε ≤ C*Parameters.inputLog n ε ∧
          Parameters.precision fixed m ε ≤ C*Parameters.inputLog n ε) ∧
        ((FullAlgorithm.execute fixed (fun e => (E e).scope)
          (fun e => (O e).valueOracle.query) p.r p.c ε).2 : ℚ) ≤
          (B:ℚ)*((L:ℚ)+1)^D*((n:ℚ)/ε)^C ∧
        (FullAlgorithm.totalWork fixed (fun e => (E e).scope) (fun e => (E e).psi.toFun)
          labels O p.r p.c ε : ℚ) ≤ (B:ℚ)*((L:ℚ)+1)^D*((n:ℚ)/ε)^C :=
  by
  sorry

theorem arbitrary_real_quadrature_value_and_operations {n t r J : ℕ}
    (scopes : Fin t → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (f : (i : Fin t) → LocalFunc (scopes i).card) (ht : 1 ≤ t) :
    (QuadratureRealOperationCount.countedRule scopes f J).1 =
      Quadrature.totalLevelRule (Quadrature.scopedIncrement scopes f) J ∧
    (QuadratureRealOperationCount.countedRule scopes f J).2 ≤
      10*t*(J+t).choose t*2^(r*J) :=
  by
  sorry

theorem original_common_closed_disk {n m : ℕ} (p : FPTAS.Params)
    (E : FactorFamily n p.r m) (hc : FamilyBoundedOccurrence E p.c)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
    (B : Finset (Fin m)) {z : ℂ} (hz : ‖z‖ ≤ FPTAS.beta p) :
    ZeroFree.Q E B z ≠ 0 :=
  by
  sorry

theorem original_implemented_accuracy_all_dimensions {n m : ℕ} (p : FPTAS.Params)
    (fixed : Parameters.Fixed) (hb : FPTASCorrectness.FixedBounds p fixed)
    (E : FactorFamily n p.r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hc : FamilyBoundedOccurrence E p.c)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
    {ε : ℚ} (hε : 0 < ε) (hεu : ε ≤ 1/2) :
    FPTAS.Accurate
      ((FullAlgorithm.execute fixed (fun e => (E e).scope)
        (fun e => (O e).query) p.r p.c ε).1 : ℝ)
      (Integral.partitionFunctionFactor E) (ε : ℝ) :=
  by
  sorry

theorem original_primal_degree_corollary  {Δ η : ℕ} {k δ : ℝ}
    (hΔ : 1 ≤ Δ) (hη : 2 ≤ η) (hk : 0 < k) (hδ : 0 < δ ∧ δ < 1)
    (hρ : 1 < FPTAS.gamarnikSmediraRho Δ η δ) :
    let p := FPTAS.Params.ofGamarnikSmedira hΔ hη hk hδ hρ
    ∃ fixed : Parameters.Fixed, FPTASCorrectness.FixedBounds p fixed ∧
      ∃ C : ℕ, ∀ A degree : ℕ, ∃ B D : ℕ, 0 < B ∧
        ∀ {n r m L : ℕ} (E : FactorFamily n r m) (labels : Fin m → ℕ)
        (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labels e))
        (_hlabels : ∀ e, labels e ≤ L) (_hdegree : FamilyPrimalDegreeLe E η)
        (_hocc : FamilyBoundedOccurrence E Δ)
        (_hrange : ∀ e x, x ∈ Integral.cube (E e).scope.card →
          1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ FPTAS.gamarnikSmediraRho Δ η δ)
        (_hLip : ∀ e, (E e).LipOk k)
        {ε : ℚ} (_hn : 1 ≤ n) (_hε : 0 < ε) (_hεu : ε ≤ 1/2)
        (_hbits : BitComplexity.rationalBits ε ≤ L),
        FPTAS.Accurate
          ((FullAlgorithm.execute fixed (fun e => (E e).scope)
            (fun e => (O e).valueOracle.query) (η+1) Δ ε).1 : ℝ)
          (Integral.partitionFunctionFactor E) (ε : ℝ) ∧
        ((FPTASCost.runWithCost fixed (fun e => (E e).scope)
          (fun e => (O e).valueOracle.query) (η+1) Δ ε).2 : ℚ) ≤ ((n:ℚ)/ε)^C ∧
        (1 ≤ m → Parameters.level fixed m ε ≤ C*Parameters.inputLog n ε ∧
          Parameters.precision fixed m ε ≤ C*Parameters.inputLog n ε) ∧
        ((FullAlgorithm.execute fixed (fun e => (E e).scope)
          (fun e => (O e).valueOracle.query) (η+1) Δ ε).2 : ℚ) ≤
          (B:ℚ)*((L:ℚ)+1)^D*((n:ℚ)/ε)^C ∧
        (FullAlgorithm.totalWork fixed (fun e => (E e).scope) (fun e => (E e).psi.toFun)
          labels O (η+1) Δ ε : ℚ) ≤ (B:ℚ)*((L:ℚ)+1)^D*((n:ℚ)/ε)^C :=
  by
  sorry

end Paper08.VerifiedComponents
