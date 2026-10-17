import Paper08.LowDegreePolynomial

/-! # One uniform guarantee for the actual degree-one run

The same run supplies the executed output, the actual query count, both
selected precisions, and complete bit work. Its numerical exponent is chosen
before the effective oracle's polynomial parameters.
-/
open scoped BigOperators
namespace Paper08.LowDegreeGuarantee
open Paper08 LowDegreeAlgorithm LowDegreeDiscreteCost LowDegreePolynomial

/-- Fixed coefficient and exponent absorbing the query prefactor. -/
def queryCoefficient (Δ T : ℕ) : ℕ := 2 * Δ + 8 * T + 4

def queryExponent (Δ T : ℕ) : ℕ :=
  (Parameters.binaryLog ((queryCoefficient Δ T : ℕ) : ℚ) + 1) * 3

def meshSlope (T : ℕ) : ℕ := Nat.clog 2 (4 * T) + 1

def answerSlope (Δ U : ℕ) : ℕ :=
  Nat.clog 2 (4 * (2 * Δ) * U ^ (2 * Δ - 1)) + 1

lemma base_order_le_inputLog (n : ℕ) {ε : ℚ} (hε : 0 < ε) :
    dyadicPrecision n ε ≤ Parameters.inputLog n ε := by
  change Parameters.binaryLog ((n : ℚ) / ε) ≤ Parameters.binaryLog (((n + 1 : ℕ) : ℚ) / ε)
  apply Parameters.binaryLog_mono
  apply div_le_div_of_nonneg_right _ hε.le
  push_cast
  linarith

lemma actual_mesh_precision_le (T n : ℕ) {ε : ℚ} (hε : 0 < ε) :
    meshLevel T n ε ≤ meshSlope T * Parameters.inputLog n ε :=
  (selected_precision_le_order (4 * T) n hε).trans
    (Nat.mul_le_mul_left _ (base_order_le_inputLog n hε))

lemma actual_answer_precision_le (Δ U n : ℕ) {ε : ℚ} (hε : 0 < ε) :
    answerBits Δ U n ε ≤ answerSlope Δ U * Parameters.inputLog n ε :=
  (selected_precision_le_order (4 * (2 * Δ) * U ^ (2 * Δ - 1)) n hε).trans
    (Nat.mul_le_mul_left _ (base_order_le_inputLog n hε))

/-- A pure power bound for the actual oracle calls, with no input-dependent
prefactor and with exponent depending only on the fixed model parameters. -/
theorem actual_queries_le_ratio {n r m Δ : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    (T : ℕ) {ε : ℚ} (hn : 1 ≤ n) (hε : 0 < ε) (hεu : ε ≤ 1 / 2) :
    (queryCalls E (meshLevel T n ε) : ℚ) ≤ ((n : ℚ) / ε) ^ queryExponent Δ T := by
  let x : ℚ := (n : ℚ) / ε
  let a := queryCoefficient Δ T
  let M := 2 * (⌈((4 * T * n : ℕ) : ℚ) / ε⌉₊ + 1)
  have hx : (2 : ℚ) ≤ x := by
    apply (le_div_iff₀ hε).mpr
    have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have hnx : (n : ℚ) ≤ x := by
    apply (le_div_iff₀ hε).mpr
    nlinarith [show (0 : ℚ) ≤ n by positivity]
  have hM : (M : ℚ) ≤ ((8 * T + 4 : ℕ) : ℚ) * x := by
    have hc := Nat.ceil_lt_add_one
      (show (0 : ℚ) ≤ ((4 * T * n : ℕ) : ℚ) / ε by positivity)
    have heq : ((4 * T * n : ℕ) : ℚ) / ε = ((4 * T : ℕ) : ℚ) * x := by
      dsimp [x]
      push_cast
      ring
    rw [heq] at hc
    dsimp [M]
    rw [heq]
    push_cast at hc ⊢
    nlinarith
  have haT : 8 * T + 4 ≤ a := by dsimp [a, queryCoefficient]; omega
  have haΔ : 2 * Δ ≤ a := by dsimp [a, queryCoefficient]; omega
  have hMa : (M : ℚ) ≤ (a : ℚ) * x := hM.trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast haT) (by linarith))
  have hq : (queryCalls E (meshLevel T n ε) : ℚ) ≤ (n : ℚ) * (2 * Δ : ℕ) * (M : ℚ) ^ 2 := by
    exact_mod_cast runQ_queryCalls_le E hdeg hocc T ε
  calc
    _ ≤ (n : ℚ) * (2 * Δ : ℕ) * (M : ℚ) ^ 2 := hq
    _ ≤ x * (a : ℚ) * ((a : ℚ) * x) ^ 2 := by gcongr
    _ = ((a : ℚ) * x) ^ 3 := by ring
    _ ≤ _ := MainTheorem.absorb_constant hx (by positivity)

/-- All conclusions refer to the same actual selected run. This proposition
is a conclusion bundle, never an input certificate. -/
def RunGuarantee {n r m A degree : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (Δ U T B D C H : ℕ) (ε : ℚ) : Prop :=
  FPTAS.Accurate
    ((SchoolbookArithmetic.execute (runProgram E (fun e => (O e).valueOracle.query) Δ U T ε)).1 : ℝ)
    (Integral.partitionFunctionFactor E) ε ∧
  (queryCalls E (meshLevel T n ε) : ℝ) ≤ ((n : ℝ) / (ε : ℝ)) ^ C ∧
  meshLevel T n ε ≤ C * Parameters.inputLog n ε ∧
  answerBits Δ U n ε ≤ C * Parameters.inputLog n ε ∧
  (fullActualWork E labelBits O Δ U T ε : ℝ) ≤
    (B : ℝ) * ((H + 1 : ℕ) : ℝ) ^ D * ((n : ℝ) / (ε : ℝ)) ^ C

/-- Appendix A and the degree-one corollary in a single uniform interface.
The same C controls oracle calls, both precisions and complete bit work. -/
theorem lemma_A1_full_guarantee (Δ : ℕ) {U K : ℝ} (hU : 1 < U) (hK : 0 < K) :
    ∃ C : ℕ, ∀ A degree : ℕ, ∃ B D : ℕ, 0 < B ∧ ∀ (n r m H : ℕ) (E : FactorFamily n r m)
      (labelBits : Fin m → ℕ)
      (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e)),
      (∀ e, labelBits e ≤ H) → FamilyPrimalDegreeLe E 1 → FamilyBoundedOccurrence E Δ →
      (∀ e x, x ∈ Integral.cube (E e).scope.card →
        1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U) →
      (∀ e, (E e).LipOk K) → ∀ (ε : ℚ), 1 ≤ n → 0 < ε → ε ≤ 1 / 2 →
      BitComplexity.rationalBits ε ≤ H →
      RunGuarantee E labelBits O Δ (rangeBound U) (lipBudget Δ K U) B D C H ε := by
  obtain ⟨C0, hp⟩ := lemma_A1_uniform_polynomial Δ hU hK
  let C := C0 + queryExponent Δ (lipBudget Δ K U) + meshSlope (lipBudget Δ K U) +
    answerSlope Δ (rangeBound U) + 1
  have hC0 : C0 ≤ C := by dsimp [C]; omega
  have hCq : queryExponent Δ (lipBudget Δ K U) ≤ C := by dsimp [C]; omega
  have hCL : meshSlope (lipBudget Δ K U) ≤ C := by dsimp [C]; omega
  have hCb : answerSlope Δ (rangeBound U) ≤ C := by dsimp [C]; omega
  refine ⟨C, ?_⟩
  intro A degree
  obtain ⟨B, D, hB, hp⟩ := hp A degree
  refine ⟨B, D, hB, ?_⟩
  intro n r m H E labelBits O hlabels hdeg hocc hrange hLip ε hn hε hεu hbits
  obtain ⟨hacc, hwork⟩ := hp n r m H E labelBits O hlabels hdeg hocc hrange hLip ε hn hε hεu hbits
  have hx : (1 : ℝ) ≤ (n : ℝ) / (ε : ℝ) := by
    have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hεur := (Rat.cast_le (K := ℝ)).mpr hεu
    norm_num at hεur
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    apply (le_div_iff₀ hεr).mpr
    linarith
  refine ⟨hacc, ?_, ?_, ?_, ?_⟩
  · have hq : (queryCalls E (meshLevel (lipBudget Δ K U) n ε) : ℝ) ≤
        ((n : ℝ) / (ε : ℝ)) ^ queryExponent Δ (lipBudget Δ K U) := by
      exact_mod_cast actual_queries_le_ratio E hdeg hocc (lipBudget Δ K U) hn hε hεu
    exact hq.trans (pow_le_pow_right₀ hx hCq)
  · exact (actual_mesh_precision_le (lipBudget Δ K U) n hε).trans
      (Nat.mul_le_mul_right _ hCL)
  · exact (actual_answer_precision_le Δ (rangeBound U) n hε).trans
      (Nat.mul_le_mul_right _ hCb)
  · exact hwork.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hC0) (by positivity))

/-- Corollary 1.3's η=1 branch inherits all four conclusions for one run. -/
theorem corollary_1_3_eta_one_full_guarantee (Δ : ℕ) {δ K : ℝ}
    (hρ : 1 < FPTAS.gamarnikSmediraRho Δ 1 δ) (hK : 0 < K) :
    ∃ C : ℕ, ∀ A degree : ℕ, ∃ B D : ℕ, 0 < B ∧ ∀ (n r m H : ℕ) (E : FactorFamily n r m)
      (labelBits : Fin m → ℕ)
      (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e)),
      (∀ e, labelBits e ≤ H) → FamilyPrimalDegreeLe E 1 → FamilyBoundedOccurrence E Δ →
      (∀ e x, x ∈ Integral.cube (E e).scope.card →
        1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ FPTAS.gamarnikSmediraRho Δ 1 δ) →
      (∀ e, (E e).LipOk K) → ∀ (ε : ℚ), 1 ≤ n → 0 < ε → ε ≤ 1 / 2 →
      BitComplexity.rationalBits ε ≤ H →
      RunGuarantee E labelBits O Δ (rangeBound (FPTAS.gamarnikSmediraRho Δ 1 δ))
        (lipBudget Δ K (FPTAS.gamarnikSmediraRho Δ 1 δ)) B D C H ε :=
  lemma_A1_full_guarantee Δ hρ hK

end Paper08.LowDegreeGuarantee
