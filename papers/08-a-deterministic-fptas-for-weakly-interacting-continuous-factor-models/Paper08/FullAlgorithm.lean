import Paper08.ProgramPolynomial
import Paper08.ImplementedAlgorithm
import Paper08.MainTheorem
import Paper08.FPTASDiscreteCost
import Paper08.FPTASDiscretePolynomial

/-! # Polynomial bounds for the actual binary execution and oracle trace

The oracle-time estimate uses the accumulated time at the actual queried
points. Its polynomial is derived from the original effective-access bound.
The numerical exponent of non-oracle arithmetic is independent of the
uniform oracle polynomial's degree.
-/
set_option maxHeartbeats 1200000
namespace Paper08.FullAlgorithm

open ProgramPolynomial

def queryExponent (fixed : Parameters.Fixed) (r c : ℕ) : ℕ :=
  (Parameters.binaryLog ((8*(c+1):ℕ):ℚ)+1)*FPTASCost.queryDegree fixed r c

/-- Increasing polynomial degrees on inputs at least one preserves a bound. -/
lemma monomial_mono {x y : ℚ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (A : ℕ) {d c D C : ℕ} (hd : d ≤ D) (hc : c ≤ C) :
    (A:ℚ)*y^d*x^c ≤ (A:ℚ)*y^D*x^C := by
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy hd) (Nat.cast_nonneg A))
    (pow_le_pow_right₀ hx hc) (pow_nonneg (by linarith) _) (by positivity)

section Model
variable {n m A degree L : ℕ} (p : FPTAS.Params) (fixed : Parameters.Fixed)
variable (hb : FPTASCorrectness.FixedBounds p fixed) (E : FactorFamily n p.r m)
variable (labels : Fin m → ℕ)
variable (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labels e))
variable (hlabels : ∀ e, labels e ≤ L)
variable (hc : FamilyBoundedOccurrence E p.c)
variable (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
variable (hne : FPTASCorrectness.CommonNonvanishing p E)
variable {ε : ℚ} (hn : 1 ≤ n) (hε : 0 < ε) (hεu : ε ≤ 1/2)
variable (hbits : BitComplexity.rationalBits ε ≤ L)
include hb hlabels hc hE hLip hne hn hε hεu hbits

/-- The cost of the verified schoolbook evaluator itself, with no assumed
answer-height or arithmetic-cost certificate. -/
theorem arithmetic_polynomial :
    (ImplementedAlgorithm.arithmeticCost fixed (fun e => (E e).scope)
      (fun e => (O e).valueOracle.query) p.r p.c ε : ℚ) ≤
      arithmeticCoeff fixed p.r p.c A degree *
      ((L:ℚ)+1)^arithmeticEncodingDegree fixed p.r p.c degree *
      ((n:ℚ)/ε)^arithmeticRatioDegree fixed p.r p.c := by
  rw [ImplementedAlgorithm.arithmeticCost, (SchoolbookArithmetic.execute_spec _).2]
  exact (model_program_polynomial p fixed hb E labels O hlabels hc hE hLip hne hn hε hεu hbits).2.2.2

/-- Including the original oracle running time remains polynomial in input
length, n and inverse accuracy. -/
theorem oracle_time_polynomial :
    ((FPTASOracleTime.timedRun (fun e => (E e).scope) (fun e => (E e).psi.toFun)
      labels O fixed p.r p.c ε).2 : ℚ) ≤
      arithmeticCoeff fixed p.r p.c A degree *
      ((L:ℚ)+1)^arithmeticEncodingDegree fixed p.r p.c degree *
      ((n:ℚ)/ε)^(queryExponent fixed p.r p.c + arithmeticRatioDegree fixed p.r p.c) := by
  by_cases hm0 : m = 0
  · simp only [FPTASOracleTime.timedRun, if_pos hm0, Nat.cast_zero]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by have := (Nat.cast_nonneg L : (0:ℚ) ≤ L); linarith) _))
      (pow_nonneg (div_nonneg (Nat.cast_nonneg n) hε.le) _)
  have hm : 1 ≤ m := by omega
  let B : ℚ := arithmeticCoeff fixed p.r p.c A degree *
    ((L:ℚ)+1)^arithmeticEncodingDegree fixed p.r p.c degree *
    ((n:ℚ)/ε)^arithmeticRatioDegree fixed p.r p.c
  have hbnd := (model_numeric_bounds_polynomial p fixed hb E labels O hc hE hLip hne hm hn hε hεu hbits).2
  have hp : FPTASOracleTime.perQueryBound p.r (Parameters.truncationOrder fixed m ε)
      fixed.C A degree L (Parameters.primitiveTolerance fixed m ε) ≤
      FPTASProgram.runInputBound fixed (fun e => (E e).scope)
        (fun e => (O e).valueOracle.query) p.r p.c A degree L ε := by
    unfold FPTASOracleTime.perQueryBound FPTASProgram.runInputBound PrimitiveInputHeight.inputBound
    simp only [Parameters.level, Parameters.precision]
    omega
  have hpB : (FPTASOracleTime.perQueryBound p.r (Parameters.truncationOrder fixed m ε)
      fixed.C A degree L (Parameters.primitiveTolerance fixed m ε) : ℚ) ≤ B :=
    (Nat.cast_le.mpr hp).trans hbnd
  have hq := MainTheorem.query_bound fixed (fun e => (E e).scope) (fun e => (E e).card_le)
    (family_card_le_occurrence_mul_variables E hc) (fun e => (O e).valueOracle.query) hn hε hεu
  have ht := FPTASOracleTime.timedRun_time (fun e => (E e).scope) (fun e => (E e).card_le)
    (fun e => (E e).psi.toFun) labels O hlabels fixed p.c ε
  calc
    _ ≤ ((FPTASCost.runWithCost fixed (fun e => (E e).scope)
          (fun e => (O e).valueOracle.query) p.r p.c ε).2 : ℚ) *
        (FPTASOracleTime.perQueryBound p.r (Parameters.truncationOrder fixed m ε)
          fixed.C A degree L (Parameters.primitiveTolerance fixed m ε) : ℚ) := by exact_mod_cast ht
    _ ≤ ((n:ℚ)/ε)^queryExponent fixed p.r p.c * B :=
      mul_le_mul hq hpB (Nat.cast_nonneg _) (pow_nonneg (div_nonneg (Nat.cast_nonneg n) hε.le) _)
    _ = _ := by dsimp only [B]; rw [pow_add]; ring

end Model

/-- The cached control program and the schoolbook evaluator are one executed
algorithm. Its second component includes non-oracle control and arithmetic. -/
def execute {n m : ℕ} (fixed : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : PrimitiveMomentsQ.Queries scopes) (r c : ℕ) (ε : ℚ) : ℚ × ℕ :=
  FPTASDiscreteCost.implementedRun fixed scopes query r c ε

@[simp] theorem execute_value {n m : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (query : PrimitiveMomentsQ.Queries scopes)
    (r c : ℕ) (ε : ℚ) :
    (execute fixed scopes query r c ε).1 = FPTASAlgorithm.run fixed scopes query r c ε :=
  FPTASDiscreteCost.implementedRun_value fixed scopes query r c ε

/-- Accuracy for every dimension, including the empty instance, is a statement
about the actual implemented answer and the actual partition integral. -/
theorem execute_correct {n m : ℕ} (p : FPTAS.Params) (fixed : Parameters.Fixed)
    (hb : FPTASCorrectness.FixedBounds p fixed) (E : FactorFamily n p.r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hc : FamilyBoundedOccurrence E p.c)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
    (hne : FPTASCorrectness.CommonNonvanishing p E) {ε : ℚ}
    (hε : 0 < ε) (hεu : ε ≤ 1/2) :
    FPTAS.Accurate
      ((execute fixed (fun e => (E e).scope) (fun e => (O e).query) p.r p.c ε).1 : ℝ)
      (Integral.partitionFunctionFactor E) (ε : ℝ) := by
  rw [execute_value]
  exact FPTASCorrectness.run_correct_of_common_nonvanishing p fixed hb E O hc hE hLip hne hε hεu

/-- The empty-factor input returns one with constant non-oracle work; no
accuracy or precision parameter is inspected along this branch. -/
theorem execute_empty (n : ℕ) (fixed : Parameters.Fixed)
    (scopes : Fin 0 → Finset (Fin n)) (query : PrimitiveMomentsQ.Queries scopes)
    (r c : ℕ) (ε : ℚ) : execute fixed scopes query r c ε = (1, 1) := by
  rfl

/-- Accumulated actual oracle time plus the implemented non-oracle trace. -/
def totalWork {n m A degree : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n))
    (Ψ : (i : Fin m) → (Fin (scopes i).card → ℝ) → ℝ) (labels : Fin m → ℕ)
    (O : (i : Fin m) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labels i))
    (r c : ℕ) (ε : ℚ) : ℕ :=
  (execute fixed scopes (fun e => (O e).valueOracle.query) r c ε).2 +
    (FPTASOracleTime.timedRun scopes Ψ labels O fixed r c ε).2

/-- **Theorem 1.2, including the actual implemented bit cost.** Fixed program
constants and the numerical exponent are chosen before all oracle polynomial
parameters and all model inputs. This reusable conditional theorem takes
common nonvanishing explicitly; OriginalTheorems.theorem_1_2 discharges it
from the original factor promises. The empty instance is
handled separately by execute_empty and accuracy holds in every dimension. -/
theorem theorem_1_2_uniform (p : FPTAS.Params) :
    ∃ fixed : Parameters.Fixed, FPTASCorrectness.FixedBounds p fixed ∧
      ∃ C : ℕ, ∀ A degree : ℕ, ∃ B D : ℕ, 0 < B ∧
        ∀ {n m L : ℕ} (E : FactorFamily n p.r m) (labels : Fin m → ℕ)
        (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labels e))
        (_hlabels : ∀ e, labels e ≤ L) (_hc : FamilyBoundedOccurrence E p.c)
        (_hE : ∀ e, (E e).RangeOk p.q) (_hLip : ∀ e, (E e).LipOk p.K)
        (_hne : FPTASCorrectness.CommonNonvanishing p E) {ε : ℚ}
        (_hn : 1 ≤ n) (_hε : 0 < ε) (_hεu : ε ≤ 1/2)
        (_hbits : BitComplexity.rationalBits ε ≤ L),
        FPTAS.Accurate
          ((execute fixed (fun e => (E e).scope) (fun e => (O e).valueOracle.query) p.r p.c ε).1 : ℝ)
          (Integral.partitionFunctionFactor E) (ε : ℝ) ∧
        ((FPTASCost.runWithCost fixed (fun e => (E e).scope)
          (fun e => (O e).valueOracle.query) p.r p.c ε).2 : ℚ) ≤ ((n:ℚ)/ε)^C ∧
        (1 ≤ m → Parameters.level fixed m ε ≤ C*Parameters.inputLog n ε ∧
          Parameters.precision fixed m ε ≤ C*Parameters.inputLog n ε) ∧
        ((execute fixed (fun e => (E e).scope) (fun e => (O e).valueOracle.query) p.r p.c ε).2 : ℚ) ≤
          (B:ℚ)*((L:ℚ)+1)^D*((n:ℚ)/ε)^C ∧
        (totalWork fixed (fun e => (E e).scope) (fun e => (E e).psi.toFun)
          labels O p.r p.c ε : ℚ) ≤ (B:ℚ)*((L:ℚ)+1)^D*((n:ℚ)/ε)^C := by
  obtain ⟨fixed,hb⟩ := CertifiedConstants.exists_fixedBounds p
  obtain ⟨Cd,hd⟩ := FPTASDiscretePolynomial.exists_complete_polynomial p fixed hb
  let C := max (MainTheorem.precisionConstant fixed p.c)
    (max Cd (arithmeticRatioDegree fixed p.r p.c + queryExponent fixed p.r p.c))
  refine ⟨fixed,hb,C,?_⟩
  intro A degree
  obtain ⟨Bd,Dd,hBd,hd⟩ := hd A degree
  let Ba := arithmeticCoeff fixed p.r p.c A degree
  let Da := arithmeticEncodingDegree fixed p.r p.c degree
  let B := 2*Ba+Bd+1
  let D := max Da Dd
  refine ⟨B,D,by dsimp only [B]; omega,?_⟩
  intro n m L E labels O hlabels hc hE hLip hne ε hn hε hεu hbits
  let x : ℚ := (n:ℚ)/ε
  let y : ℚ := (L:ℚ)+1
  have hx : 1 ≤ x := by
    apply (le_div_iff₀ hε).mpr
    have hnq : (1:ℚ) ≤ n := Nat.cast_le.mpr hn
    linarith
  have hy : 1 ≤ y := by dsimp only [y]; have := (Nat.cast_nonneg L : (0:ℚ) ≤ L); linarith
  have hCa : arithmeticRatioDegree fixed p.r p.c ≤ C := by dsimp only [C]; omega
  have hCo : queryExponent fixed p.r p.c + arithmeticRatioDegree fixed p.r p.c ≤ C := by
    dsimp only [C]; omega
  have hCd : Cd ≤ C := by dsimp only [C]; omega
  have hCq : queryExponent fixed p.r p.c ≤ C := by dsimp only [C]; omega
  have hCp : MainTheorem.precisionConstant fixed p.c ≤ C := le_max_left _ _
  have ha := (arithmetic_polynomial p fixed hb E labels O hlabels hc hE hLip hne hn hε hεu hbits).trans
    (monomial_mono hx hy Ba (le_max_left Da Dd) hCa)
  have hctrl := (hd E labels O hlabels hc hE hLip hne hn hε hεu hbits).trans
    (monomial_mono hx hy Bd (le_max_right Da Dd) hCd)
  have ho := (oracle_time_polynomial p fixed hb E labels O hlabels hc hE hLip hne hn hε hεu hbits).trans
    (monomial_mono hx hy Ba (le_max_left Da Dd) hCo)
  have heq : ((execute fixed (fun e => (E e).scope)
      (fun e => (O e).valueOracle.query) p.r p.c ε).2 : ℚ) =
      (ImplementedAlgorithm.arithmeticCost fixed (fun e => (E e).scope)
        (fun e => (O e).valueOracle.query) p.r p.c ε : ℚ)+
      (FPTASDiscreteCost.completeDiscreteWork fixed (fun e => (E e).scope)
        (fun e => (O e).valueOracle.query) p.r p.c ε : ℚ) := by
    simp only [execute,FPTASDiscreteCost.implementedRun,FPTASDiscreteCost.cachedRunProgram_eq,
      ImplementedAlgorithm.arithmeticCost,Nat.cast_add]
  have hcost : ((execute fixed (fun e => (E e).scope)
      (fun e => (O e).valueOracle.query) p.r p.c ε).2 : ℚ) ≤
      ((Ba+Bd:ℕ):ℚ)*y^D*x^C := by
    rw [heq]
    have hh := add_le_add ha hctrl
    convert hh using 1 <;> push_cast <;> ring
  have htotal : (totalWork fixed (fun e => (E e).scope) (fun e => (E e).psi.toFun)
      labels O p.r p.c ε : ℚ) ≤ ((2*Ba+Bd:ℕ):ℚ)*y^D*x^C := by
    unfold totalWork
    rw [Nat.cast_add]
    have hh := add_le_add hcost ho
    convert hh using 1 <;> push_cast <;> ring
  have hmono1 : ((Ba+Bd:ℕ):ℚ)*y^D*x^C ≤ (B:ℚ)*y^D*x^C := by
    apply mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by dsimp only [B]; omega)) (pow_nonneg (by linarith) _))
      (pow_nonneg (by linarith) _)
  have hmono2 : ((2*Ba+Bd:ℕ):ℚ)*y^D*x^C ≤ (B:ℚ)*y^D*x^C := by
    apply mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by dsimp only [B]; omega)) (pow_nonneg (by linarith) _))
      (pow_nonneg (by linarith) _)
  refine ⟨execute_correct p fixed hb E (fun e => (O e).valueOracle) hc hE hLip hne hε hεu,?_,?_,
    hcost.trans hmono1,htotal.trans hmono2⟩
  · exact (MainTheorem.query_bound fixed (fun e => (E e).scope) (fun e => (E e).card_le)
      (family_card_le_occurrence_mul_variables E hc) (fun e => (O e).valueOracle.query) hn hε hεu).trans
      (pow_le_pow_right₀ hx hCq)
  · intro hm
    have hp := MainTheorem.precision_bound fixed hm (family_card_le_occurrence_mul_variables E hc) hε
    exact ⟨hp.1.trans (Nat.mul_le_mul_right _ hCp),hp.2.trans (Nat.mul_le_mul_right _ hCp)⟩

end Paper08.FullAlgorithm
