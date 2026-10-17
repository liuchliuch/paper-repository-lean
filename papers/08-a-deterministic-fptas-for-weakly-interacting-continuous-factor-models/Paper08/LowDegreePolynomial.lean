import Paper08.LowDegreeDiscreteCost
import Paper08.ProgramPolynomial

/-! # The literal polynomial-time statement for Appendix A

Fixed parameters are outside the existential polynomial coefficients. Neither
an arity bound nor any cost/output certificate is a premise of the final
algorithm theorem.
-/
open scoped BigOperators
namespace Paper08.LowDegreePolynomial
open Paper08 LowDegreeAlgorithm LowDegreeDiscreteCost

/-- A unary natural expression has a fixed monomial envelope. -/
def PolynomialGrowth (f : ℕ → ℕ) : Prop :=
  ∃ B C : ℕ, ∀ x : ℕ, 1 ≤ x → f x ≤ B * x ^ C

lemma growth_const (a : ℕ) : PolynomialGrowth (fun _ => a) := by
  exact ⟨a, 0, by simp⟩

lemma growth_id : PolynomialGrowth (fun x => x) := by
  exact ⟨1, 1, by simp⟩

lemma growth_add {f g : ℕ → ℕ} (hf : PolynomialGrowth f) (hg : PolynomialGrowth g) :
    PolynomialGrowth (fun x => f x + g x) := by
  obtain ⟨B, C, hf⟩ := hf
  obtain ⟨D, E, hg⟩ := hg
  refine ⟨B + D, C + E, ?_⟩
  intro x hx
  have hc := Nat.pow_le_pow_right hx (Nat.le_add_right C E)
  have he := Nat.pow_le_pow_right hx (Nat.le_add_left E C)
  have h1 := (hf x hx).trans (Nat.mul_le_mul_left B hc)
  have h2 := (hg x hx).trans (Nat.mul_le_mul_left D he)
  nlinarith

lemma growth_mul {f g : ℕ → ℕ} (hf : PolynomialGrowth f) (hg : PolynomialGrowth g) :
    PolynomialGrowth (fun x => f x * g x) := by
  obtain ⟨B, C, hf⟩ := hf
  obtain ⟨D, E, hg⟩ := hg
  refine ⟨B * D, C + E, ?_⟩
  intro x hx
  have hh := Nat.mul_le_mul (hf x hx) (hg x hx)
  simpa only [pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh

lemma growth_pow {f : ℕ → ℕ} (hf : PolynomialGrowth f) (k : ℕ) :
    PolynomialGrowth (fun x => f x ^ k) := by
  obtain ⟨B, C, hf⟩ := hf
  refine ⟨B ^ k, C * k, ?_⟩
  intro x hx
  simpa only [mul_pow, ← pow_mul] using Nat.pow_le_pow_left (hf x hx) k

syntax "prove_growth" : tactic
open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| prove_growth) => do
      let target ← Lean.instantiateMVars (← getMainTarget)
      let f := target.getAppArgs[0]!
      let f ← Lean.Meta.whnf f
      let .lam _ _ body _ := f | throwError "expected a unary natural expression"
      let body := body.headBeta.consumeMData
      if !body.hasLooseBVars then
        evalTactic (← `(tactic| exact growth_const _))
      else if body == .bvar 0 then
        evalTactic (← `(tactic| exact growth_id))
      else if body.isAppOf ``HAdd.hAdd || body.isAppOf ``Add.add || body.isAppOf ``Nat.add then
        evalTactic (← `(tactic| apply growth_add <;> prove_growth))
      else if body.isAppOf ``HMul.hMul || body.isAppOf ``Mul.mul || body.isAppOf ``Nat.mul then
        evalTactic (← `(tactic| apply growth_mul <;> prove_growth))
      else if body.isAppOf ``HPow.hPow || body.isAppOf ``Pow.pow || body.isAppOf ``Nat.pow then
        evalTactic (← `(tactic| apply growth_pow <;> prove_growth))
      else
        throwError "not a fixed natural polynomial: {body}"

/-- The explicit bound with its growing arguments exposed separately. -/
def costBody (Δ A degree U : ℕ) (n m H b L M Q : ℕ) : ℕ :=
  let N := n * (M ^ 2 * ((2 * Δ) * (2 * b + 6) + 2 * L + 3) + 1)
  let B := A * (1 + H + b + 2 * (2 * L + 3)) ^ degree + Nat.clog 2 U + 5
  10000 * (N * (4 * ((B + 2) * (N + 1)) + 3) ^ 3 +
    (n * (2 * Δ) * M ^ 2) * (A * (1 + H + b + 2 * (2 * L + 3)) ^ degree)) +
    discreteBound n m b L (M ^ 2) + 10000 * (2 * expressionControlBound Q (2 * Δ + 8))

lemma fullBitBound_eq_body (n m Δ A degree H U T : ℕ) (ε : ℚ) :
    fullBitBound n m Δ A degree H U T ε = costBody Δ A degree U n m H
      (answerBits Δ U n ε) (meshLevel T n ε)
      (2 * (⌈((4 * T * n : ℕ) : ℚ) / ε⌉₊ + 1)) (parameterHeight n Δ U T ε) := rfl

lemma costBody_mono (Δ A degree U : ℕ) {n m H b L M Q S : ℕ}
    (hn : n ≤ S) (hm : m ≤ S) (hH : H ≤ S) (hb : b ≤ S)
    (hL : L ≤ S) (hM : M ≤ S) (hQ : Q ≤ S) :
    costBody Δ A degree U n m H b L M Q ≤ costBody Δ A degree U S S S S S S S := by
  unfold costBody discreteBound expressionControlBound precisionControlBound
  dsimp only
  gcongr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
lemma costBody_growth (Δ A degree U : ℕ) :
    PolynomialGrowth (fun S => costBody Δ A degree U S S S S S S S) := by
  unfold costBody discreteBound expressionControlBound precisionControlBound
  dsimp only
  prove_growth

/-- A fixed scale simultaneously dominates the coefficient of every quotient
and all fixed logarithmic encoding constants. -/
def fixedScale (Δ U T : ℕ) : ℕ :=
  2 * (4 * T + 4 * (2 * Δ) * U ^ (2 * Δ - 1) + Δ +
    Nat.clog 2 Δ + Nat.clog 2 U + Nat.clog 2 T + 30)

lemma fixedScale_pos (Δ U T : ℕ) : 1 ≤ fixedScale Δ U T := by
  unfold fixedScale
  omega

lemma clog_le_self (N : ℕ) : Nat.clog 2 N ≤ N :=
  (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr Nat.lt_two_pow_self.le

lemma ceil_multiple_ratio (a n : ℕ) {ε : ℚ} (hε : 0 < ε) :
    ⌈((a * n : ℕ) : ℚ) / ε⌉₊ ≤ a * ⌈(n : ℚ) / ε⌉₊ := by
  apply Nat.ceil_le.mpr
  have hh := mul_le_mul_of_nonneg_left (Nat.le_ceil ((n : ℚ) / ε)) (Nat.cast_nonneg a : (0 : ℚ) ≤ a)
  convert hh using 1 <;> push_cast <;> ring

lemma selected_precision_le (a n : ℕ) {ε : ℚ} (hε : 0 < ε) :
    dyadicPrecision (a * n) ε ≤ a * ⌈(n : ℚ) / ε⌉₊ + 1 := by
  have hc := (clog_le_self ⌈((a * n : ℕ) : ℚ) / ε⌉₊).trans (ceil_multiple_ratio a n hε)
  unfold dyadicPrecision
  omega

lemma ratio_ceil_ge_n {n : ℕ} {ε : ℚ} (hε : 0 < ε) (hεu : ε ≤ 1 / 2) :
    n ≤ ⌈(n : ℚ) / ε⌉₊ := by
  have hnq : (n : ℚ) ≤ (n : ℚ) / ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith [show (0 : ℚ) ≤ (n : ℚ) by positivity]
  exact_mod_cast hnq.trans (Nat.le_ceil _)

lemma affine_le_scale {a c R H K : ℕ} (h : a + c ≤ K) :
    a * R + c ≤ K * (H + R + 1) := by
  have ha : a ≤ K := by omega
  have hc : c ≤ K := by omega
  calc
    a * R + c ≤ K * R + K := Nat.add_le_add (Nat.mul_le_mul_right R ha) hc
    _ ≤ K * (H + R + 1) := by nlinarith [Nat.zero_le (K * H)]

/-- Every growing natural argument in the actual cost formula fits a single
fixed multiple of the input encoding and the numerical input ratio. -/
lemma selected_arguments_le {n m H Δ U T : ℕ} {ε : ℚ}
    (hm : m ≤ Δ * n) (hε : 0 < ε) (hεu : ε ≤ 1 / 2)
    (hbits : BitComplexity.rationalBits ε ≤ H) :
    let S := fixedScale Δ U T * (H + ⌈(n : ℚ) / ε⌉₊ + 1)
    n ≤ S ∧ m ≤ S ∧ H ≤ S ∧ answerBits Δ U n ε ≤ S ∧ meshLevel T n ε ≤ S ∧
      2 * (⌈((4 * T * n : ℕ) : ℚ) / ε⌉₊ + 1) ≤ S ∧ parameterHeight n Δ U T ε ≤ S := by
  let R := ⌈(n : ℚ) / ε⌉₊
  let K := fixedScale Δ U T
  have hK := fixedScale_pos Δ U T
  have hn := ratio_ceil_ge_n (n := n) hε hεu
  have hS : H + R + K ≤ K * (H + R + 1) := by
    have hh := Nat.mul_le_mul_right (H + R) hK
    dsimp [K] at hh ⊢
    nlinarith
  have hkm : Δ ≤ K := by dsimp [K, fixedScale]; omega
  have hb := selected_precision_le (4 * (2 * Δ) * U ^ (2 * Δ - 1)) n hε
  have hL := selected_precision_le (4 * T) n hε
  have hM := ceil_multiple_ratio (4 * T) n hε
  have hQ := parameterHeight_le_inputBits n Δ U T ε
  have hcn := clog_le_self n
  have hKb : 4 * (2 * Δ) * U ^ (2 * Δ - 1) + 1 ≤ K := by dsimp [K, fixedScale]; omega
  have hKL : 4 * T + 1 ≤ K := by dsimp [K, fixedScale]; omega
  have hKM : 2 * (4 * T) + 2 ≤ K := by dsimp [K, fixedScale]; omega
  have hKQ : Nat.clog 2 Δ + Nat.clog 2 U + Nat.clog 2 T + 17 ≤ K := by
    dsimp [K, fixedScale]; omega
  change n ≤ K * (H + R + 1) ∧ _
  dsimp only [answerBits, meshLevel] at *
  change n ≤ R at hn
  change dyadicPrecision (4 * (2 * Δ) * U ^ (2 * Δ - 1) * n) ε ≤ _ at hb
  change dyadicPrecision (4 * T * n) ε ≤ _ at hL
  have hm' := hm.trans (Nat.mul_le_mul_left Δ hn)
  have hm'' := Nat.mul_le_mul hkm (show R ≤ H + R + 1 by omega)
  have hb' := affine_le_scale (R := R) (H := H) hKb
  have hL' := affine_le_scale (R := R) (H := H) hKL
  have hM' := affine_le_scale (R := R) (H := H) hKM
  have hbase := Nat.mul_le_mul_right (H + R + 1) hK
  dsimp only [R, K] at *
  constructor
  · omega
  constructor
  · exact hm'.trans hm''
  constructor
  · omega
  constructor
  · exact hb.trans hb'
  constructor
  · exact hL.trans hL'
  constructor
  · nlinarith only [hM, hM']
  · omega

lemma scale_le_ratio {n H Δ U T : ℕ} {ε : ℚ}
    (hn : 1 ≤ n) (hε : 0 < ε) (hεu : ε ≤ 1 / 2) :
    ((fixedScale Δ U T * (H + ⌈(n : ℚ) / ε⌉₊ + 1) : ℕ) : ℚ) ≤
      ((3 * fixedScale Δ U T : ℕ) : ℚ) * ((H + 1 : ℕ) : ℚ) * ((n : ℚ) / ε) := by
  have hr : (2 : ℚ) ≤ (n : ℚ) / ε := by
    apply (le_div_iff₀ hε).mpr
    have hnq : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have hc := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ (n : ℚ) / ε by positivity)
  have hh : (H : ℚ) + (⌈(n : ℚ) / ε⌉₊ : ℚ) + 1 ≤
      3 * ((H : ℚ) + 1) * ((n : ℚ) / ε) := by
    nlinarith [mul_nonneg (show (0 : ℚ) ≤ H by positivity)
      (show (0 : ℚ) ≤ (n : ℚ) / ε - 1 by linarith)]
  have hs := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (fixedScale Δ U T) :
    (0 : ℚ) ≤ fixedScale Δ U T)
  convert hs using 1 <;> push_cast <;> ring

/-- The literal fixed-polynomial upper bound: B,D,C depend only on the fixed
parameters, and are chosen before every original input n,m,H,ε. -/
theorem fullBitBound_polynomial (Δ U T A degree : ℕ) :
    ∃ B D C : ℕ, 0 < B ∧ ∀ (n m H : ℕ) (ε : ℚ),
      1 ≤ n → m ≤ Δ * n → 0 < ε → ε ≤ 1 / 2 → BitComplexity.rationalBits ε ≤ H →
      (fullBitBound n m Δ A degree H U T ε : ℚ) ≤
        (B : ℚ) * ((H + 1 : ℕ) : ℚ) ^ D * ((n : ℚ) / ε) ^ C := by
  obtain ⟨B, C, hgrowth⟩ := costBody_growth Δ A degree U
  let K := fixedScale Δ U T
  have hK : 1 ≤ K := fixedScale_pos Δ U T
  refine ⟨(B + 1) * (3 * K) ^ C, C, C, by positivity, ?_⟩
  intro n m H ε hn hm hε hεu hbits
  let S := K * (H + ⌈(n : ℚ) / ε⌉₊ + 1)
  have hS : 1 ≤ S := by dsimp [S]; nlinarith
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := selected_arguments_le hm hε hεu hbits
  have hcost : fullBitBound n m Δ A degree H U T ε ≤ B * S ^ C := by
    rw [fullBitBound_eq_body]
    exact (costBody_mono Δ A degree U h1 h2 h3 h4 h5 h6 h7).trans (hgrowth S hS)
  have hcostq : (fullBitBound n m Δ A degree H U T ε : ℚ) ≤ (B : ℚ) * (S : ℚ) ^ C := by
    exact_mod_cast hcost
  have hscale : (S : ℚ) ≤ ((3 * K : ℕ) : ℚ) * ((H + 1 : ℕ) : ℚ) * ((n : ℚ) / ε) :=
    scale_le_ratio hn hε hεu
  calc
    _ ≤ (B : ℚ) * (S : ℚ) ^ C := hcostq
    _ ≤ ((B + 1 : ℕ) : ℚ) *
        (((3 * K : ℕ) : ℚ) * ((H + 1 : ℕ) : ℚ) * ((n : ℚ) / ε)) ^ C := by
      apply mul_le_mul (by norm_num) (pow_le_pow_left₀ (by positivity) hscale C) (by positivity) (by positivity)
    _ = _ := by push_cast; simp only [mul_pow]; ring

/-- The same polynomial bound over the real input ratio. -/
theorem fullBitBound_polynomial_real (Δ U T A degree : ℕ) :
    ∃ B D C : ℕ, 0 < B ∧ ∀ (n m H : ℕ) (ε : ℚ),
      1 ≤ n → m ≤ Δ * n → 0 < ε → ε ≤ 1 / 2 → BitComplexity.rationalBits ε ≤ H →
      (fullBitBound n m Δ A degree H U T ε : ℝ) ≤
        (B : ℝ) * ((H + 1 : ℕ) : ℝ) ^ D * ((n : ℝ) / (ε : ℝ)) ^ C := by
  obtain ⟨B, D, C, hB, hp⟩ := fullBitBound_polynomial Δ U T A degree
  refine ⟨B, D, C, hB, ?_⟩
  intro n m H ε hn hm hε hεu hbits
  exact_mod_cast hp n m H ε hn hm hε hεu hbits

/-- A nonnegative ceiling computed by the actual binary floor kernel. -/
def actualCeil (x : ℚ) : ℕ := (-(SchoolbookArithmetic.floorKernel (-x)).1).toNat

@[simp] theorem actualCeil_eq (x : ℚ) : actualCeil x = ⌈x⌉₊ := by
  simp [actualCeil, SchoolbookArithmetic.floorKernel_value, Int.floor_neg, Int.ceil_toNat]

/-- These are precisely the two previously uncharged true ceiling kernels. -/
def extraCeilWork (n Δ U T : ℕ) (ε : ℚ) : ℕ :=
  (SchoolbookArithmetic.floorKernel (-(meshArgument n T ε).eval)).2 +
    (SchoolbookArithmetic.floorKernel (-(answerArgument n Δ U ε).eval)).2

def actualSelectionWork (n Δ U T : ℕ) (ε : ℚ) : ℕ :=
  binarySelectionWork n Δ U T ε + extraCeilWork n Δ U T ε

lemma floorKernel_le_precisionControl (x : ℚ) :
    (SchoolbookArithmetic.floorKernel (-x)).2 ≤ 10000 * precisionControl x := by
  have hk := SchoolbookArithmetic.floorKernel_cost_le (-x)
  have hneg : BitComplexity.rationalBits (-x) = BitComplexity.rationalBits x := by
    simp [BitComplexity.rationalBits]
  rw [hneg] at hk
  apply hk.trans
  apply Nat.mul_le_mul_left 10000
  dsimp only [precisionControl]
  omega

lemma extraCeilWork_le (n Δ U T : ℕ) (ε : ℚ) :
    extraCeilWork n Δ U T ε ≤ 10000 * precisionSelectionBound n Δ U T ε := by
  have hm := floorKernel_le_precisionControl (meshArgument n T ε).eval
  have ha := floorKernel_le_precisionControl (answerArgument n Δ U ε).eval
  have hp := precisionSelectionWork_le n Δ U T ε
  unfold precisionSelectionWork expressionControlWork at hp
  unfold extraCeilWork
  nlinarith

lemma actualSelectionWork_le (n Δ U T : ℕ) (ε : ℚ) :
    actualSelectionWork n Δ U T ε ≤ 20000 * precisionSelectionBound n Δ U T ε := by
  have hb := binarySelectionWork_le n Δ U T ε
  have hc := extraCeilWork_le n Δ U T ε
  unfold actualSelectionWork
  omega

/-- Full executed arithmetic and discrete work, including both actual binary
ceiling kernels as well as the existing conservative integer-control scans. -/
def fullActualWork {n r m A degree : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (Δ U T : ℕ) (ε : ℚ) : ℕ :=
  fullBitWork E labelBits O Δ U T ε + extraCeilWork n Δ U T ε

/-- The extra true kernels only double the previous explicit envelope. -/
theorem fullActualWork_le {n r m Δ A degree H : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ H) (hdeg : FamilyPrimalDegreeLe E 1)
    (hocc : FamilyBoundedOccurrence E Δ) (U T : ℕ) (ε : ℚ) :
    fullActualWork E labelBits O Δ U T ε ≤ 2 * fullBitBound n m Δ A degree H U T ε := by
  have hb := fullBitWork_le E labelBits O hlabels hdeg hocc U T ε
  have hc := extraCeilWork_le n Δ U T ε
  have hs : 10000 * precisionSelectionBound n Δ U T ε ≤ fullBitBound n m Δ A degree H U T ε := by
    dsimp only [fullBitBound]
    omega
  unfold fullActualWork
  omega

/-- Lemma A.1 in the original polynomial form, uniformly in all arities and
all inputs. The output is the actual binary-kernel execution result. -/
theorem lemma_A1_polynomial (Δ A degree : ℕ) {U K : ℝ} (hU : 1 < U) (hK : 0 < K) :
    ∃ B D C : ℕ, 0 < B ∧ ∀ (n r m H : ℕ) (E : FactorFamily n r m)
      (labelBits : Fin m → ℕ)
      (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e)),
      (∀ e, labelBits e ≤ H) → FamilyPrimalDegreeLe E 1 → FamilyBoundedOccurrence E Δ →
      (∀ e x, x ∈ Integral.cube (E e).scope.card →
        1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U) →
      (∀ e, (E e).LipOk K) → ∀ (ε : ℚ), 1 ≤ n → 0 < ε → ε ≤ 1 / 2 →
      BitComplexity.rationalBits ε ≤ H →
      FPTAS.Accurate
        ((SchoolbookArithmetic.execute (runProgram E (fun e => (O e).valueOracle.query)
          Δ (rangeBound U) (lipBudget Δ K U) ε)).1 : ℝ)
        (Integral.partitionFunctionFactor E) ε ∧
      (fullActualWork E labelBits O Δ (rangeBound U) (lipBudget Δ K U) ε : ℝ) ≤
        (B : ℝ) * ((H + 1 : ℕ) : ℝ) ^ D * ((n : ℝ) / (ε : ℝ)) ^ C := by
  obtain ⟨B, D, C, hB, hp⟩ := fullBitBound_polynomial_real Δ (rangeBound U) (lipBudget Δ K U) A degree
  refine ⟨2 * B, D, C, by positivity, ?_⟩
  intro n r m H E labelBits O hlabels hdeg hocc hrange hLip ε hn hε hεu hbits
  have ha := lemma_A1_bit_algorithm E labelBits O hlabels hdeg hocc hU hK hrange hLip ε hε
  refine ⟨ha.1, ?_⟩
  have hm := family_card_le_occurrence_mul_variables E hocc
  have hc : (fullActualWork E labelBits O Δ (rangeBound U) (lipBudget Δ K U) ε : ℝ) ≤
      2 * (fullBitBound n m Δ A degree H (rangeBound U) (lipBudget Δ K U) ε : ℝ) := by
    exact_mod_cast fullActualWork_le E labelBits O hlabels hdeg hocc (rangeBound U) (lipBudget Δ K U) ε
  calc
    _ ≤ 2 * (fullBitBound n m Δ A degree H (rangeBound U) (lipBudget Δ K U) ε : ℝ) := hc
    _ ≤ 2 * ((B : ℝ) * ((H + 1 : ℕ) : ℝ) ^ D * ((n : ℝ) / (ε : ℝ)) ^ C) :=
      mul_le_mul_of_nonneg_left (hp n m H ε hn hm hε hεu hbits) (by norm_num)
    _ = _ := by push_cast; ring

/-- The η=1 branch inherits the uniform polynomial directly. -/
theorem corollary_1_3_eta_one_polynomial (Δ A degree : ℕ) {δ K : ℝ}
    (hρ : 1 < FPTAS.gamarnikSmediraRho Δ 1 δ) (hK : 0 < K) :
    ∃ B D C : ℕ, 0 < B ∧ ∀ (n r m H : ℕ) (E : FactorFamily n r m)
      (labelBits : Fin m → ℕ)
      (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e)),
      (∀ e, labelBits e ≤ H) → FamilyPrimalDegreeLe E 1 → FamilyBoundedOccurrence E Δ →
      (∀ e x, x ∈ Integral.cube (E e).scope.card →
        1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ FPTAS.gamarnikSmediraRho Δ 1 δ) →
      (∀ e, (E e).LipOk K) → ∀ (ε : ℚ), 1 ≤ n → 0 < ε → ε ≤ 1 / 2 →
      BitComplexity.rationalBits ε ≤ H →
      FPTAS.Accurate
        ((SchoolbookArithmetic.execute (runProgram E (fun e => (O e).valueOracle.query) Δ
          (rangeBound (FPTAS.gamarnikSmediraRho Δ 1 δ))
          (lipBudget Δ K (FPTAS.gamarnikSmediraRho Δ 1 δ)) ε)).1 : ℝ)
        (Integral.partitionFunctionFactor E) ε ∧
      (fullActualWork E labelBits O Δ (rangeBound (FPTAS.gamarnikSmediraRho Δ 1 δ))
        (lipBudget Δ K (FPTAS.gamarnikSmediraRho Δ 1 δ)) ε : ℝ) ≤
        (B : ℝ) * ((H + 1 : ℕ) : ℝ) ^ D * ((n : ℝ) / (ε : ℝ)) ^ C :=
  lemma_A1_polynomial Δ A degree hρ hK

/-- Expose the oracle magnitude as one independent input. All remaining
expression powers are fixed, independently of the effective oracle degree. -/
def reducedBody (Δ U : ℕ) (n m b L M Q O : ℕ) : ℕ :=
  let N := n * (M ^ 2 * ((2 * Δ) * (2 * b + 6) + 2 * L + 3) + 1)
  let B := O + Nat.clog 2 U + 5
  10000 * (N * (4 * ((B + 2) * (N + 1)) + 3) ^ 3 + (n * (2 * Δ) * M ^ 2) * O) +
    discreteBound n m b L (M ^ 2) + 10000 * (2 * expressionControlBound Q (2 * Δ + 8))

lemma costBody_eq_reduced (Δ A degree U n m H b L M Q : ℕ) :
    costBody Δ A degree U n m H b L M Q = reducedBody Δ U n m b L M Q
      (A * (1 + H + b + 2 * (2 * L + 3)) ^ degree) := rfl

lemma reducedBody_mono (Δ U : ℕ) {n m b L M Q O S : ℕ}
    (hn : n ≤ S) (hm : m ≤ S) (hb : b ≤ S) (hL : L ≤ S)
    (hM : M ≤ S) (hQ : Q ≤ S) (hO : O ≤ S) :
    reducedBody Δ U n m b L M Q O ≤ reducedBody Δ U S S S S S S S := by
  unfold reducedBody discreteBound expressionControlBound precisionControlBound
  dsimp only
  gcongr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
lemma reducedBody_growth (Δ U : ℕ) :
    PolynomialGrowth (fun S => reducedBody Δ U S S S S S S S) := by
  unfold reducedBody discreteBound expressionControlBound precisionControlBound
  dsimp only
  prove_growth

/-- A coefficient in the argument changes the logarithmic precision by only
a fixed multiple of the base logarithmic order. -/
lemma selected_precision_le_order (a n : ℕ) {ε : ℚ} (hε : 0 < ε) :
    dyadicPrecision (a * n) ε ≤ (Nat.clog 2 a + 1) * dyadicPrecision n ε := by
  let N := ⌈(n : ℚ) / ε⌉₊
  let s := dyadicPrecision n ε
  have hs : 1 ≤ s := dyadicPrecision_pos n ε
  have hn : N ≤ 2 ^ s := (Nat.le_pow_clog (by decide : 1 < 2) N).trans
    (Nat.pow_le_pow_right (by decide) (show Nat.clog 2 N ≤ s from le_max_right _ _))
  have ha := Nat.le_pow_clog (by decide : 1 < 2) a
  have hc : ⌈((a * n : ℕ) : ℚ) / ε⌉₊ ≤ 2 ^ (Nat.clog 2 a + s) := by
    apply (ceil_multiple_ratio a n hε).trans
    have hh := Nat.mul_le_mul ha hn
    simpa only [pow_add] using hh
  have hlog := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hc
  have hp := Nat.mul_le_mul_left (Nat.clog 2 a) hs
  change max 1 _ ≤ _
  exact max_le (by nlinarith) (by nlinarith)

lemma ratio_order_pow_le {n : ℕ} {ε : ℚ} (hn : 1 ≤ n) (hε : 0 < ε) (hεu : ε ≤ 1 / 2) :
    (2 : ℚ) ^ dyadicPrecision n ε ≤ 4 * ((n : ℚ) / ε) := by
  have hr : (2 : ℚ) ≤ (n : ℚ) / ε := by
    apply (le_div_iff₀ hε).mpr
    have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have hp := dyadicPrecision_pow_le n ε
  have hpq : (2 : ℚ) ^ dyadicPrecision n ε ≤ 2 * ((⌈(n : ℚ) / ε⌉₊ : ℚ) + 1) := by
    exact_mod_cast hp
  have hc := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ (n : ℚ) / ε by positivity)
  linarith

/-- Absorb the oracle's fixed polynomial degree into its coefficient and the
input-length power; the numerical ratio receives just one power. -/
lemma oracle_power_split {n H Δ U T A degree : ℕ} {ε : ℚ}
    (hn : 1 ≤ n) (hε : 0 < ε) (hεu : ε ≤ 1 / 2) :
    ((A * (1 + H + answerBits Δ U n ε + 2 * (2 * meshLevel T n ε + 3)) ^ degree : ℕ) : ℚ) ≤
      ((4 * ProgramPolynomial.splitLeafCoeff A degree 2 (Nat.clog 2 (4 * T) + 1)
        (Nat.clog 2 (4 * (2 * Δ) * U ^ (2 * Δ - 1)) + 1) 0 : ℕ) : ℚ) *
        ((H + 1 : ℕ) : ℚ) ^ (degree + 1) * ((n : ℚ) / ε) := by
  let s := dyadicPrecision n ε
  let a := Nat.clog 2 (4 * T) + 1
  let b := Nat.clog 2 (4 * (2 * Δ) * U ^ (2 * Δ - 1)) + 1
  have hL : meshLevel T n ε ≤ a * s := selected_precision_le_order (4 * T) n hε
  have hb : answerBits Δ U n ε ≤ b * s := selected_precision_le_order _ n hε
  have hr : (1 : ℚ) ≤ 4 * ((n : ℚ) / ε) := by
    have hratio : (1 : ℚ) ≤ (n : ℚ) / ε := by
      have hh := ratio_ceil_ge_n (n := n) hε hεu
      apply (le_div_iff₀ hε).mpr
      have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
      linarith
    linarith
  have hp := ProgramPolynomial.input_split_envelope (A := A) (degree := degree) (r := 2)
    (L := H) (J := meshLevel T n ε) (P := answerBits Δ U n ε) (s := s) (N := 0)
    (a := a) (b := b) (k := 0) hr (ratio_order_pow_le hn hε hεu) hL hb (by positivity)
  have ho : A * (1 + H + answerBits Δ U n ε + 2 * (2 * meshLevel T n ε + 3)) ^ degree ≤
      PrimitiveInputHeight.inputBound A degree H 2 (meshLevel T n ε) (answerBits Δ U n ε) s + 0 + 3 := by
    unfold PrimitiveInputHeight.inputBound
    omega
  have hoq : ((A * (1 + H + answerBits Δ U n ε + 2 * (2 * meshLevel T n ε + 3)) ^ degree : ℕ) : ℚ) ≤
      ((PrimitiveInputHeight.inputBound A degree H 2 (meshLevel T n ε) (answerBits Δ U n ε) s + 0 + 3 : ℕ) : ℚ) := by
    exact_mod_cast ho
  convert hoq.trans hp using 1 <;> dsimp [a, b] <;> push_cast <;> ring

def oracleCoeff (Δ U T A degree : ℕ) : ℕ :=
  4 * ProgramPolynomial.splitLeafCoeff A degree 2 (Nat.clog 2 (4 * T) + 1)
    (Nat.clog 2 (4 * (2 * Δ) * U ^ (2 * Δ - 1)) + 1) 0

def uniformScale (Δ U T A degree : ℕ) : ℕ :=
  3 * fixedScale Δ U T + oracleCoeff Δ U T A degree + 1

/-- The numerical ratio degree is fixed before the oracle polynomial is
specified. Only the coefficient and encoding degree depend on A,degree. -/
theorem fullBitBound_uniform_polynomial (Δ U T : ℕ) :
    ∃ C : ℕ, ∀ A degree : ℕ, ∃ B D : ℕ, 0 < B ∧ ∀ (n m H : ℕ) (ε : ℚ),
      1 ≤ n → m ≤ Δ * n → 0 < ε → ε ≤ 1 / 2 → BitComplexity.rationalBits ε ≤ H →
      (fullBitBound n m Δ A degree H U T ε : ℚ) ≤
        (B : ℚ) * ((H + 1 : ℕ) : ℚ) ^ D * ((n : ℚ) / ε) ^ C := by
  obtain ⟨B0, C, hgrowth⟩ := reducedBody_growth Δ U
  refine ⟨C, ?_⟩
  intro A degree
  let K := uniformScale Δ U T A degree
  have hK : 1 ≤ K := by dsimp [K, uniformScale]; omega
  have hK0 : 3 * fixedScale Δ U T ≤ K := by dsimp [K, uniformScale]; omega
  have hKO : oracleCoeff Δ U T A degree ≤ K := by dsimp [K, uniformScale]; omega
  refine ⟨(B0 + 1) * (2 * K) ^ C, (degree + 1) * C, by positivity, ?_⟩
  intro n m H ε hn hm hε hεu hbits
  let X : ℚ := (n : ℚ) / ε
  let W : ℚ := (K : ℚ) * ((H + 1 : ℕ) : ℚ) ^ (degree + 1) * X
  let S := ⌈W⌉₊
  have hX : (1 : ℚ) ≤ X := by
    apply (le_div_iff₀ hε).mpr
    have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have hH : (1 : ℚ) ≤ ((H + 1 : ℕ) : ℚ) := by exact_mod_cast (show 1 ≤ H + 1 by omega)
  have hHP : (1 : ℚ) ≤ ((H + 1 : ℕ) : ℚ) ^ (degree + 1) := one_le_pow₀ hH
  have hHpow : ((H + 1 : ℕ) : ℚ) ≤ ((H + 1 : ℕ) : ℚ) ^ (degree + 1) := by
    simpa using pow_le_pow_right₀ hH (show 1 ≤ degree + 1 by omega)
  have hKq : (1 : ℚ) ≤ K := by exact_mod_cast hK
  have hW : (1 : ℚ) ≤ W := by
    calc
      1 ≤ (K : ℚ) * ((H + 1 : ℕ) : ℚ) ^ (degree + 1) := one_le_mul_of_one_le_of_one_le hKq hHP
      _ ≤ W := le_mul_of_one_le_right (by positivity) hX
  have hS : 1 ≤ S := by
    have hh := Nat.ceil_mono hW
    simpa only [Nat.ceil_one] using hh
  let S0 := fixedScale Δ U T * (H + ⌈(n : ℚ) / ε⌉₊ + 1)
  have hS0 : (S0 : ℚ) ≤ W := by
    apply (scale_le_ratio (Δ := Δ) (U := U) (T := T) (H := H) hn hε hεu).trans
    change ((3 * fixedScale Δ U T : ℕ) : ℚ) * ((H + 1 : ℕ) : ℚ) * X ≤ W
    dsimp only [W]
    gcongr
  have hS0S : S0 ≤ S := by
    have hh := hS0.trans (Nat.le_ceil W)
    exact_mod_cast hh
  let O := A * (1 + H + answerBits Δ U n ε + 2 * (2 * meshLevel T n ε + 3)) ^ degree
  have hOW : (O : ℚ) ≤ W := by
    apply (oracle_power_split (Δ := Δ) (U := U) (T := T) (A := A) (degree := degree) hn hε hεu).trans
    change (oracleCoeff Δ U T A degree : ℚ) * ((H + 1 : ℕ) : ℚ) ^ (degree + 1) * X ≤ W
    dsimp only [W]
    gcongr
  have hOS : O ≤ S := by exact_mod_cast hOW.trans (Nat.le_ceil W)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := selected_arguments_le hm hε hεu hbits
  have hcost : fullBitBound n m Δ A degree H U T ε ≤ B0 * S ^ C := by
    rw [fullBitBound_eq_body, costBody_eq_reduced]
    exact (reducedBody_mono Δ U (h1.trans hS0S) (h2.trans hS0S) (h4.trans hS0S)
      (h5.trans hS0S) (h6.trans hS0S) (h7.trans hS0S) hOS).trans (hgrowth S hS)
  have hSq : (S : ℚ) ≤ 2 * W := by
    have hh := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ W by linarith)
    dsimp only [S]
    linarith
  have hcostq : (fullBitBound n m Δ A degree H U T ε : ℚ) ≤ (B0 : ℚ) * (S : ℚ) ^ C := by
    exact_mod_cast hcost
  calc
    _ ≤ (B0 : ℚ) * (S : ℚ) ^ C := hcostq
    _ ≤ ((B0 + 1 : ℕ) : ℚ) * (2 * W) ^ C := by
      exact mul_le_mul (by norm_num) (pow_le_pow_left₀ (by positivity) hSq C) (by positivity) (by positivity)
    _ = _ := by dsimp [W, X]; push_cast; simp only [mul_pow, ← pow_mul]; ring

/-- Real-valued version retaining the order of the uniform quantifiers. -/
theorem fullBitBound_uniform_polynomial_real (Δ U T : ℕ) :
    ∃ C : ℕ, ∀ A degree : ℕ, ∃ B D : ℕ, 0 < B ∧ ∀ (n m H : ℕ) (ε : ℚ),
      1 ≤ n → m ≤ Δ * n → 0 < ε → ε ≤ 1 / 2 → BitComplexity.rationalBits ε ≤ H →
      (fullBitBound n m Δ A degree H U T ε : ℝ) ≤
        (B : ℝ) * ((H + 1 : ℕ) : ℝ) ^ D * ((n : ℝ) / (ε : ℝ)) ^ C := by
  obtain ⟨C, hp⟩ := fullBitBound_uniform_polynomial Δ U T
  refine ⟨C, ?_⟩
  intro A degree
  obtain ⟨B, D, hB, hp⟩ := hp A degree
  refine ⟨B, D, hB, ?_⟩
  intro n m H ε hn hm hε hεu hbits
  exact_mod_cast hp n m H ε hn hm hε hεu hbits

/-- Uniform Appendix A algorithm: the numerical ratio exponent depends only
on fixed model parameters, while oracle complexity affects B and D. -/
theorem lemma_A1_uniform_polynomial (Δ : ℕ) {U K : ℝ} (hU : 1 < U) (hK : 0 < K) :
    ∃ C : ℕ, ∀ A degree : ℕ, ∃ B D : ℕ, 0 < B ∧ ∀ (n r m H : ℕ) (E : FactorFamily n r m)
      (labelBits : Fin m → ℕ)
      (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e)),
      (∀ e, labelBits e ≤ H) → FamilyPrimalDegreeLe E 1 → FamilyBoundedOccurrence E Δ →
      (∀ e x, x ∈ Integral.cube (E e).scope.card →
        1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U) →
      (∀ e, (E e).LipOk K) → ∀ (ε : ℚ), 1 ≤ n → 0 < ε → ε ≤ 1 / 2 →
      BitComplexity.rationalBits ε ≤ H →
      FPTAS.Accurate
        ((SchoolbookArithmetic.execute (runProgram E (fun e => (O e).valueOracle.query)
          Δ (rangeBound U) (lipBudget Δ K U) ε)).1 : ℝ)
        (Integral.partitionFunctionFactor E) ε ∧
      (fullActualWork E labelBits O Δ (rangeBound U) (lipBudget Δ K U) ε : ℝ) ≤
        (B : ℝ) * ((H + 1 : ℕ) : ℝ) ^ D * ((n : ℝ) / (ε : ℝ)) ^ C := by
  obtain ⟨C, hp⟩ := fullBitBound_uniform_polynomial_real Δ (rangeBound U) (lipBudget Δ K U)
  refine ⟨C, ?_⟩
  intro A degree
  obtain ⟨B, D, hB, hp⟩ := hp A degree
  refine ⟨2 * B, D, by positivity, ?_⟩
  intro n r m H E labelBits O hlabels hdeg hocc hrange hLip ε hn hε hεu hbits
  have ha := lemma_A1_bit_algorithm E labelBits O hlabels hdeg hocc hU hK hrange hLip ε hε
  refine ⟨ha.1, ?_⟩
  have hm := family_card_le_occurrence_mul_variables E hocc
  have hc : (fullActualWork E labelBits O Δ (rangeBound U) (lipBudget Δ K U) ε : ℝ) ≤
      2 * (fullBitBound n m Δ A degree H (rangeBound U) (lipBudget Δ K U) ε : ℝ) := by
    exact_mod_cast fullActualWork_le E labelBits O hlabels hdeg hocc (rangeBound U) (lipBudget Δ K U) ε
  calc
    _ ≤ 2 * (fullBitBound n m Δ A degree H (rangeBound U) (lipBudget Δ K U) ε : ℝ) := hc
    _ ≤ 2 * ((B : ℝ) * ((H + 1 : ℕ) : ℝ) ^ D * ((n : ℝ) / (ε : ℝ)) ^ C) :=
      mul_le_mul_of_nonneg_left (hp n m H ε hn hm hε hεu hbits) (by norm_num)
    _ = _ := by push_cast; ring

/-- The η=1 corollary inherits the model-only numerical exponent. -/
theorem corollary_1_3_eta_one_uniform_polynomial (Δ : ℕ) {δ K : ℝ}
    (hρ : 1 < FPTAS.gamarnikSmediraRho Δ 1 δ) (hK : 0 < K) :
    ∃ C : ℕ, ∀ A degree : ℕ, ∃ B D : ℕ, 0 < B ∧ ∀ (n r m H : ℕ) (E : FactorFamily n r m)
      (labelBits : Fin m → ℕ)
      (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labelBits e)),
      (∀ e, labelBits e ≤ H) → FamilyPrimalDegreeLe E 1 → FamilyBoundedOccurrence E Δ →
      (∀ e x, x ∈ Integral.cube (E e).scope.card →
        1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ FPTAS.gamarnikSmediraRho Δ 1 δ) →
      (∀ e, (E e).LipOk K) → ∀ (ε : ℚ), 1 ≤ n → 0 < ε → ε ≤ 1 / 2 →
      BitComplexity.rationalBits ε ≤ H →
      FPTAS.Accurate
        ((SchoolbookArithmetic.execute (runProgram E (fun e => (O e).valueOracle.query) Δ
          (rangeBound (FPTAS.gamarnikSmediraRho Δ 1 δ))
          (lipBudget Δ K (FPTAS.gamarnikSmediraRho Δ 1 δ)) ε)).1 : ℝ)
        (Integral.partitionFunctionFactor E) ε ∧
      (fullActualWork E labelBits O Δ (rangeBound (FPTAS.gamarnikSmediraRho Δ 1 δ))
        (lipBudget Δ K (FPTAS.gamarnikSmediraRho Δ 1 δ)) ε : ℝ) ≤
        (B : ℝ) * ((H + 1 : ℕ) : ℝ) ^ D * ((n : ℝ) / (ε : ℝ)) ^ C :=
  lemma_A1_uniform_polynomial Δ hρ hK

end Paper08.LowDegreePolynomial
