import Paper08.FPTASProgram
import Paper08.SchoolbookArithmetic
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Polynomial bounds for the actual arithmetic program

All growing expression-size and input-leaf bounds are absorbed into fixed
powers of the numerical input ratio and its input encoding length.
-/

noncomputable section
open scoped BigOperators
namespace Paper08.ProgramPolynomial
open RationalProgram FPTASProgram FPTASAlgorithm

/-- Fixed exponent absorbing the actual logarithmic-order Taylor parameter. -/
def orderExponent (fixed : Parameters.Fixed) (c : ℕ) : ℕ :=
  (Parameters.binaryLog ((8 * (c + 1) : ℕ) : ℚ) + 1) *
    (Parameters.truncationBlock fixed * (Parameters.truncationOffset fixed + 1))

lemma two_pow_order_variables (fixed : Parameters.Fixed) {n m c : ℕ} {ε : ℚ}
    (hn : 1 ≤ n) (hmn : m ≤ c * n) (hε : 0 < ε) (hεu : ε ≤ 1 / 2) :
    (2 : ℚ) ^ Parameters.truncationOrder fixed m ε ≤
      ((n : ℚ) / ε) ^ orderExponent fixed c := by
  have hx : (2 : ℚ) ≤ (n : ℚ) / ε := by
    apply (le_div_iff₀ hε).mpr
    have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have hbase : 4 * (((m + 1 : ℕ) : ℚ) / ε) ≤
      ((8 * (c + 1) : ℕ) : ℚ) * ((n : ℚ) / ε) := by
    have hmn' : m + 1 ≤ 2 * (c + 1) * n := by nlinarith
    have hq : ((m + 1 : ℕ) : ℚ) ≤ 2 * (c + 1 : ℕ) * (n : ℚ) := by exact_mod_cast hmn'
    have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hq hε.le)
      (by norm_num : (0 : ℚ) ≤ 4)
    convert hh using 1; push_cast; ring
  apply (Parameters.two_pow_order_le fixed hε (by linarith : ε ≤ 1)).trans
  exact (pow_le_pow_left₀ (by positivity) hbase _).trans
    (MainTheorem.absorb_constant hx (by positivity))

def precisionSlope (fixed : Parameters.Fixed) : ℕ :=
  3 * Parameters.budgetBaseLog fixed + 3 * Parameters.momentBaseLog fixed + 23

lemma precision_le_slope (fixed : Parameters.Fixed) {m : ℕ} {ε : ℚ}
    (hm : 1 ≤ m) (hε : 0 < ε) :
    Parameters.precision fixed m ε ≤ precisionSlope fixed * Parameters.truncationOrder fixed m ε := by
  apply (Parameters.precision_le fixed hm hε).trans
  have hs := Parameters.truncationOrder_pos fixed m ε
  unfold Parameters.precisionBound Parameters.sampleToleranceExponent Parameters.levelBound
    Parameters.toleranceExponent precisionSlope
  nlinarith

/-- The fixed coefficient and degree in the primitive arithmetic envelope. -/
def primitiveCoeff (r a b : ℕ) : ℕ := r * a + 160 * (b + 3) ^ 2 + 6
def primitiveDegree (r a : ℕ) : ℕ := (r + 1) * a + 5

lemma primitive_nodes_envelope {r s P J a b : ℕ} {z : ℚ}
    (hz : 1 ≤ z) (hs : (2 : ℚ) ^ s ≤ z) (hJ : J ≤ a * s) (hP : P ≤ b * s) :
    (PrimitiveIntegralProgram.primitiveNodes r s P J : ℚ) ≤
      primitiveCoeff r a b * z ^ primitiveDegree r a := by
  have hs' : (s : ℚ) ≤ z := (by exact_mod_cast s.lt_two_pow_self.le :
    (s : ℚ) ≤ (2 : ℚ) ^ s).trans hs
  have hP' : (P : ℚ) ≤ b * z := (by exact_mod_cast hP : (P : ℚ) ≤ b * (s : ℚ)).trans
    (mul_le_mul_of_nonneg_left hs' (by positivity))
  have hJ' : (J : ℚ) ≤ a * z := (by exact_mod_cast hJ : (J : ℚ) ≤ a * (s : ℚ)).trans
    (mul_le_mul_of_nonneg_left hs' (by positivity))
  let k := (r + 1) * a + 1
  have hexp : (2 : ℚ) ^ ((r + 1) * J + s) ≤ z ^ k := by
    calc
      _ ≤ (2 : ℚ) ^ (k * s) := by
        apply pow_le_pow_right₀ (by norm_num)
        dsimp [k]
        nlinarith
      _ = ((2 : ℚ) ^ s) ^ k := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ z ^ k := pow_le_pow_left₀ (by positivity) hs k
  have hz3 : (1 : ℚ) ≤ z ^ 3 := one_le_pow₀ hz
  have hz4 : (1 : ℚ) ≤ z ^ 4 := one_le_pow₀ hz
  have hzz4 : z ≤ z ^ 4 := by simpa using pow_le_pow_right₀ hz (by omega : 1 ≤ 4)
  have hsample : (PrimitiveIntegralProgram.sampleNodes s P : ℚ) ≤
      80 * (b + 3 : ℚ) ^ 2 * z ^ 3 := by
    dsimp [PrimitiveIntegralProgram.sampleNodes]
    push_cast
    calc
      40 * ((s : ℚ) + 1) * ((P : ℚ) + 3) ^ 2 ≤
          40 * (2 * z) * (((b : ℚ) + 3) * z) ^ 2 := by gcongr <;> nlinarith
      _ = _ := by ring
  have hbody : (r : ℚ) * J + 2 * s * ((PrimitiveIntegralProgram.sampleNodes s P : ℚ) + 1) + 4 ≤
      primitiveCoeff r a b * z ^ 4 := by
    calc
      _ ≤ (r : ℚ) * (a * z ^ 4) +
          2 * z * ((80 * (b + 3 : ℚ) ^ 2 + 1) * z ^ 3) + 4 * z ^ 4 := by
        gcongr <;> nlinarith
      _ = _ := by dsimp [primitiveCoeff]; push_cast; ring
  dsimp [PrimitiveIntegralProgram.primitiveNodes]
  push_cast
  calc
    _ ≤ z ^ k * (primitiveCoeff r a b * z ^ 4) := by gcongr
    _ = primitiveCoeff r a b * z ^ (k + 4) := by rw [pow_add]; ring
    _ = _ := by rfl

/-- Fixed constants in the complete logarithmic assembly node envelope. -/
def logCoeff (r _c a b : ℕ) : ℕ := 16 * (primitiveCoeff r a b + 5) + 4
def logDegree (r c a : ℕ) : ℕ := (8 * degreeBound r c).size + primitiveDegree r a + 5

lemma log_nodes_envelope {m r c s P J a b : ℕ} {z : ℚ}
    (hz : 1 ≤ z) (hm : (m : ℚ) ≤ z) (hs : (2 : ℚ) ^ s ≤ z)
    (hJ : J ≤ a * s) (hP : P ≤ b * s) :
    (FPTASProgram.logNodes m r c s P J : ℚ) ≤ logCoeff r c a b * z ^ logDegree r c a := by
  have hs' : (s : ℚ) ≤ z := (by exact_mod_cast s.lt_two_pow_self.le :
    (s : ℚ) ≤ (2 : ℚ) ^ s).trans hs
  let e := primitiveDegree r a
  let A := primitiveCoeff r a b
  have he : 1 ≤ e := by dsimp [e, primitiveDegree]; omega
  have hze : z ≤ z ^ e := by simpa using pow_le_pow_right₀ hz he
  have hprim := primitive_nodes_envelope (r := r) hz hs hJ hP
  have hmoment : (momentNodes r s P J : ℚ) ≤ (A + 4 : ℕ) * z ^ (e + 2) := by
    unfold momentNodes
    push_cast
    have h4 : (4 : ℚ) ^ s ≤ z ^ 2 := by
      calc
        (4 : ℚ) ^ s = ((2 : ℚ) ^ s) ^ 2 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
        _ ≤ z ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
    calc
      _ ≤ z ^ 2 * ((A : ℚ) * z ^ e + 2 * z ^ e + 2 * z ^ e) := by gcongr <;> linarith [one_le_pow₀ hz (n := e)]
      _ = _ := by rw [pow_add]; ring
  have hlocal : (localNodes r s P J : ℚ) ≤ (16 * (A + 5) : ℕ) * z ^ (e + 3) := by
    unfold localNodes
    push_cast
    have h2 : (2 : ℚ) ^ (s + 4) ≤ 16 * z := by rw [pow_add]; norm_num; nlinarith
    calc
      _ ≤ (((A + 4 : ℕ) : ℚ) * z ^ (e + 2) + z ^ (e + 2)) * (16 * z) := by
        gcongr
        exact one_le_pow₀ hz
      _ = _ := by push_cast; rw [show e + 3 = (e + 2) + 1 by omega, pow_succ]; ring
  have hbase : ((8 * degreeBound r c : ℕ) : ℚ) ^ s ≤ z ^ (8 * degreeBound r c).size := by
    have hb : ((8 * degreeBound r c : ℕ) : ℚ) ≤ (2 : ℚ) ^ (8 * degreeBound r c).size := by
      exact_mod_cast (Nat.lt_size_self (8 * degreeBound r c)).le
    calc
      _ ≤ ((2 : ℚ) ^ (8 * degreeBound r c).size) ^ s := pow_le_pow_left₀ (by positivity) hb s
      _ = ((2 : ℚ) ^ s) ^ (8 * degreeBound r c).size := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hs _
  let k := (8 * degreeBound r c).size + e + 4
  have hzk : 1 ≤ z ^ k := one_le_pow₀ hz
  have hze3 : z ≤ z ^ (e + 3) := by simpa using pow_le_pow_right₀ hz (by omega : 1 ≤ e + 3)
  unfold FPTASProgram.logNodes
  push_cast
  calc
    _ ≤ z * (z * z ^ (8 * degreeBound r c).size *
        (((16 * (A + 5) : ℕ) : ℚ) * z ^ (e + 3) + z ^ (e + 3) + 2 * z ^ (e + 3)) + z ^ k) := by
      gcongr
      · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbase
      · exact hs'.trans hze3
      · nlinarith [one_le_pow₀ hz (n := e + 3)]
    _ = logCoeff r c a b * z ^ logDegree r c a := by
      dsimp [logCoeff, logDegree, k, e, A]
      push_cast
      simp only [pow_succ]
      ring

/-- A fixed coefficient for the final rational exponential AST. -/
def nodeCoeff (C k : ℕ) : ℕ := k * ((k + 6) * ((k + 6) * (C + k + 3) + 2) + 1)

lemma final_nodes_envelope {g h N k e C : ℕ} {w : ℚ}
    (hw : 1 ≤ w) (he : 1 ≤ e)
    (hpow : ((2 ^ h : ℕ) : ℚ) ≤ k * w) (hh : (h : ℚ) ≤ k * w)
    (hN : (N : ℚ) + 1 ≤ (k + 6 : ℕ) * w) (hg : (g : ℚ) ≤ C * w ^ e) :
    ((2 ^ h * ((N + 1) * ((N + 1) * (g + h + 3) + 2) + 1) : ℕ) : ℚ) ≤
      nodeCoeff C k * w ^ (e + 3) := by
  have hwe : w ≤ w ^ e := by simpa using pow_le_pow_right₀ hw he
  have h1e : 1 ≤ w ^ e := one_le_pow₀ hw
  have hinner : (g : ℚ) + h + 3 ≤ (C + k + 3 : ℕ) * w ^ e := by
    push_cast
    nlinarith
  have h1e1 : 1 ≤ w ^ (e + 1) := one_le_pow₀ hw
  have h1e2 : 1 ≤ w ^ (e + 2) := one_le_pow₀ hw
  push_cast
  calc
    _ ≤ (k : ℚ) * w *
        (((k + 6 : ℕ) : ℚ) * w *
          ((((k + 6 : ℕ) : ℚ) * w * (((C + k + 3 : ℕ) : ℚ) * w ^ e)) + 2 * w ^ (e + 1)) +
            w ^ (e + 2)) := by
      gcongr
      · simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpow
      · nlinarith
    _ = nodeCoeff C k * w ^ (e + 3) := by
      dsimp [nodeCoeff]
      push_cast
      simp only [pow_succ]
      ring

/-- A common envelope for nodes and leaves yields a seventh-power envelope
for the actual operand-sensitive arithmetic work. -/
lemma work_of_common_envelope (e : Expr) {T : ℚ} (hT : 1 ≤ T)
    (ho : (e.operations : ℚ) ≤ T) (hi : (e.inputHeight : ℚ) ≤ T) :
    (e.work : ℚ) ≤ 27 ^ 3 * T ^ 7 := by
  have he : (e.work : ℚ) ≤ (e.operations : ℚ) *
      (4 * (((e.inputHeight : ℚ) + 2) * ((e.operations : ℚ) + 1)) + 3) ^ 3 := by
    exact_mod_cast e.work_le
  have hinner : 4 * (((e.inputHeight : ℚ) + 2) * ((e.operations : ℚ) + 1)) + 3 ≤
      27 * T ^ 2 := by
    calc
      _ ≤ 4 * ((T + 2) * (T + 1)) + 3 := by gcongr
      _ ≤ _ := by nlinarith [sq_nonneg (T - 1)]
  calc
    (e.work : ℚ) ≤ (e.operations : ℚ) *
        (4 * (((e.inputHeight : ℚ) + 2) * ((e.operations : ℚ) + 1)) + 3) ^ 3 := he
    _ ≤ T * (27 * T ^ 2) ^ 3 := by gcongr
    _ = 27 ^ 3 * T ^ 7 := by ring

/-- The fixed coefficient needed for the actual oracle input leaves. -/
def leafCoeff (A degree r a b k : ℕ) : ℕ :=
  A * (2 + b + r * (2 * a + 3)) ^ degree + 2 * b + k + 17

lemma final_input_envelope {A degree r L J P s N a b k : ℕ} {w : ℚ}
    (hw : 1 ≤ w) (hL : (L : ℚ) ≤ w) (hJ : (J : ℚ) ≤ a * w)
    (hP : (P : ℚ) ≤ b * w) (hs : (s : ℚ) ≤ w)
    (hN : (N : ℚ) ≤ (k + 5 : ℕ) * w) :
    ((PrimitiveInputHeight.inputBound A degree L r J P s + N + 3 : ℕ) : ℚ) ≤
      leafCoeff A degree r a b k * w ^ (degree + 1) := by
  have hbase : (1 : ℚ) + L + P + r * (2 * J + 3) ≤
      (2 + b + r * (2 * a + 3) : ℕ) * w := by
    push_cast
    nlinarith
  have hwd : w ^ degree ≤ w ^ (degree + 1) := pow_le_pow_right₀ hw (by omega)
  have hw1 : w ≤ w ^ (degree + 1) := by simpa using pow_le_pow_right₀ hw (by omega : 1 ≤ degree + 1)
  unfold PrimitiveInputHeight.inputBound
  push_cast
  calc
    _ ≤ (A : ℚ) * ((((2 + b + r * (2 * a + 3) : ℕ) : ℚ) * w) ^ degree) +
        (2 * b + k + 17 : ℕ) * w := by
      have hp := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ 1 + L + P + r * (2 * J + 3)) hbase degree)
        (Nat.cast_nonneg A : (0 : ℚ) ≤ A)
      push_cast at hp ⊢
      push_cast at hN
      nlinarith
    _ ≤ (A : ℚ) * ((2 + b + r * (2 * a + 3) : ℕ) : ℚ) ^ degree * w ^ (degree + 1) +
        (2 * b + k + 17 : ℕ) * w ^ (degree + 1) := by
      rw [mul_pow, ← mul_assoc]
      gcongr
    _ = _ := by dsimp [leafCoeff]; push_cast; ring


/-- Fixed scale, common degree, and coefficient for the whole expression. -/
def scaleCoeff (fixed : Parameters.Fixed) : ℕ := 4 * ⌈fixed.qPlus⌉₊ + 6

def commonDegree (fixed : Parameters.Fixed) (r c degree : ℕ) : ℕ :=
  max (logDegree r c (FPTASCost.levelSlope fixed) + 3) (degree + 1)

def commonCoeff (fixed : Parameters.Fixed) (r c A degree : ℕ) : ℕ :=
  max (nodeCoeff (logCoeff r c (FPTASCost.levelSlope fixed) (precisionSlope fixed)) (scaleCoeff fixed))
    (leafCoeff A degree r (FPTASCost.levelSlope fixed) (precisionSlope fixed) (scaleCoeff fixed)) + 1

/-- Numerical absorption for the actual final node/leaf envelopes. The
argument bound is the consequence of the actual accuracy theorem supplied
in `run_program_polynomial` below, rather than an output certificate. -/
theorem run_bounds_envelope {n m r c A degree L : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (query : PrimitiveMomentsQ.Queries scopes)
    {ε z : ℚ} (hm : 1 ≤ m) (hε : 0 < ε) (hden : ε.den.size ≤ L)
    (hz : 1 ≤ z) (hmz : (m : ℚ) ≤ z)
    (hs : (2 : ℚ) ^ Parameters.truncationOrder fixed m ε ≤ z)
    (harg : |(logProgram scopes query r c (Parameters.truncationOrder fixed m ε) fixed.C
      (Parameters.primitiveTolerance fixed m ε)).eval| ≤ (m : ℚ) * fixed.qPlus + 1) :
    let w := ((L : ℚ) + 1) * z
    (runNodeBound fixed scopes query r c ε : ℚ) ≤
      commonCoeff fixed r c A degree * w ^ commonDegree fixed r c degree ∧
    (runInputBound fixed scopes query r c A degree L ε : ℚ) ≤
      commonCoeff fixed r c A degree * w ^ commonDegree fixed r c degree := by
  let s := Parameters.truncationOrder fixed m ε
  let J := Parameters.level fixed m ε
  let P := Parameters.precision fixed m ε
  let T := logProgram scopes query r c s fixed.C (Parameters.primitiveTolerance fixed m ε)
  let h := Algorithm.exponentialScale T.eval
  let N := Algorithm.exponentialDegree (ε / (12 * (2 : ℚ) ^ h))
  let a := FPTASCost.levelSlope fixed
  let b := precisionSlope fixed
  let k := scaleCoeff fixed
  let e := logDegree r c a
  let C := logCoeff r c a b
  let w := ((L : ℚ) + 1) * z
  have hzw : z ≤ w := by dsimp [w]; nlinarith [mul_nonneg (Nat.cast_nonneg L : (0 : ℚ) ≤ L) (by linarith : 0 ≤ z)]
  have hw : 1 ≤ w := hz.trans hzw
  have hLw : (L : ℚ) ≤ w := by dsimp [w]; nlinarith [mul_nonneg (Nat.cast_nonneg L : (0 : ℚ) ≤ L) (by linarith : 0 ≤ z - 1)]
  have hsc : (s : ℚ) ≤ z := (by exact_mod_cast s.lt_two_pow_self.le : (s : ℚ) ≤ (2 : ℚ) ^ s).trans hs
  have hJ : J ≤ a * s := FPTASCost.level_le_slope fixed hm hε
  have hP : P ≤ b * s := precision_le_slope fixed hm hε
  have hJw : (J : ℚ) ≤ a * w :=
    (by exact_mod_cast hJ : (J : ℚ) ≤ a * (s : ℚ)).trans
      (mul_le_mul_of_nonneg_left (hsc.trans hzw) (by positivity))
  have hPw : (P : ℚ) ≤ b * w :=
    (by exact_mod_cast hP : (P : ℚ) ≤ b * (s : ℚ)).trans
      (mul_le_mul_of_nonneg_left (hsc.trans hzw) (by positivity))
  have hscale : ((2 ^ h : ℕ) : ℚ) ≤ k * z := by
    have hq := Nat.le_ceil fixed.qPlus
    have hmq : (m : ℚ) * fixed.qPlus ≤ z * (⌈fixed.qPlus⌉₊ : ℚ) :=
      mul_le_mul hmz hq fixed.qPlus_pos.le (by linarith)
    have hp := Algorithm.exponentialScale_power_bound T.eval
    change ((2 ^ h : ℕ) : ℚ) ≤ 4 * |T.eval| + 2 at hp
    push_cast at hp
    change |T.eval| ≤ (m : ℚ) * fixed.qPlus + 1 at harg
    dsimp [k, scaleCoeff]
    push_cast
    nlinarith
  have hhw : (h : ℚ) ≤ k * w :=
    ((by exact_mod_cast h.lt_two_pow_self.le : (h : ℚ) ≤ ((2 ^ h : ℕ) : ℚ)).trans hscale).trans
      (mul_le_mul_of_nonneg_left hzw (by positivity))
  have hpoww : ((2 ^ h : ℕ) : ℚ) ≤ k * w :=
    hscale.trans (mul_le_mul_of_nonneg_left hzw (by positivity))
  have hNnat : N ≤ ε.den.size + h + 4 := BitComplexity.rationalExp_degree_le T.eval ε hε
  have hNw : (N : ℚ) ≤ (k + 5 : ℕ) * w := by
    have hn : (N : ℚ) ≤ L + (h : ℚ) + 4 := by exact_mod_cast hNnat.trans (by omega)
    push_cast
    nlinarith
  have hNplus : (N : ℚ) + 1 ≤ (k + 6 : ℕ) * w := by push_cast at hNw ⊢; nlinarith
  have he : 1 ≤ e := by dsimp [e, logDegree, primitiveDegree]; omega
  have hlog : (logNodes m r c s P J : ℚ) ≤ C * w ^ e :=
    (log_nodes_envelope (r := r) (c := c) hz hmz hs hJ hP).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hzw e) (by positivity))
  have hn := final_nodes_envelope (g := logNodes m r c s P J) hw he hpoww hhw hNplus hlog
  have hi := final_input_envelope (A := A) (degree := degree) (r := r)
    hw hLw hJw hPw (hsc.trans hzw) hNw
  have hnc : nodeCoeff C k ≤ commonCoeff fixed r c A degree := by
    exact (le_max_left _ _).trans (Nat.le_succ _)
  have hic : leafCoeff A degree r a b k ≤ commonCoeff fixed r c A degree := by
    exact (le_max_right _ _).trans (Nat.le_succ _)
  constructor
  · change (runNodeBound fixed scopes query r c ε : ℚ) ≤
      commonCoeff fixed r c A degree * w ^ commonDegree fixed r c degree
    change ((2 ^ h * ((N + 1) * ((N + 1) * (logNodes m r c s P J + h + 3) + 2) + 1) : ℕ) : ℚ) ≤ _
    apply hn.trans
    apply mul_le_mul (by exact_mod_cast hnc)
      (pow_le_pow_right₀ hw (le_max_left _ _)) (by positivity) (by positivity)
  · change (runInputBound fixed scopes query r c A degree L ε : ℚ) ≤
      commonCoeff fixed r c A degree * w ^ commonDegree fixed r c degree
    change ((PrimitiveInputHeight.inputBound A degree L r J P s + N + 3 : ℕ) : ℚ) ≤ _
    apply hi.trans
    apply mul_le_mul (by exact_mod_cast hic)
      (pow_le_pow_right₀ hw (le_max_right _ _)) (by positivity) (by positivity)


/-- A fixed-degree polynomial in the logarithmic parameter costs only one
additional exponential factor, independently of that degree. -/
lemma order_power_le (s d : ℕ) : (s + 1) ^ d ≤ (d.factorial * 2 ^ d) * 2 ^ s := by
  calc
    (s + 1) ^ d ≤ (s + 1).ascFactorial d := Nat.pow_succ_le_ascFactorial _ _
    _ = d.factorial * (s + d).choose d := Nat.ascFactorial_eq_factorial_mul_choose _ _
    _ ≤ d.factorial * 2 ^ (s + d) := Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
    _ = _ := by rw [pow_add]; ring

/-- Fixed oracle degree appears only in the coefficient and the input-length
power; the numerical input ratio gets one additional power. -/
def splitLeafCoeff (A degree r a b k : ℕ) : ℕ :=
  A * (2 + b + r * (2 * a + 3)) ^ degree * (degree.factorial * 2 ^ degree) +
    2 * b + k + 17

set_option maxHeartbeats 1000000 in
lemma input_split_envelope {A degree r L J P s N a b k : ℕ} {z : ℚ}
    (hz : 1 ≤ z) (hs : (2 : ℚ) ^ s ≤ z) (hJ : J ≤ a * s) (hP : P ≤ b * s)
    (hN : (N : ℚ) ≤ L + k * z + 4) :
    ((PrimitiveInputHeight.inputBound A degree L r J P s + N + 3 : ℕ) : ℚ) ≤
      splitLeafCoeff A degree r a b k * ((L : ℚ) + 1) ^ (degree + 1) * z := by
  have hsc : (s : ℚ) ≤ z := (by exact_mod_cast s.lt_two_pow_self.le : (s : ℚ) ≤ (2 : ℚ) ^ s).trans hs
  have hp : (P : ℚ) ≤ b * (s : ℚ) := by exact_mod_cast hP
  have hj : (J : ℚ) ≤ a * (s : ℚ) := by exact_mod_cast hJ
  have hL : (1 : ℚ) ≤ L + 1 := by have := (Nat.cast_nonneg L : (0 : ℚ) ≤ L); linarith
  have hLpow : ((L : ℚ) + 1) ^ degree ≤ ((L : ℚ) + 1) ^ (degree + 1) :=
    pow_le_pow_right₀ hL (by omega)
  have hLpow1 : (L : ℚ) + 1 ≤ ((L : ℚ) + 1) ^ (degree + 1) := by
    simpa using pow_le_pow_right₀ hL (by omega : 1 ≤ degree + 1)
  have hbase : (1 : ℚ) + L + P + r * (2 * J + 3) ≤
      ((2 + b + r * (2 * a + 3) : ℕ) : ℚ) * ((L : ℚ) + 1) * ((s : ℚ) + 1) := by
    calc
      _ ≤ (1 : ℚ) + L + b * (s : ℚ) + r * (2 * (a * (s : ℚ)) + 3) := by gcongr
      _ ≤ _ := by
        push_cast
        apply le_of_sub_nonneg
        ring_nf
        positivity
  have hpoly : ((s : ℚ) + 1) ^ degree ≤ ((degree.factorial * 2 ^ degree : ℕ) : ℚ) * z := by
    have hp := order_power_le s degree
    have hpq : ((s : ℚ) + 1) ^ degree ≤ ((degree.factorial * 2 ^ degree : ℕ) : ℚ) * (2 : ℚ) ^ s := by
      exact_mod_cast hp
    exact hpq.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have hpower : (A : ℚ) * ((1 : ℚ) + L + P + r * (2 * J + 3)) ^ degree ≤
      ((A * (2 + b + r * (2 * a + 3)) ^ degree * (degree.factorial * 2 ^ degree) : ℕ) : ℚ) *
        ((L : ℚ) + 1) ^ (degree + 1) * z := by
    calc
      _ ≤ (A : ℚ) * ((((2 + b + r * (2 * a + 3) : ℕ) : ℚ) *
          ((L : ℚ) + 1) * ((s : ℚ) + 1)) ^ degree) := by gcongr
      _ = (A : ℚ) * ((2 + b + r * (2 * a + 3) : ℕ) : ℚ) ^ degree *
          ((L : ℚ) + 1) ^ degree * ((s : ℚ) + 1) ^ degree := by rw [mul_pow, mul_pow]; ring
      _ ≤ (A : ℚ) * ((2 + b + r * (2 * a + 3) : ℕ) : ℚ) ^ degree *
          ((L : ℚ) + 1) ^ (degree + 1) * (((degree.factorial * 2 ^ degree : ℕ) : ℚ) * z) := by gcongr
      _ = _ := by push_cast; ring
  have htail : (2 : ℚ) * P + s + 8 + N + 3 ≤
      ((2 * b + k + 17 : ℕ) : ℚ) * ((L : ℚ) + 1) ^ (degree + 1) * z := by
    have hPz : (P : ℚ) ≤ b * z := hp.trans (mul_le_mul_of_nonneg_left hsc (by positivity))
    have h1z : (1 : ℚ) ≤ ((L : ℚ) + 1) * z := by nlinarith
    have hLz : (L : ℚ) ≤ ((L : ℚ) + 1) * z := by nlinarith [mul_nonneg (Nat.cast_nonneg L : (0 : ℚ) ≤ L) (by linarith : 0 ≤ z - 1)]
    have hzz : z ≤ ((L : ℚ) + 1) * z := by nlinarith [mul_nonneg (Nat.cast_nonneg L : (0 : ℚ) ≤ L) (by linarith : 0 ≤ z)]
    calc
      _ ≤ ((2 * b + k + 17 : ℕ) : ℚ) * ((L : ℚ) + 1) * z := by push_cast; nlinarith
      _ ≤ _ := by gcongr
  unfold PrimitiveInputHeight.inputBound
  push_cast at hpower htail ⊢
  dsimp [splitLeafCoeff]
  push_cast
  nlinarith


lemma orderExponent_pos (fixed : Parameters.Fixed) (c : ℕ) : 1 ≤ orderExponent fixed c := by
  have hb := Parameters.truncationBlock_pos fixed
  have ho : 1 ≤ Parameters.truncationOffset fixed + 1 := by omega
  have hl : 1 ≤ Parameters.binaryLog ((8 * (c + 1) : ℕ) : ℚ) + 1 := by omega
  unfold orderExponent
  calc
    1 = 1 * (1 * 1) := by norm_num
    _ ≤ _ := Nat.mul_le_mul hl (Nat.mul_le_mul hb ho)

/-- The numerical degree is independent of the uniform oracle polynomial. -/
def numericalDegree (fixed : Parameters.Fixed) (r c : ℕ) : ℕ := commonDegree fixed r c 0
def encodingDegree (fixed : Parameters.Fixed) (r c degree : ℕ) : ℕ :=
  max (numericalDegree fixed r c) (degree + 1)
def programCoeff (fixed : Parameters.Fixed) (r c A degree : ℕ) : ℕ :=
  max (commonCoeff fixed r c 0 0)
    (splitLeafCoeff A degree r (FPTASCost.levelSlope fixed) (precisionSlope fixed) (scaleCoeff fixed)) + 1

/-- Actual model semantics give the argument-amplitude bound used in numerical
absorption, rather than a cost or answer-size certificate. -/
lemma actual_argument_bound {n m A degree : ℕ} (p : FPTAS.Params) (fixed : Parameters.Fixed)
    (hb : FPTASCorrectness.FixedBounds p fixed) (E : FactorFamily n p.r m)
    (labels : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labels e))
    (hc : FamilyBoundedOccurrence E p.c) (hE : ∀ e, (E e).RangeOk p.q)
    (hLip : ∀ e, (E e).LipOk p.K) (hne : FPTASCorrectness.CommonNonvanishing p E)
    {ε : ℚ} (hm : 1 ≤ m) (hε : 0 < ε) (hεu : ε ≤ 1 / 2) :
    |(logProgram (fun e => (E e).scope) (fun e => (O e).valueOracle.query) p.r p.c
      (Parameters.truncationOrder fixed m ε) fixed.C (Parameters.primitiveTolerance fixed m ε)).eval| ≤
        (m : ℚ) * fixed.qPlus + 1 := by
  have ha := FPTASCorrectness.logApprox_abs_le p fixed hb E
    (fun e => (O e).valueOracle) hc hE hLip hne hm hε hεu
  have hr : |(logApprox (fun e => (E e).scope) (fun e => (O e).valueOracle.query) p.r p.c
      (Parameters.truncationOrder fixed m ε) fixed.C (Parameters.primitiveTolerance fixed m ε) : ℝ)| ≤
        (m : ℝ) * (fixed.qPlus : ℝ) + 1 := by
    apply ha.trans
    nlinarith [mul_le_mul_of_nonneg_left hb.q_upper (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rw [logProgram_eval]
  exact_mod_cast hr

set_option maxHeartbeats 1000000 in
theorem model_run_envelopes {n m A degree L : ℕ} (p : FPTAS.Params) (fixed : Parameters.Fixed)
    (hb : FPTASCorrectness.FixedBounds p fixed) (E : FactorFamily n p.r m)
    (labels : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labels e))
    (hc : FamilyBoundedOccurrence E p.c) (hE : ∀ e, (E e).RangeOk p.q)
    (hLip : ∀ e, (E e).LipOk p.K) (hne : FPTASCorrectness.CommonNonvanishing p E)
    {ε : ℚ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hε : 0 < ε) (hεu : ε ≤ 1 / 2)
    (hden : ε.den.size ≤ L) :
    let z : ℚ := (p.c + 1 : ℕ) * ((n : ℚ) / ε) ^ orderExponent fixed p.c
    let T : ℚ := programCoeff fixed p.r p.c A degree * ((L : ℚ) + 1) ^ encodingDegree fixed p.r p.c degree *
      z ^ numericalDegree fixed p.r p.c
    (runNodeBound fixed (fun e => (E e).scope) (fun e => (O e).valueOracle.query) p.r p.c ε : ℚ) ≤ T ∧
    (runInputBound fixed (fun e => (E e).scope) (fun e => (O e).valueOracle.query) p.r p.c A degree L ε : ℚ) ≤ T := by
  let x : ℚ := (n : ℚ) / ε
  let z : ℚ := (p.c + 1 : ℕ) * x ^ orderExponent fixed p.c
  have hx : 1 ≤ x := by
    apply (le_div_iff₀ hε).mpr
    have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have hxp : x ≤ x ^ orderExponent fixed p.c := by
    simpa using pow_le_pow_right₀ hx (orderExponent_pos fixed p.c)
  have hz : 1 ≤ z := by
    have hpow : 1 ≤ x ^ orderExponent fixed p.c := one_le_pow₀ hx
    have hc1 : (1 : ℚ) ≤ (p.c + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le p.c)
    dsimp [z]
    nlinarith
  have hnx : (n : ℚ) ≤ x := by
    apply (le_div_iff₀ hε).mpr
    nlinarith [mul_le_mul_of_nonneg_left (show ε ≤ 1 by linarith) (Nat.cast_nonneg n : (0 : ℚ) ≤ n)]
  have hocc := family_card_le_occurrence_mul_variables E hc
  have hmz : (m : ℚ) ≤ z := by
    have hmn : (m : ℚ) ≤ (p.c : ℚ) * n := by exact_mod_cast hocc
    have hcx := mul_le_mul_of_nonneg_left hnx (Nat.cast_nonneg p.c : (0 : ℚ) ≤ p.c)
    dsimp [z]
    push_cast
    nlinarith
  have hs : (2 : ℚ) ^ Parameters.truncationOrder fixed m ε ≤ z :=
    (two_pow_order_variables fixed hn hocc hε hεu).trans (by
      dsimp [z]
      have hp : (0 : ℚ) ≤ x ^ orderExponent fixed p.c := by positivity
      push_cast
      nlinarith)
  have harg := actual_argument_bound p fixed hb E labels O hc hE hLip hne hm hε hεu
  have hnumb := (run_bounds_envelope (A := 0) (degree := 0) fixed
    (fun e => (E e).scope) (fun e => (O e).valueOracle.query) hm hε hden hz hmz hs harg).1
  let s := Parameters.truncationOrder fixed m ε
  let J := Parameters.level fixed m ε
  let P := Parameters.precision fixed m ε
  let Tlog := logProgram (fun e => (E e).scope) (fun e => (O e).valueOracle.query) p.r p.c s fixed.C
    (Parameters.primitiveTolerance fixed m ε)
  let h := Algorithm.exponentialScale Tlog.eval
  let N := Algorithm.exponentialDegree (ε / (12 * (2 : ℚ) ^ h))
  have hscale : ((2 ^ h : ℕ) : ℚ) ≤ scaleCoeff fixed * z := by
    have hq := Nat.le_ceil fixed.qPlus
    have hmq : (m : ℚ) * fixed.qPlus ≤ z * (⌈fixed.qPlus⌉₊ : ℚ) :=
      mul_le_mul hmz hq fixed.qPlus_pos.le (by linarith)
    have hp := Algorithm.exponentialScale_power_bound Tlog.eval
    change ((2 ^ h : ℕ) : ℚ) ≤ 4 * |Tlog.eval| + 2 at hp
    change |Tlog.eval| ≤ (m : ℚ) * fixed.qPlus + 1 at harg
    unfold scaleCoeff
    push_cast at hp ⊢
    nlinarith
  have hh : (h : ℚ) ≤ scaleCoeff fixed * z :=
    (by exact_mod_cast h.lt_two_pow_self.le : (h : ℚ) ≤ ((2 ^ h : ℕ) : ℚ)).trans hscale
  have hN : (N : ℚ) ≤ L + scaleCoeff fixed * z + 4 := by
    have hbN := BitComplexity.rationalExp_degree_le Tlog.eval ε hε
    have hhN : N ≤ L + h + 4 := hbN.trans (by omega)
    have hcast : (N : ℚ) ≤ L + (h : ℚ) + 4 := by exact_mod_cast hhN
    linarith
  have hj := FPTASCost.level_le_slope fixed hm hε
  have hp := precision_le_slope fixed hm hε
  have hinput := input_split_envelope (A := A) (degree := degree) (r := p.r) hz hs hj hp hN
  have hL1 : (1 : ℚ) ≤ L + 1 := by have := (Nat.cast_nonneg L : (0 : ℚ) ≤ L); linarith
  have he : 1 ≤ numericalDegree fixed p.r p.c := le_max_right _ _
  have hze : z ≤ z ^ numericalDegree fixed p.r p.c := by simpa using pow_le_pow_right₀ hz he
  have hncoeff : commonCoeff fixed p.r p.c 0 0 ≤ programCoeff fixed p.r p.c A degree :=
    (le_max_left _ _).trans (Nat.le_succ _)
  have hicoeff : splitLeafCoeff A degree p.r (FPTASCost.levelSlope fixed) (precisionSlope fixed) (scaleCoeff fixed) ≤
      programCoeff fixed p.r p.c A degree := (le_max_right _ _).trans (Nat.le_succ _)
  constructor
  · apply hnumb.trans
    rw [mul_pow]
    rw [← mul_assoc]
    have hcoef : (commonCoeff fixed p.r p.c 0 0 : ℚ) ≤ programCoeff fixed p.r p.c A degree :=
      Nat.cast_le.mpr hncoeff
    have hdegree : commonDegree fixed p.r p.c 0 ≤ encodingDegree fixed p.r p.c degree :=
      le_max_left _ _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hcoef (pow_le_pow_right₀ hL1 hdegree) (by positivity) (by positivity))
      (by positivity)

  · change (runInputBound fixed (fun e => (E e).scope) (fun e => (O e).valueOracle.query)
      p.r p.c A degree L ε : ℚ) ≤ _
    change ((PrimitiveInputHeight.inputBound A degree L p.r J P s + N + 3 : ℕ) : ℚ) ≤ _
    apply hinput.trans
    apply mul_le_mul
      (mul_le_mul (Nat.cast_le.mpr hicoeff) (pow_le_pow_right₀ hL1 (le_max_right _ _))
        (by positivity) (by positivity)) hze (by linarith) (by positivity)


/-- A fixed exponential in the actual truncation order is polynomial in n/ε. -/
lemma fixed_base_order_le (fixed : Parameters.Fixed) (base : ℕ)
    {n m c : ℕ} {ε : ℚ} (hn : 1 ≤ n) (hmn : m ≤ c * n)
    (hε : 0 < ε) (hεu : ε ≤ 1 / 2) :
    (base : ℚ) ^ Parameters.truncationOrder fixed m ε ≤
      ((n : ℚ) / ε) ^ (orderExponent fixed c * base.size) := by
  have hb : (base : ℚ) ≤ (2 : ℚ) ^ base.size := by
    exact_mod_cast (Nat.lt_size_self base).le
  calc
    _ ≤ ((2 : ℚ) ^ base.size) ^ Parameters.truncationOrder fixed m ε :=
      pow_le_pow_left₀ (by positivity) hb _
    _ = ((2 : ℚ) ^ Parameters.truncationOrder fixed m ε) ^ base.size := by
      simp only [← pow_mul, Nat.mul_comm]
    _ ≤ (((n : ℚ) / ε) ^ orderExponent fixed c) ^ base.size :=
      pow_le_pow_left₀ (by positivity) (two_pow_order_variables fixed hn hmn hε hεu) _
    _ = _ := (pow_mul _ _ _).symm

/-- Only the prefactor and input-length degree depend on the effective oracle
polynomial. The numerical input ratio degree depends on the fixed model parameters. -/
def arithmeticCoeff (fixed : Parameters.Fixed) (r c A degree : ℕ) : ℕ :=
  10000 * 27 ^ 3 * programCoeff fixed r c A degree ^ 7 *
    (c + 1) ^ (numericalDegree fixed r c * 7)
def arithmeticEncodingDegree (fixed : Parameters.Fixed) (r c degree : ℕ) : ℕ :=
  encodingDegree fixed r c degree * 7
def arithmeticRatioDegree (fixed : Parameters.Fixed) (r c : ℕ) : ℕ :=
  orderExponent fixed c * numericalDegree fixed r c * 7

lemma arithmeticCoeff_pos (fixed : Parameters.Fixed) (r c A degree : ℕ) :
    0 < arithmeticCoeff fixed r c A degree := by
  have hk : 0 < programCoeff fixed r c A degree := by unfold programCoeff; omega
  unfold arithmeticCoeff
  positivity

lemma arithmetic_factorization (fixed : Parameters.Fixed) (r c A degree L : ℕ) (x : ℚ) :
    10000 * (27 : ℚ) ^ 3 *
      ((programCoeff fixed r c A degree : ℚ) * ((L : ℚ) + 1) ^ encodingDegree fixed r c degree *
        (((c + 1 : ℕ) : ℚ) * x ^ orderExponent fixed c) ^ numericalDegree fixed r c) ^ 7 =
    (arithmeticCoeff fixed r c A degree : ℚ) *
      ((L : ℚ) + 1) ^ arithmeticEncodingDegree fixed r c degree *
      x ^ arithmeticRatioDegree fixed r c := by
  unfold arithmeticCoeff arithmeticEncodingDegree arithmeticRatioDegree
  push_cast
  simp only [mul_pow, ← pow_mul, Nat.mul_assoc]
  ring

set_option maxHeartbeats 1000000 in
/-- The actual fully expanded rational program, including schoolbook rational
normalization, has polynomial cost. No answer-size or output certificate is an
input to the theorem. Its exponent of n/ε is independent of the oracle degree. -/
theorem model_program_polynomial {n m A degree L : ℕ} (p : FPTAS.Params) (fixed : Parameters.Fixed)
    (hb : FPTASCorrectness.FixedBounds p fixed) (E : FactorFamily n p.r m)
    (labels : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labels e))
    (hlabels : ∀ e, labels e ≤ L)
    (hc : FamilyBoundedOccurrence E p.c) (hE : ∀ e, (E e).RangeOk p.q)
    (hLip : ∀ e, (E e).LipOk p.K) (hne : FPTASCorrectness.CommonNonvanishing p E)
    {ε : ℚ} (hn : 1 ≤ n) (hε : 0 < ε) (hεu : ε ≤ 1 / 2)
    (hbits : BitComplexity.rationalBits ε ≤ L) :
    let e := runProgram fixed (fun e => (E e).scope) (fun e => (O e).valueOracle.query) p.r p.c ε
    let B : ℚ := arithmeticCoeff fixed p.r p.c A degree *
      ((L : ℚ) + 1) ^ arithmeticEncodingDegree fixed p.r p.c degree *
      ((n : ℚ) / ε) ^ arithmeticRatioDegree fixed p.r p.c
    (e.operations : ℚ) ≤ B ∧ (e.inputHeight : ℚ) ≤ B ∧
      (e.work : ℚ) ≤ B ∧ (SchoolbookArithmetic.exprBitCost e : ℚ) ≤ B := by
  let x : ℚ := (n : ℚ) / ε
  let z : ℚ := ((p.c + 1 : ℕ) : ℚ) * x ^ orderExponent fixed p.c
  let T : ℚ := programCoeff fixed p.r p.c A degree * ((L : ℚ) + 1) ^ encodingDegree fixed p.r p.c degree *
    z ^ numericalDegree fixed p.r p.c
  let e := runProgram fixed (fun e => (E e).scope) (fun e => (O e).valueOracle.query) p.r p.c ε
  have hx : 1 ≤ x := by
    apply (le_div_iff₀ hε).mpr
    have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have hz : 1 ≤ z := by
    have hcp : (1 : ℚ) ≤ ((p.c + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.le_add_left 1 p.c
    have hxp : 1 ≤ x ^ orderExponent fixed p.c := one_le_pow₀ hx
    dsimp only [z]
    nlinarith
  have hT : 1 ≤ T := by
    have hk : (1 : ℚ) ≤ (programCoeff fixed p.r p.c A degree : ℚ) := by
      exact_mod_cast (show 1 ≤ programCoeff fixed p.r p.c A degree by unfold programCoeff; omega)
    have hL : (1 : ℚ) ≤ ((L : ℚ) + 1) ^ encodingDegree fixed p.r p.c degree :=
      one_le_pow₀ (by have := (Nat.cast_nonneg L : (0 : ℚ) ≤ L); linarith)
    have hzp : 1 ≤ z ^ numericalDegree fixed p.r p.c := one_le_pow₀ hz
    dsimp only [T]
    calc
      1 = 1 * 1 * 1 := by norm_num
      _ ≤ _ := mul_le_mul (mul_le_mul hk hL (by norm_num) (by positivity)) hzp (by norm_num) (by positivity)
  have hbig : T ≤ 10000 * (27 : ℚ) ^ 3 * T ^ 7 := by
    have hpow : T ≤ T ^ 7 := by simpa using pow_le_pow_right₀ hT (by norm_num : 1 ≤ 7)
    nlinarith [pow_nonneg (by linarith : 0 ≤ T) 7]
  have hden : ε.den.size ≤ L := by unfold BitComplexity.rationalBits at hbits; omega
  have hh : (e.operations : ℚ) ≤ T ∧ (e.inputHeight : ℚ) ≤ T := by
    by_cases hm : m = 0
    · dsimp only [e, runProgram]
      rw [if_pos hm]
      constructor
      · simpa only [Expr.operations, Nat.cast_zero] using (by linarith : (0 : ℚ) ≤ T)
      · simpa [Expr.inputHeight, RationalProgram.height] using hT
    · have hm1 : 1 ≤ m := by omega
      have hen := model_run_envelopes p fixed hb E labels O hc hE hLip hne hm1 hn hε hεu hden
      constructor
      · exact (Nat.cast_le.mpr (runProgram_operations_le fixed (fun e => (E e).scope)
          (fun e => (E e).card_le) (fun e => (O e).valueOracle.query) ε)).trans hen.1
      · exact (Nat.cast_le.mpr (runProgram_inputHeight fixed (fun e => (E e).scope)
          (fun e => (E e).card_le) (fun e => (E e).psi.toFun) labels O hlabels ε)).trans hen.2
  have hw : (e.work : ℚ) ≤ (27 : ℚ) ^ 3 * T ^ 7 := work_of_common_envelope e hT hh.1 hh.2
  have hbcost : (SchoolbookArithmetic.exprBitCost e : ℚ) ≤ 10000 * (27 : ℚ) ^ 3 * T ^ 7 := by
    have hk : (SchoolbookArithmetic.exprBitCost e : ℚ) ≤ 10000 * (e.work : ℚ) := by
      exact_mod_cast SchoolbookArithmetic.exprBitCost_le e
    exact hk.trans (by nlinarith)
  change (e.operations : ℚ) ≤ _ ∧ (e.inputHeight : ℚ) ≤ _ ∧ (e.work : ℚ) ≤ _ ∧
    (SchoolbookArithmetic.exprBitCost e : ℚ) ≤ _
  rw [← arithmetic_factorization fixed p.r p.c A degree L x]
  change (e.operations : ℚ) ≤ 10000 * (27 : ℚ)^3 * T^7 ∧
    (e.inputHeight : ℚ) ≤ 10000 * (27 : ℚ)^3 * T^7 ∧
    (e.work : ℚ) ≤ 10000 * (27 : ℚ)^3 * T^7 ∧
    (SchoolbookArithmetic.exprBitCost e : ℚ) ≤ 10000 * (27 : ℚ)^3 * T^7
  exact ⟨hh.1.trans hbig, hh.2.trans hbig, hw.trans (by nlinarith [pow_nonneg (by linarith : 0 ≤ T) 7]), hbcost⟩


/-- The explicit numeric node and input-height envelopes satisfy the same
polynomial as the actual program. This also controls the oracle-time envelope,
whose query-size estimate uses `runInputBound` itself. -/
theorem model_numeric_bounds_polynomial {n m A degree L : ℕ} (p : FPTAS.Params) (fixed : Parameters.Fixed)
    (hb : FPTASCorrectness.FixedBounds p fixed) (E : FactorFamily n p.r m)
    (labels : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun A degree (labels e))
    (hc : FamilyBoundedOccurrence E p.c) (hE : ∀ e, (E e).RangeOk p.q)
    (hLip : ∀ e, (E e).LipOk p.K) (hne : FPTASCorrectness.CommonNonvanishing p E)
    {ε : ℚ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hε : 0 < ε) (hεu : ε ≤ 1 / 2)
    (hbits : BitComplexity.rationalBits ε ≤ L) :
    let B : ℚ := arithmeticCoeff fixed p.r p.c A degree *
      ((L : ℚ) + 1) ^ arithmeticEncodingDegree fixed p.r p.c degree *
      ((n : ℚ) / ε) ^ arithmeticRatioDegree fixed p.r p.c
    (runNodeBound fixed (fun e => (E e).scope) (fun e => (O e).valueOracle.query) p.r p.c ε : ℚ) ≤ B ∧
    (runInputBound fixed (fun e => (E e).scope) (fun e => (O e).valueOracle.query) p.r p.c A degree L ε : ℚ) ≤ B := by
  let x : ℚ := (n : ℚ) / ε
  let z : ℚ := ((p.c + 1 : ℕ) : ℚ) * x ^ orderExponent fixed p.c
  let T : ℚ := programCoeff fixed p.r p.c A degree * ((L : ℚ) + 1) ^ encodingDegree fixed p.r p.c degree *
    z ^ numericalDegree fixed p.r p.c
  have hx : 1 ≤ x := by
    apply (le_div_iff₀ hε).mpr
    have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have hz : 1 ≤ z := by
    have hcp : (1 : ℚ) ≤ ((p.c + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.le_add_left 1 p.c
    have hxp : 1 ≤ x ^ orderExponent fixed p.c := one_le_pow₀ hx
    dsimp only [z]
    nlinarith
  have hT : 1 ≤ T := by
    have hk : (1 : ℚ) ≤ (programCoeff fixed p.r p.c A degree : ℚ) := by
      exact_mod_cast (show 1 ≤ programCoeff fixed p.r p.c A degree by unfold programCoeff; omega)
    have hL : (1 : ℚ) ≤ ((L : ℚ) + 1) ^ encodingDegree fixed p.r p.c degree :=
      one_le_pow₀ (by have := (Nat.cast_nonneg L : (0 : ℚ) ≤ L); linarith)
    have hzp : 1 ≤ z ^ numericalDegree fixed p.r p.c := one_le_pow₀ hz
    dsimp only [T]
    calc
      1 = 1 * 1 * 1 := by norm_num
      _ ≤ _ := mul_le_mul (mul_le_mul hk hL (by norm_num) (by positivity)) hzp (by norm_num) (by positivity)
  have hbig : T ≤ 10000 * (27 : ℚ) ^ 3 * T ^ 7 := by
    have hpow : T ≤ T ^ 7 := by simpa using pow_le_pow_right₀ hT (by norm_num : 1 ≤ 7)
    nlinarith [pow_nonneg (by linarith : 0 ≤ T) 7]
  have hden : ε.den.size ≤ L := by unfold BitComplexity.rationalBits at hbits; omega
  have hen := model_run_envelopes p fixed hb E labels O hc hE hLip hne hm hn hε hεu hden
  dsimp only
  rw [← arithmetic_factorization fixed p.r p.c A degree L x]
  change _ ≤ 10000 * (27 : ℚ)^3 * T^7 ∧ _ ≤ 10000 * (27 : ℚ)^3 * T^7
  exact ⟨hen.1.trans hbig, hen.2.trans hbig⟩

end Paper08.ProgramPolynomial
