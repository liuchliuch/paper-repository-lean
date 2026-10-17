import Paper08.Oracle
import Mathlib.Algebra.Order.Ring.Pow

/-! # Effective choices and bounds for the precision parameters

Only the paper's fixed rational upper bounds occur in `Fixed`. None of the
accuracy or complexity conclusions is supplied as a field.
-/

namespace Paper08.Parameters

/-- Certified fixed constants used by the rational algorithm. -/
structure Fixed where
  R : ℚ
  qPlus : ℚ
  A0 : ℕ
  F : ℕ
  C : ℕ
  R_gt_one : 1 < R
  qPlus_pos : 0 < qPlus
  A0_pos : 1 ≤ A0
  F_pos : 1 ≤ F
  C_pos : 1 ≤ C

/-- A computable upper binary logarithm, with the compulsory value at least one. -/
def binaryLog (x : ℚ) : ℕ := max 1 (Nat.clog 2 ⌈x⌉₊)

lemma binaryLog_pos (x : ℚ) : 1 ≤ binaryLog x := le_max_left _ _

lemma binaryLog_pow (x : ℚ) : x ≤ (2 : ℚ) ^ binaryLog x := by
  have hl : ⌈x⌉₊ ≤ 2 ^ binaryLog x :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp (le_max_right _ _)
  exact (Nat.le_ceil x).trans (by exact_mod_cast hl)

lemma binaryLog_le {x : ℚ} {u : ℕ} (hu : 1 ≤ u) (hx : x ≤ (2 : ℚ) ^ u) :
    binaryLog x ≤ u := by
  rw [binaryLog, max_le_iff]
  refine ⟨hu, (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr ?_⟩
  rw [Nat.ceil_le]
  exact_mod_cast hx

/-- A fixed block of powers of `R` that grows by at least a factor of two. -/
def truncationBlock (p : Fixed) : ℕ := max 1 ⌈1 / (p.R - 1)⌉₊

def truncationOffset (p : Fixed) : ℕ := binaryLog (6 * p.R * p.qPlus / (p.R - 1))

/-- The single growing binary logarithm controlling all precision parameters. -/
def inputLog (m : ℕ) (ε : ℚ) : ℕ := binaryLog (((m + 1 : ℕ) : ℚ) / ε)

/-- An effective Taylor truncation degree. It is a fixed multiple of the
input binary logarithm plus a fixed offset. -/
def truncationOrder (p : Fixed) (m : ℕ) (ε : ℚ) : ℕ :=
  truncationBlock p * (truncationOffset p + inputLog m ε)

/-- The primitive integral tolerance (4.2), in rational arithmetic. -/
def primitiveTolerance (p : Fixed) (m : ℕ) (ε : ℚ) : ℚ :=
  let s := truncationOrder p m ε
  ε / (3 * s * m * ((4 * p.A0 * p.F : ℕ) : ℚ) ^ s)

/-- The actual common quadrature level (3.11). -/
def level (p : Fixed) (m : ℕ) (ε : ℚ) : ℕ :=
  Oracle.totalLevelChoice (truncationOrder p m ε) p.C (primitiveTolerance p m ε)

/-- The actual common sample and oracle precision (3.13). -/
def precision (p : Fixed) (m : ℕ) (ε : ℚ) : ℕ :=
  let s := truncationOrder p m ε
  Oracle.samplePrecision s (Oracle.primitiveSampleTol s (level p m ε) p.C
    (primitiveTolerance p m ε))

lemma truncationBlock_pos (p : Fixed) : 1 ≤ truncationBlock p := le_max_left _ _

lemma truncationOrder_pos (p : Fixed) (m : ℕ) (ε : ℚ) : 1 ≤ truncationOrder p m ε := by
  have hb := truncationBlock_pos p
  have hl := binaryLog_pos (((m + 1 : ℕ) : ℚ) / ε)
  unfold truncationOrder inputLog
  nlinarith

lemma inputLog_le_order (p : Fixed) (m : ℕ) (ε : ℚ) :
    inputLog m ε ≤ truncationOrder p m ε := by
  have hb := truncationBlock_pos p
  unfold truncationOrder
  nlinarith

lemma truncationBlock_pow (p : Fixed) : (2 : ℚ) ≤ p.R ^ truncationBlock p := by
  have hR : 0 < p.R - 1 := by linarith [p.R_gt_one]
  have hc := (Nat.le_ceil (1 / (p.R - 1))).trans
    (show (⌈1 / (p.R - 1)⌉₊ : ℚ) ≤ (truncationBlock p : ℚ) by
      exact_mod_cast le_max_right 1 ⌈1 / (p.R - 1)⌉₊)
  have hm : 1 ≤ (truncationBlock p : ℚ) * (p.R - 1) := (div_le_iff₀ hR).mp hc
  have hb := one_add_mul_sub_le_pow (show (-1 : ℚ) ≤ p.R by linarith [p.R_gt_one])
    (truncationBlock p)
  linarith

/-- The computed order satisfies the rational truncation test (2.5). -/
theorem truncationOrder_sufficient (p : Fixed) (m : ℕ) (ε : ℚ) (hε : 0 < ε) :
    (2 * p.R * m * p.qPlus / (p.R - 1)) / p.R ^ truncationOrder p m ε ≤ ε / 3 := by
  have hR : 0 < p.R - 1 := by linarith [p.R_gt_one]
  have hRp : 0 < p.R := by linarith [p.R_gt_one]
  have hq := p.qPlus_pos
  have hK : 0 < 6 * p.R * p.qPlus / (p.R - 1) := by positivity
  have hx : 0 ≤ ((m + 1 : ℕ) : ℚ) / ε := by positivity
  have hk := binaryLog_pow (6 * p.R * p.qPlus / (p.R - 1))
  have hl := binaryLog_pow (((m + 1 : ℕ) : ℚ) / ε)
  have hp := mul_le_mul hk hl hx (by positivity : (0 : ℚ) ≤ 2 ^ truncationOffset p)
  have hblock := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2) (truncationBlock_pow p)
    (truncationOffset p + inputLog m ε)
  have heq : p.R ^ truncationOrder p m ε =
      (p.R ^ truncationBlock p) ^ (truncationOffset p + inputLog m ε) := by
    rw [truncationOrder, pow_mul]
  rw [← heq] at hblock
  have htarget : (6 * p.R * p.qPlus / (p.R - 1)) *
      (((m + 1 : ℕ) : ℚ) / ε) ≤ p.R ^ truncationOrder p m ε := by
    exact hp.trans (by simpa only [truncationOffset, inputLog, ← pow_add] using hblock)
  apply (div_le_iff₀ (pow_pos hRp _)).mpr
  have ht := (div_le_iff₀ hε).mp
    (show (6 * p.R * p.qPlus / (p.R - 1)) * ((m + 1 : ℕ) : ℚ) / ε ≤
      p.R ^ truncationOrder p m ε by simpa only [mul_div_assoc] using htarget)
  have hm : (m : ℚ) ≤ ((m + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.le_succ m
  have ht' := (mul_le_mul_of_nonneg_left hm hK.le).trans ht
  calc
    2 * p.R * (m : ℚ) * p.qPlus / (p.R - 1) =
        (6 * p.R * p.qPlus / (p.R - 1) * (m : ℚ)) / 3 := by ring
    _ ≤ ε / 3 * p.R ^ truncationOrder p m ε := by linarith

lemma primitiveTolerance_pos (p : Fixed) {m : ℕ} {ε : ℚ} (hm : 1 ≤ m) (hε : 0 < ε) :
    0 < primitiveTolerance p m ε := by
  have hs : (0 : ℚ) < truncationOrder p m ε := by exact_mod_cast truncationOrder_pos p m ε
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hA : (0 : ℚ) < (4 * p.A0 * p.F : ℕ) := by
    exact_mod_cast Nat.mul_pos
      (Nat.mul_pos (by decide : 0 < 4) (by have := p.A0_pos; omega))
      (by have := p.F_pos; omega)
  unfold primitiveTolerance
  positivity

/-- Explicit linear bound for the actual order, in the growing binary
logarithm; the two other quantities depend only on fixed parameters. -/
theorem truncationOrder_linear (p : Fixed) (m : ℕ) (ε : ℚ) :
    truncationOrder p m ε ≤
      truncationBlock p * (truncationOffset p + 1) * inputLog m ε := by
  have hk := binaryLog_pos (((m + 1 : ℕ) : ℚ) / ε)
  have hi : truncationOffset p + inputLog m ε ≤
      (truncationOffset p + 1) * inputLog m ε := by
    have hm := Nat.mul_le_mul_left (truncationOffset p) hk
    unfold inputLog
    nlinarith
  simpa only [truncationOrder, Nat.mul_assoc] using
    Nat.mul_le_mul_left (truncationBlock p) hi


/-- Fixed binary size of the coefficient-error budget base. -/
def momentBaseLog (p : Fixed) : ℕ := binaryLog ((4 * p.A0 * p.F : ℕ) : ℚ)

/-- Fixed binary size of the primitive Lipschitz budget base. -/
def budgetBaseLog (p : Fixed) : ℕ := binaryLog ((4 * p.C : ℕ) : ℚ)

/-- An explicit exponent bounding the reciprocal primitive tolerance. -/
def toleranceExponent (p : Fixed) (s : ℕ) : ℕ := (momentBaseLog p + 2) * s + 2

/-- An explicit linear envelope for the actual chosen total level. -/
def levelBound (p : Fixed) (s : ℕ) : ℕ :=
  2 * (1 + budgetBaseLog p * s + toleranceExponent p s)

/-- Reciprocal tolerance bound, proved for the actual tolerance (4.2). -/
theorem primitiveTolerance_inv_le (p : Fixed) {m : ℕ} {ε : ℚ}
    (hm : 1 ≤ m) (hε : 0 < ε) :
    1 / primitiveTolerance p m ε ≤
      (2 : ℚ) ^ toleranceExponent p (truncationOrder p m ε) := by
  let s := truncationOrder p m ε
  let k := inputLog m ε
  let b := momentBaseLog p
  have hs : (s : ℚ) ≤ (2 : ℚ) ^ s := by exact_mod_cast Nat.le_of_lt s.lt_two_pow_self
  have hk : (m : ℚ) / ε ≤ (2 : ℚ) ^ k := by
    apply le_trans _ (binaryLog_pow (((m + 1 : ℕ) : ℚ) / ε))
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ m) hε.le
  have hb : ((4 * p.A0 * p.F : ℕ) : ℚ) ^ s ≤ ((2 : ℚ) ^ b) ^ s :=
    pow_le_pow_left₀ (by positivity) (binaryLog_pow _) s
  have heq : 1 / primitiveTolerance p m ε =
      3 * (s : ℚ) * ((m : ℚ) / ε) * ((4 * p.A0 * p.F : ℕ) : ℚ) ^ s := by
    unfold primitiveTolerance
    dsimp only [s]
    field_simp
  rw [heq]
  have h3 : (3 : ℚ) ≤ 4 := by norm_num
  have hp : 3 * (s : ℚ) * ((m : ℚ) / ε) * ((4 * p.A0 * p.F : ℕ) : ℚ) ^ s ≤
      4 * (2 : ℚ) ^ s * (2 : ℚ) ^ k * ((2 : ℚ) ^ b) ^ s := by
    gcongr
  have he : 4 * (2 : ℚ) ^ s * (2 : ℚ) ^ k * ((2 : ℚ) ^ b) ^ s =
      (2 : ℚ) ^ (2 + s + k + b * s) := by
    rw [← pow_mul, show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add, ← pow_add]
  have hks : k ≤ s := inputLog_le_order p m ε
  have hexp : 2 + s + k + b * s ≤ toleranceExponent p s := by
    unfold toleranceExponent
    dsimp only [b]
    nlinarith
  exact hp.trans (he ▸ pow_le_pow_right₀ (by norm_num) hexp)

/-- The actual total-level choice is linear in the computed order. -/
theorem level_le (p : Fixed) {m : ℕ} {ε : ℚ} (hm : 1 ≤ m) (hε : 0 < ε) :
    level p m ε ≤ levelBound p (truncationOrder p m ε) := by
  let s := truncationOrder p m ε
  let τ := primitiveTolerance p m ε
  let b := budgetBaseLog p
  let T := toleranceExponent p s
  have hτ : 0 < τ := primitiveTolerance_pos p hm hε
  have hb : ((4 * p.C : ℕ) : ℚ) ^ s ≤ ((2 : ℚ) ^ b) ^ s :=
    pow_le_pow_left₀ (by positivity) (binaryLog_pow _) s
  have ht : 1 / τ ≤ (2 : ℚ) ^ T := primitiveTolerance_inv_le p hm hε
  have hbase : 2 * ((4 * p.C : ℕ) : ℚ) ^ s / τ ≤
      (2 : ℚ) ^ (1 + b * s + T) := by
    calc
      _ = 2 * ((4 * p.C : ℕ) : ℚ) ^ s * (1 / τ) := by ring
      _ ≤ 2 * ((2 : ℚ) ^ b) ^ s * (2 : ℚ) ^ T := by gcongr
      _ = _ := by simp only [pow_add, pow_mul, pow_one]
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ 2 * ((4 * p.C : ℕ) : ℚ) ^ s / τ) hbase 2
  apply Oracle.totalLevelChoice_le
  convert hp using 1 <;> simp only [← pow_mul, levelBound, T, b] <;> congr 1 <;> ring

/-- An explicit binary exponent for the reciprocal sample tolerance. -/
def sampleToleranceExponent (p : Fixed) (s J : ℕ) : ℕ :=
  (budgetBaseLog p + 3) * s + J + toleranceExponent p s + 3

/-- A rational minimum with positive arguments can be bounded through the
reciprocals of its two explicit arguments. -/
lemma inv_min_le {x y B : ℚ} (hx : 0 < x) (hy : 0 < y)
    (hxb : 1 / x ≤ B) (hyb : 1 / y ≤ B) : 1 / min x y ≤ B := by
  rcases le_total x y with h | h
  · simpa only [min_eq_left h] using hxb
  · simpa only [min_eq_right h] using hyb

/-- Reciprocal sample-error budget for the actual choices (3.11)–(3.13). -/
theorem primitiveSampleTol_inv_le (p : Fixed) {m : ℕ} {ε : ℚ}
    (hm : 1 ≤ m) (hε : 0 < ε) :
    1 / Oracle.primitiveSampleTol (truncationOrder p m ε) (level p m ε) p.C
        (primitiveTolerance p m ε) ≤
      (2 : ℚ) ^ sampleToleranceExponent p (truncationOrder p m ε) (level p m ε) := by
  let s := truncationOrder p m ε
  let J := level p m ε
  let τ := primitiveTolerance p m ε
  let b := budgetBaseLog p
  let T := toleranceExponent p s
  have hs : (s : ℚ) ≤ (2 : ℚ) ^ s := by exact_mod_cast Nat.le_of_lt s.lt_two_pow_self
  have hJ : (J : ℚ) + 1 ≤ (2 : ℚ) ^ (J + 1) := by
    exact_mod_cast Nat.le_of_lt (J + 1).lt_two_pow_self
  have hτ : 0 < τ := primitiveTolerance_pos p hm hε
  have hsp : (0 : ℚ) < s := by exact_mod_cast truncationOrder_pos p m ε
  have hCp : (0 : ℚ) < p.C := by exact_mod_cast p.C_pos
  have hb : (p.C : ℚ) ^ s ≤ ((2 : ℚ) ^ b) ^ s := by
    apply pow_le_pow_left₀ (by positivity)
    exact (show (p.C : ℚ) ≤ ((4 * p.C : ℕ) : ℚ) by push_cast; nlinarith).trans (binaryLog_pow _)
  have h3 : (3 : ℚ) ^ (s - 1) ≤ (2 : ℚ) ^ (2 * s) := by
    calc
      _ ≤ (4 : ℚ) ^ (s - 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ ≤ (4 : ℚ) ^ s := pow_le_pow_right₀ (by norm_num) (Nat.sub_le s 1)
      _ = _ := by rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]
  have ht : 1 / τ ≤ (2 : ℚ) ^ T := primitiveTolerance_inv_le p hm hε
  unfold Oracle.primitiveSampleTol
  apply inv_min_le (by positivity) (by positivity)
  · have h1 : 1 / (1 / (2 * ((J : ℚ) + 1))) ≤ (2 : ℚ) ^ (J + 2) := by
      have hp := mul_le_mul_of_nonneg_left hJ (by norm_num : (0 : ℚ) ≤ 2)
      convert hp using 1 <;> simp only [one_div, inv_inv, pow_add, pow_one] <;> ring
    apply h1.trans
    apply pow_le_pow_right₀ (by norm_num)
    dsimp [sampleToleranceExponent]
    omega
  · have heq : 1 / (τ / (4 * (s : ℚ) * ((J : ℚ) + 1) * 3 ^ (s - 1) * (p.C : ℚ) ^ s)) =
        4 * (s : ℚ) * ((J : ℚ) + 1) * 3 ^ (s - 1) * (p.C : ℚ) ^ s * (1 / τ) := by
      field_simp
    rw [heq]
    have hp : 4 * (s : ℚ) * ((J : ℚ) + 1) * 3 ^ (s - 1) * (p.C : ℚ) ^ s * (1 / τ) ≤
        4 * (2 : ℚ) ^ s * (2 : ℚ) ^ (J + 1) * (2 : ℚ) ^ (2 * s) * ((2 : ℚ) ^ b) ^ s * (2 : ℚ) ^ T := by
      gcongr
    convert hp using 1
    rw [← pow_mul, show (4 : ℚ) = 2 ^ 2 by norm_num]
    simp only [← pow_add, sampleToleranceExponent, T, b]
    congr 1
    ring

/-- Explicit linear envelope for the actual sample/oracle precision. -/
def precisionBound (p : Fixed) (s : ℕ) : ℕ :=
  (s + 2) + sampleToleranceExponent p s (levelBound p s)

/-- The actual chosen common precision is linear in the computed order. -/
theorem precision_le (p : Fixed) {m : ℕ} {ε : ℚ} (hm : 1 ≤ m) (hε : 0 < ε) :
    precision p m ε ≤ precisionBound p (truncationOrder p m ε) := by
  let s := truncationOrder p m ε
  let J := level p m ε
  let ζ := Oracle.primitiveSampleTol s J p.C (primitiveTolerance p m ε)
  let V := sampleToleranceExponent p s J
  let P := (s + 2) + V
  have hζ : 0 < ζ := Oracle.primitiveSampleTol_pos (truncationOrder_pos p m ε) p.C_pos
    (primitiveTolerance_pos p hm hε)
  have h2s : ((2 * s + 1 : ℕ) : ℚ) ≤ (2 : ℚ) ^ (s + 2) := by
    have hs : (s : ℚ) ≤ (2 : ℚ) ^ s := by exact_mod_cast Nat.le_of_lt s.lt_two_pow_self
    have hp : (1 : ℚ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
    rw [pow_add]
    norm_num
    push_cast
    nlinarith
  have hinv : 1 / ζ ≤ (2 : ℚ) ^ V := primitiveSampleTol_inv_le p hm hε
  have hratio : ((2 * s + 1 : ℕ) : ℚ) / ζ ≤ (2 : ℚ) ^ P := by
    have hp := mul_le_mul h2s hinv (by positivity : (0 : ℚ) ≤ 1 / ζ) (by positivity : (0 : ℚ) ≤ 2 ^ (s + 2))
    simpa only [P, pow_add, mul_one_div] using hp
  have hp : Oracle.samplePrecision s ζ ≤ P := by
    rw [Oracle.samplePrecision, max_le_iff]
    refine ⟨by dsimp [P]; omega, (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr ?_⟩
    rw [Nat.ceil_le]
    exact_mod_cast hratio
  apply hp.trans
  have hJ := level_le p hm hε
  dsimp only [P, V, precisionBound, sampleToleranceExponent, s, J]
  omega

/-- Both growing precision parameters have explicit linear bounds in the
single input binary logarithm. -/
theorem level_precision_linear (p : Fixed) {m : ℕ} {ε : ℚ} (hm : 1 ≤ m) (hε : 0 < ε) :
    ∃ D : ℕ, D = truncationBlock p * (truncationOffset p + 1) ∧
      level p m ε ≤ (2 * (budgetBaseLog p + momentBaseLog p + 2) + 6) *
        D * inputLog m ε ∧
      precision p m ε ≤ (3 * budgetBaseLog p + 3 * momentBaseLog p + 23) *
        D * inputLog m ε := by
  let s := truncationOrder p m ε
  let D := truncationBlock p * (truncationOffset p + 1)
  have hs := truncationOrder_linear p m ε
  have hsp : 1 ≤ s := truncationOrder_pos p m ε
  refine ⟨D, rfl, ?_, ?_⟩
  · have hj := level_le p hm hε
    have hJ : levelBound p s ≤ (2 * (budgetBaseLog p + momentBaseLog p + 2) + 6) * s := by
      unfold levelBound toleranceExponent
      nlinarith
    apply hj.trans
    apply hJ.trans
    simpa only [s, D, Nat.mul_assoc] using Nat.mul_le_mul_left
      (2 * (budgetBaseLog p + momentBaseLog p + 2) + 6) hs
  · have hp := precision_le p hm hε
    have hP : precisionBound p s ≤ (3 * budgetBaseLog p + 3 * momentBaseLog p + 23) * s := by
      unfold precisionBound sampleToleranceExponent levelBound toleranceExponent
      nlinarith
    apply hp.trans
    apply hP.trans
    simpa only [s, D, Nat.mul_assoc] using Nat.mul_le_mul_left
      (3 * budgetBaseLog p + 3 * momentBaseLog p + 23) hs


/-- Monotonicity of the computable binary logarithm. -/
lemma binaryLog_mono {x y : ℚ} (hxy : x ≤ y) : binaryLog x ≤ binaryLog y :=
  binaryLog_le (binaryLog_pos y) (hxy.trans (binaryLog_pow y))

/-- Multiplicative inputs add their binary-logarithmic bounds. -/
lemma binaryLog_mul_le {x y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    binaryLog (x * y) ≤ binaryLog x + binaryLog y := by
  apply binaryLog_le (by have := binaryLog_pos x; omega)
  rw [pow_add]
  exact mul_le_mul (binaryLog_pow x) (binaryLog_pow y) hy
    (by positivity : (0 : ℚ) ≤ 2 ^ binaryLog x)

/-- Bounded occurrence converts the factor-count logarithm to a variable-count
logarithm, with an additive fixed constant depending only on `c`. -/
theorem inputLog_le_variables {m n c : ℕ} {ε : ℚ} (hm : m ≤ c * n) (hε : 0 < ε) :
    inputLog m ε ≤ binaryLog ((c + 1 : ℕ) : ℚ) + inputLog n ε := by
  have hmn : ((m + 1 : ℕ) : ℚ) ≤ ((c + 1 : ℕ) : ℚ) * ((n + 1 : ℕ) : ℚ) := by
    have hmn' : m + 1 ≤ (c + 1) * (n + 1) := by nlinarith
    exact_mod_cast hmn'
  have hdiv : ((m + 1 : ℕ) : ℚ) / ε ≤
      ((c + 1 : ℕ) : ℚ) * (((n + 1 : ℕ) : ℚ) / ε) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hmn hε.le
  exact (binaryLog_mono hdiv).trans (binaryLog_mul_le (by positivity) (by positivity))

/-- The binary logarithm really is logarithmic: its exponential is bounded
by a linear function of its positive argument. -/
theorem binaryLog_power_le {x : ℚ} (hx : 1 ≤ x) :
    (2 : ℚ) ^ binaryLog x ≤ 4 * x := by
  let k := Nat.clog 2 ⌈x⌉₊
  by_cases hk : k ≤ 1
  · have he : binaryLog x = 1 := max_eq_left hk
    rw [he]
    norm_num
    linarith
  · have hkpos : 0 < k := by omega
    have hxceil : 1 < ⌈x⌉₊ := by
      by_contra h
      have hz := Nat.clog_of_right_le_one (by omega : ⌈x⌉₊ ≤ 1) 2
      dsimp [k] at hk
      omega
    have hb := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hxceil
    have he : (2 : ℕ) ^ k = 2 * 2 ^ k.pred := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hkpos, pow_succ]
      ring
    have hp : (2 : ℕ) ^ k < 2 * ⌈x⌉₊ := by rw [he]; exact Nat.mul_lt_mul_of_pos_left hb (by decide)
    have hlog : binaryLog x = k := max_eq_right (by omega)
    have hpq : (2 : ℚ) ^ binaryLog x < 2 * (⌈x⌉₊ : ℚ) := by
      rw [hlog]
      exact_mod_cast hp
    have hceil : (⌈x⌉₊ : ℚ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith

/-- Exponentially many local operations in the computed truncation order
are polynomially bounded in the numerical input ratio. -/
theorem two_pow_order_le (p : Fixed) {m : ℕ} {ε : ℚ}
    (hε : 0 < ε) (hεu : ε ≤ 1) :
    (2 : ℚ) ^ truncationOrder p m ε ≤
      (4 * (((m + 1 : ℕ) : ℚ) / ε)) ^
        (truncationBlock p * (truncationOffset p + 1)) := by
  let D := truncationBlock p * (truncationOffset p + 1)
  have hx : (1 : ℚ) ≤ ((m + 1 : ℕ) : ℚ) / ε := by
    apply (le_div_iff₀ hε).mpr
    have hm : (1 : ℚ) ≤ ((m + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    linarith
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ 2 ^ inputLog m ε)
    (binaryLog_power_le hx) D
  apply (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (truncationOrder_linear p m ε)).trans
  simpa only [D, ← pow_mul, Nat.mul_comm] using hp


/-- The actual tolerance pays exactly the coefficient budget in (4.3). -/
theorem primitiveTolerance_errorBudget (p : Fixed) {m : ℕ} {ε : ℚ}
    (hm : 1 ≤ m) (hε : 0 < ε) :
    let s := truncationOrder p m ε
    (s : ℚ) * m * (p.A0 : ℚ) ^ s * (p.F : ℚ) ^ s * (4 : ℚ) ^ s *
      primitiveTolerance p m ε = ε / 3 := by
  let s := truncationOrder p m ε
  have hs : (0 : ℚ) < s := by exact_mod_cast truncationOrder_pos p m ε
  have hmp : (0 : ℚ) < m := by exact_mod_cast hm
  have hA : (0 : ℚ) < p.A0 := by exact_mod_cast p.A0_pos
  have hF : (0 : ℚ) < p.F := by exact_mod_cast p.F_pos
  dsimp only
  unfold primitiveTolerance
  change (s : ℚ) * m * (p.A0 : ℚ) ^ s * (p.F : ℚ) ^ s * (4 : ℚ) ^ s *
    (ε / (3 * s * m * ((4 * p.A0 * p.F : ℕ) : ℚ) ^ s)) = ε / 3
  push_cast
  simp only [mul_pow]
  field_simp
  <;> ring

/-- The moment error `ξ=4^s τ` selected by the actual algorithm satisfies
Lemma 4.1's smallness requirement. -/
theorem primitiveTolerance_stability (p : Fixed) {m : ℕ} {ε : ℚ}
    (hm : 1 ≤ m) (hε : 0 < ε) (hεu : ε ≤ 1 / 2) :
    let s := truncationOrder p m ε
    (4 : ℚ) ^ s * primitiveTolerance p m ε ≤ 1 / (p.F : ℚ) ^ s := by
  let s := truncationOrder p m ε
  let ξ : ℚ := (4 : ℚ) ^ s * primitiveTolerance p m ε
  have hξ : 0 ≤ ξ := by have := primitiveTolerance_pos p hm hε; dsimp [ξ]; positivity
  have hs : (1 : ℚ) ≤ s := by exact_mod_cast truncationOrder_pos p m ε
  have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hA : (1 : ℚ) ≤ p.A0 := by exact_mod_cast p.A0_pos
  have hF : (0 : ℚ) < p.F := by exact_mod_cast p.F_pos
  have hprod : 1 ≤ (s : ℚ) * m * (p.A0 : ℚ) ^ s := by
    have hsm := mul_le_mul hs hm' (by norm_num : (0 : ℚ) ≤ 1)
      (by linarith : (0 : ℚ) ≤ s)
    have hAp : (1 : ℚ) ≤ (p.A0 : ℚ) ^ s := one_le_pow₀ hA
    simpa only [one_mul] using mul_le_mul hsm hAp (by norm_num : (0 : ℚ) ≤ 1)
      (by positivity : (0 : ℚ) ≤ (s : ℚ) * m)
  have he := primitiveTolerance_errorBudget p hm hε
  have he' : (s : ℚ) * m * (p.A0 : ℚ) ^ s * ((p.F : ℚ) ^ s * ξ) = ε / 3 := by
    dsimp [ξ, s]
    simpa only [mul_assoc] using he
  have hmul := mul_le_mul_of_nonneg_right hprod
    (by positivity : (0 : ℚ) ≤ (p.F : ℚ) ^ s * ξ)
  have hbound : (p.F : ℚ) ^ s * ξ ≤ 1 := by nlinarith
  exact (le_div_iff₀ (pow_pos hF s)).mpr (by simpa only [ξ, s, one_mul, mul_comm] using hbound)

/-- Real-cast form of the exact budget, matching the analytic stability and
support-extraction estimates. -/
theorem primitiveTolerance_errorBudget_real (p : Fixed) {m : ℕ} {ε : ℚ}
    (hm : 1 ≤ m) (hε : 0 < ε) :
    let s := truncationOrder p m ε
    (s : ℝ) * m * (p.A0 : ℝ) ^ s * (p.F : ℝ) ^ s * (4 : ℝ) ^ s *
      (primitiveTolerance p m ε : ℝ) = (ε : ℝ) / 3 := by
  have he := congrArg (fun x : ℚ => (x : ℝ)) (primitiveTolerance_errorBudget p hm hε)
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_div] using he

/-- Real-cast form of the actual smallness budget in Lemma 4.1. -/
theorem primitiveTolerance_stability_real (p : Fixed) {m : ℕ} {ε : ℚ}
    (hm : 1 ≤ m) (hε : 0 < ε) (hεu : ε ≤ 1 / 2) :
    let s := truncationOrder p m ε
    (4 : ℝ) ^ s * (primitiveTolerance p m ε : ℝ) ≤ (p.F : ℝ) ^ (-(s : ℝ)) := by
  dsimp only
  have hF : (0 : ℝ) ≤ p.F := by positivity
  rw [Real.rpow_neg hF, Real.rpow_natCast]
  have he := (Rat.cast_le (K := ℝ)).mpr (primitiveTolerance_stability p hm hε hεu)
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_div, Rat.cast_inv, Rat.cast_one, one_div] using he

end Paper08.Parameters
