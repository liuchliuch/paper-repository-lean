import Paper08.BitComplexity
import Mathlib.Data.List.OfFn

/-!
# Operand-sensitive arithmetic expressions

The syntax records every rational field operation. `work` charges each node
by the cube of its actual input encoding lengths, the ordinary schoolbook
rational-arithmetic envelope (including normalization). This is an explicit
arithmetic cost model, rather than a claim about the Lean compiler or CPU time.
-/

open scoped BigOperators
namespace Paper08.RationalProgram
open BitComplexity

/-- Maximum of the two canonical component lengths. -/
def height (q : ℚ) : ℕ := max q.num.natAbs.size q.den.size

lemma num_le_pow_height (q : ℚ) : q.num.natAbs ≤ 2 ^ height q :=
  (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left _ _))

lemma den_le_pow_height (q : ℚ) : q.den ≤ 2 ^ height q :=
  (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right _ _))

lemma bits_le_height (q : ℚ) : rationalBits q ≤ 2 * height q + 1 := by
  unfold rationalBits height
  have h₁ := le_max_left q.num.natAbs.size q.den.size
  have h₂ := le_max_right q.num.natAbs.size q.den.size
  omega

lemma divInt_num_le (a b : ℤ) : (Rat.divInt a b).num.natAbs ≤ a.natAbs := by
  by_cases hb : b = 0
  · simp [hb]
  by_cases ha : a = 0
  · simp [ha]
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr ha) (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd a hb))

lemma divInt_den_le (a b : ℤ) (hb : b ≠ 0) : (Rat.divInt a b).den ≤ b.natAbs := by
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr hb)
  have h := Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd a b)
  simpa only [Int.natAbs_natCast] using h

lemma height_divInt_le (a b : ℤ) (K : ℕ)
    (ha : a.natAbs ≤ 2 ^ K) (hb : b.natAbs ≤ 2 ^ K) :
    height (Rat.divInt a b) ≤ K + 1 := by
  by_cases hb0 : b = 0
  · simp [hb0, height]
  have hn := (divInt_num_le a b).trans ha
  have hd := (divInt_den_le a b hb0).trans hb
  unfold height
  apply max_le
  · apply Nat.size_le.mpr
    rw [pow_succ]
    have hp : 0 < (2 : ℕ) ^ K := by positivity
    omega
  · apply Nat.size_le.mpr
    rw [pow_succ]
    have hp : 0 < (2 : ℕ) ^ K := by positivity
    omega

lemma height_add (x y : ℚ) : height (x + y) ≤ height x + height y + 2 := by
  have hx₁ := num_le_pow_height x
  have hx₂ := den_le_pow_height x
  have hy₁ := num_le_pow_height y
  have hy₂ := den_le_pow_height y
  have hnum : (x.num * (y.den : ℤ) + y.num * (x.den : ℤ)).natAbs ≤
      2 ^ (height x + height y + 1) := by
    have h₁ := Nat.mul_le_mul hx₁ hy₂
    have h₂ := Nat.mul_le_mul hy₁ hx₂
    have ha := Int.natAbs_add_le (x.num * (y.den : ℤ)) (y.num * (x.den : ℤ))
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at ha
    rw [pow_add, pow_one, pow_add]
    nlinarith
  have hden : ((x.den : ℤ) * (y.den : ℤ)).natAbs ≤ 2 ^ (height x + height y + 1) := by
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    have hh := Nat.mul_le_mul hx₂ hy₂
    rw [pow_add, pow_one, pow_add]
    nlinarith
  have h := height_divInt_le _ _ (height x + height y + 1) hnum hden
  have heq : x + y = Rat.divInt (x.num * (y.den : ℤ) + y.num * (x.den : ℤ))
      ((x.den : ℤ) * (y.den : ℤ)) := by
    rw [Rat.add_def, Rat.normalize_eq_mkRat, Rat.mkRat_eq_divInt]
    norm_cast
  rw [heq]
  exact h

lemma height_neg (x : ℚ) : height (-x) = height x := by simp [height]

lemma height_sub (x y : ℚ) : height (x - y) ≤ height x + height y + 2 := by
  simpa only [sub_eq_add_neg, height_neg] using height_add x (-y)

lemma height_mul (x y : ℚ) : height (x * y) ≤ height x + height y + 2 := by
  have hn := Nat.mul_le_mul (num_le_pow_height x) (num_le_pow_height y)
  have hd := Nat.mul_le_mul (den_le_pow_height x) (den_le_pow_height y)
  rw [← pow_add] at hn hd
  have hnum : (x.num * y.num).natAbs ≤ 2 ^ (height x + height y) := by
    simpa only [Int.natAbs_mul] using hn
  have hden : ((x.den : ℤ) * (y.den : ℤ)).natAbs ≤ 2 ^ (height x + height y) := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hd
  have h := height_divInt_le _ _ (height x + height y) hnum hden
  have heq : x * y = Rat.divInt (x.num * y.num) ((x.den : ℤ) * (y.den : ℤ)) := by
    rw [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt]
    norm_cast
  rw [heq]
  omega

lemma height_div (x y : ℚ) : height (x / y) ≤ height x + height y + 2 := by
  have hn := Nat.mul_le_mul (num_le_pow_height x) (den_le_pow_height y)
  have hd := Nat.mul_le_mul (den_le_pow_height x) (num_le_pow_height y)
  rw [← pow_add] at hn hd
  have hnum : (x.num * (y.den : ℤ)).natAbs ≤ 2 ^ (height x + height y) := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hn
  have hden : ((x.den : ℤ) * y.num).natAbs ≤ 2 ^ (height x + height y) := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hd
  have h := height_divInt_le _ _ (height x + height y) hnum hden
  rw [Rat.div_def']
  omega


lemma abs_le_pow_height (q : ℚ) : |q| ≤ (2 : ℚ) ^ height q := by
  have hn : (q.num.natAbs : ℚ) ≤ (2 : ℚ) ^ height q := by exact_mod_cast num_le_pow_height q
  rw [Moments.rational_num_natAbs] at hn
  have hd : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  nlinarith [abs_nonneg q]

lemma height_floor (q : ℚ) : height (⌊q⌋ : ℚ) ≤ height q + 2 := by
  have hq := abs_le_pow_height q
  have hl := Int.floor_le q
  have hu := Int.lt_floor_add_one q
  have hn : |(⌊q⌋ : ℚ)| ≤ (2 : ℚ) ^ height q + 1 := by
    have hqa := abs_le.mp hq
    apply abs_le.mpr
    constructor <;> linarith
  have hn' : (⌊q⌋.natAbs : ℚ) ≤ (2 : ℚ) ^ (height q + 1) := by
    have he : (⌊q⌋.natAbs : ℚ) = |(⌊q⌋ : ℚ)| := by simp only [Nat.cast_natAbs, Int.cast_abs]
    rw [he, pow_succ]
    have hp : (1 : ℚ) ≤ 2 ^ height q := one_le_pow₀ (by norm_num)
    linarith
  have hnat : ⌊q⌋.natAbs ≤ 2 ^ (height q + 1) := by exact_mod_cast hn'
  have hsize : ⌊q⌋.natAbs.size ≤ height q + 2 := by
    apply Nat.size_le.mpr
    rw [show height q + 2 = (height q + 1) + 1 by omega, pow_succ]
    have hp : 0 < (2 : ℕ) ^ (height q + 1) := by positivity
    omega
  simpa [height] using max_le hsize (show 1 ≤ height q + 2 by omega)

inductive Op where
  | add | sub | mul | div | min | max
  deriving DecidableEq

def Op.eval : Op → ℚ → ℚ → ℚ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .min, x, y => Min.min x y
  | .max, x, y => Max.max x y

lemma Op.height_le (o : Op) (x y : ℚ) : height (o.eval x y) ≤ height x + height y + 2 := by
  cases o
  · exact height_add x y
  · exact height_sub x y
  · exact height_mul x y
  · exact height_div x y
  · rcases le_total x y with h | h
    · simp only [Op.eval, min_eq_left h]; omega
    · simp only [Op.eval, min_eq_right h]; omega
  · rcases le_total x y with h | h
    · simp only [Op.eval, max_eq_right h]; omega
    · simp only [Op.eval, max_eq_left h]; omega

/-- A concrete rational arithmetic expression. Leaves are input rationals. -/
inductive Expr where
  | atom : ℚ → Expr
  | node : Op → Expr → Expr → Expr
  | floor : Expr → Expr

def Expr.eval : Expr → ℚ
  | .atom q => q
  | .node o x y => o.eval x.eval y.eval
  | .floor x => (⌊x.eval⌋ : ℚ)

def Expr.operations : Expr → ℕ
  | .atom _ => 0
  | .node _ x y => x.operations + y.operations + 1
  | .floor x => x.operations + 1

/-- Actual bit-sensitive work charged at every executed field operation. -/
def Expr.work : Expr → ℕ
  | .atom _ => 0
  | .node _ x y => x.work + y.work + (rationalBits x.eval + rationalBits y.eval + 1) ^ 3
  | .floor x => x.work + (rationalBits x.eval + 1) ^ 3

/-- Maximum input component encoding length. -/
def Expr.inputHeight : Expr → ℕ
  | .atom q => height q
  | .node _ x y => max x.inputHeight y.inputHeight
  | .floor x => x.inputHeight

/-- Every intermediate numerator and denominator in the actual expression
is bounded by a polynomial in the expression size and input encoding length. -/
theorem Expr.height_le (e : Expr) :
    height e.eval ≤ e.inputHeight * (e.operations + 1) + 2 * e.operations := by
  induction e with
  | atom q => simp [Expr.eval, Expr.inputHeight, Expr.operations]
  | node o x y hx hy =>
    have h := o.height_le x.eval y.eval
    have hx' := (Nat.mul_le_mul_right (x.operations + 1) (le_max_left x.inputHeight y.inputHeight))
    have hy' := (Nat.mul_le_mul_right (y.operations + 1) (le_max_right x.inputHeight y.inputHeight))
    dsimp only [Expr.eval, Expr.inputHeight, Expr.operations]
    nlinarith
  | floor x hx =>
    have h := height_floor x.eval
    dsimp only [Expr.eval, Expr.inputHeight, Expr.operations]
    nlinarith

/-- Polynomial upper bound for the operand-sensitive cost of the actual
arithmetic expression. No bound on its result or cost is supplied as an input. -/
theorem Expr.work_le (e : Expr) :
    e.work ≤ e.operations *
      (4 * ((e.inputHeight + 2) * (e.operations + 1)) + 3) ^ 3 := by
  induction e with
  | atom q => simp [Expr.work, Expr.operations]
  | node o x y hx hy =>
    let B := (max x.inputHeight y.inputHeight + 2) * (x.operations + y.operations + 2)
    have hxb : (x.inputHeight + 2) * (x.operations + 1) ≤ B := by
      dsimp [B]
      exact Nat.mul_le_mul (Nat.add_le_add_right (le_max_left _ _) 2) (by omega)
    have hyb : (y.inputHeight + 2) * (y.operations + 1) ≤ B := by
      dsimp [B]
      exact Nat.mul_le_mul (Nat.add_le_add_right (le_max_right _ _) 2) (by omega)
    have hxh : height x.eval ≤ B := by have := x.height_le; nlinarith
    have hyh : height y.eval ≤ B := by have := y.height_le; nlinarith
    have hxs : rationalBits x.eval ≤ 2 * B + 1 := (bits_le_height _).trans (by omega)
    have hys : rationalBits y.eval ≤ 2 * B + 1 := (bits_le_height _).trans (by omega)
    have hc : (rationalBits x.eval + rationalBits y.eval + 1) ^ 3 ≤ (4 * B + 3) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    have hxw := hx.trans (Nat.mul_le_mul_left x.operations
      (Nat.pow_le_pow_left (by omega : 4 * ((x.inputHeight + 2) * (x.operations + 1)) + 3 ≤ 4 * B + 3) 3))
    have hyw := hy.trans (Nat.mul_le_mul_left y.operations
      (Nat.pow_le_pow_left (by omega : 4 * ((y.inputHeight + 2) * (y.operations + 1)) + 3 ≤ 4 * B + 3) 3))
    dsimp only [Expr.work, Expr.operations, Expr.inputHeight]
    change x.work + y.work + _ ≤ (x.operations + y.operations + 1) * (4 * B + 3) ^ 3
    nlinarith
  | floor x hx =>
    let B := (x.inputHeight + 2) * (x.operations + 2)
    have hxb : (x.inputHeight + 2) * (x.operations + 1) ≤ B := by
      exact Nat.mul_le_mul_left _ (by omega)
    have hxh : height x.eval ≤ B := by have := x.height_le; nlinarith
    have hxs : rationalBits x.eval ≤ 2 * B + 1 := (bits_le_height _).trans (by omega)
    have hc : (rationalBits x.eval + 1) ^ 3 ≤ (4 * B + 3) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    have hxw := hx.trans (Nat.mul_le_mul_left x.operations
      (Nat.pow_le_pow_left (by omega : 4 * ((x.inputHeight + 2) * (x.operations + 1)) + 3 ≤ 4 * B + 3) 3))
    dsimp only [Expr.work, Expr.operations, Expr.inputHeight]
    change x.work + _ ≤ (x.operations + 1) * (4 * B + 3) ^ 3
    nlinarith

end Paper08.RationalProgram
