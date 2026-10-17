import Paper08.PrimitiveProgram
import Paper08.RationalRecurrenceProgram
import Paper08.BoundedRuleQ

/-! # Reflection of the actual sampled logarithms and rational quadrature

Every arithmetic operation is represented in the expression, including powers
of two, projection, flooring, the finite logarithm series and factorials.
Only actual oracle answers are input leaves.
-/
open scoped BigOperators
namespace Paper08.PrimitiveExpressions
open RationalProgram PrimitiveProgram CellGrid RationalQuadrature

lemma height_two : height (2 : ℚ) = 2 := by
  have hs : Nat.size 2 = 2 := by simpa using (Nat.size_pow (n := 1))
  norm_num [height, hs]

/-- Powers of two are constructed by rational multiplication. -/
def twoPower (P : ℕ) : Expr := natPower (.atom 2) P

def dyadExpr (P : ℕ) (e : Expr) : Expr :=
  .node .div (.floor (.node .mul e (twoPower P))) (twoPower P)

def project12Expr (e : Expr) : Expr := .node .min (.atom 2) (.node .max (.atom 1) e)
def project01Expr (e : Expr) : Expr := .node .min (.atom 1) (.node .max (.atom 0) e)

def logSeriesExpr (N : ℕ) (v : Expr) : Expr :=
  .node .mul (.atom 2) (sumSet (Finset.range N) fun j =>
    .node .div (natPower v (2*j+1)) (.atom ((2*j+1:ℕ):ℚ)))

def logSampleExpr (P : ℕ) (e : Expr) : Expr :=
  project01Expr (dyadExpr (P+1) (logSeriesExpr (P+2)
    (.node .div (.node .sub e (.atom 1)) (.node .add e (.atom 1)))))

def primitiveSampleExpr (P a : ℕ) (answer : ℚ) : Expr :=
  dyadExpr P (natPower (logSampleExpr P (project12Expr (.atom answer))) a)

@[simp] theorem twoPower_eval (P : ℕ) : (twoPower P).eval = (2:ℚ)^P := by
  simp [twoPower, Expr.eval]
@[simp] theorem dyadExpr_eval (P : ℕ) (e : Expr) :
    (dyadExpr P e).eval = Oracle.dyadQ P e.eval := by
  simp [dyadExpr, Expr.eval, Op.eval, Oracle.dyadQ]
@[simp] theorem project12Expr_eval (e : Expr) :
    (project12Expr e).eval = Oracle.project12Q e.eval := rfl
@[simp] theorem project01Expr_eval (e : Expr) :
    (project01Expr e).eval = Oracle.project01Q e.eval := rfl
@[simp] theorem logSeriesExpr_eval (N : ℕ) (e : Expr) :
    (logSeriesExpr N e).eval = Oracle.logSeriesQ N e.eval := by
  simp only [logSeriesExpr, Expr.eval, Op.eval, sumSet_eval, natPower_eval]
  simp [Oracle.logSeriesQ, Nat.cast_add, Nat.cast_mul]
@[simp] theorem logSampleExpr_eval (P : ℕ) (e : Expr) :
    (logSampleExpr P e).eval = Oracle.logSampleQ P e.eval := by
  simp only [logSampleExpr, project01Expr_eval, dyadExpr_eval, logSeriesExpr_eval,
    Expr.eval, Op.eval, Oracle.logSampleQ]
@[simp] theorem primitiveSampleExpr_eval (P a : ℕ) (answer : ℚ) :
    (primitiveSampleExpr P a answer).eval = Oracle.primitiveSampleQ P a answer := by
  simp [primitiveSampleExpr, Oracle.primitiveSampleQ, Expr.eval]

@[simp] theorem twoPower_operations (P : ℕ) : (twoPower P).operations = P := by
  simp [twoPower, Expr.operations]
@[simp] theorem dyadExpr_operations (P : ℕ) (e : Expr) :
    (dyadExpr P e).operations = e.operations+2*P+3 := by
  simp [dyadExpr, Expr.operations]; ring
@[simp] theorem project12Expr_operations (e : Expr) :
    (project12Expr e).operations = e.operations+2 := by simp [project12Expr, Expr.operations]
@[simp] theorem project01Expr_operations (e : Expr) :
    (project01Expr e).operations = e.operations+2 := by simp [project01Expr, Expr.operations]

theorem logSeriesExpr_operations (N : ℕ) (v : Expr) :
    (logSeriesExpr N v).operations ≤ 2*(N+1)^2*(v.operations+3) := by
  have hsum := sumSet_operations_le (Finset.range N) (fun j =>
    Expr.node .div (natPower v (2*j+1)) (.atom ((2*j+1:ℕ):ℚ)))
    (N := (2*N+1)*(v.operations+1)+1) (by
      intro j hj
      simp only [Expr.operations, natPower_operations]
      have hjN := Finset.mem_range.mp hj
      nlinarith)
  simp only [Finset.card_range] at hsum
  simp only [logSeriesExpr, Expr.operations]
  nlinarith

theorem primitiveSampleExpr_operations (P a : ℕ) (answer : ℚ) :
    (primitiveSampleExpr P a answer).operations ≤ 40*(a+1)*(P+3)^2 := by
  have hv : (Expr.node .div
      (.node .sub (project12Expr (.atom answer)) (.atom 1))
      (.node .add (project12Expr (.atom answer)) (.atom 1))).operations = 7 := by
    simp [Expr.operations, project12Expr_operations]
  have hh := logSeriesExpr_operations (P+2)
    (.node .div (.node .sub (project12Expr (.atom answer)) (.atom 1))
      (.node .add (project12Expr (.atom answer)) (.atom 1)))
  rw [hv] at hh
  simp only [primitiveSampleExpr, dyadExpr_operations, natPower_operations,
    logSampleExpr, project01Expr_operations, dyadExpr_operations]
  nlinarith [sq_nonneg (P:ℤ)]

lemma height_nat (j : ℕ) : height (j : ℚ) ≤ j+1 :=
  RationalRecurrenceProgram.height_natCast_le (le_refl j)

theorem twoPower_inputHeight (P : ℕ) : (twoPower P).inputHeight ≤ 2 := by
  exact natPower_inputHeight _ P (by decide) (by simp only [Expr.inputHeight, height_two]; omega)
theorem dyadExpr_inputHeight (P : ℕ) (e : Expr) {H : ℕ}
    (hH : 2 ≤ H) (he : e.inputHeight ≤ H) : (dyadExpr P e).inputHeight ≤ H := by
  exact max_le (max_le he ((twoPower_inputHeight P).trans hH)) ((twoPower_inputHeight P).trans hH)
theorem project12Expr_inputHeight (e : Expr) {H : ℕ} (hH : 2 ≤ H)
    (he : e.inputHeight ≤ H) : (project12Expr e).inputHeight ≤ H := by
  change max (height 2) (max (height 1) e.inputHeight) ≤ H
  have h2 := height_two
  have h1 : height (1 : ℚ) = 1 := by simp [height]
  have h0 : height (0 : ℚ) = 1 := by simp [height]
  simp only [h2, h1, h0]
  omega
theorem project01Expr_inputHeight (e : Expr) {H : ℕ} (hH : 1 ≤ H)
    (he : e.inputHeight ≤ H) : (project01Expr e).inputHeight ≤ H := by
  change max (height 1) (max (height 0) e.inputHeight) ≤ H
  have h2 := height_two
  have h1 : height (1 : ℚ) = 1 := by simp [height]
  have h0 : height (0 : ℚ) = 1 := by simp [height]
  simp only [h2, h1, h0]
  omega

theorem logSeriesExpr_inputHeight (N : ℕ) (v : Expr) {H : ℕ}
    (hH : 2*N+2 ≤ H) (hv : v.inputHeight ≤ H) : (logSeriesExpr N v).inputHeight ≤ H := by
  change max (height 2) (sumSet (Finset.range N) _).inputHeight ≤ H
  have h2 := height_two
  apply max_le (by rw [h2]; omega)
  apply sumSet_inputHeight _ _ (by omega)
  intro j hj
  apply max_le (natPower_inputHeight _ _ (by omega) hv)
  exact (height_nat _).trans (by have := Finset.mem_range.mp hj; omega)

theorem primitiveSampleExpr_inputHeight (P a : ℕ) (answer : ℚ) {H : ℕ}
    (hH : 2*P+6 ≤ H) (ha : height answer ≤ H) :
    (primitiveSampleExpr P a answer).inputHeight ≤ H := by
  apply dyadExpr_inputHeight P _ (by omega)
  apply natPower_inputHeight _ _ (by omega)
  apply project01Expr_inputHeight _ (by omega)
  apply dyadExpr_inputHeight (P+1) _ (by omega)
  apply logSeriesExpr_inputHeight _ _ (by omega)
  change max (max (project12Expr (.atom answer)).inputHeight (height 1))
    (max (project12Expr (.atom answer)).inputHeight (height 1)) ≤ H
  have hp := project12Expr_inputHeight (.atom answer) (by omega : 2 ≤ H) ha
  have h2 := height_two
  have h1 : height (1 : ℚ) = 1 := by simp [height]
  have h0 : height (0 : ℚ) = 1 := by simp [height]
  simp only [h2, h1, h0]
  omega

end Paper08.PrimitiveExpressions
