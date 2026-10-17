import Paper08.Moments
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size

/-!
# Executable exact arithmetic used by the algorithm in §4

The recurrence and the final Taylor polynomial are rational programs.  The
common-denominator theorem concerns the denominators of their actual outputs,
rather than a certificate postulated alongside those outputs.
-/

open scoped BigOperators

namespace Paper08
namespace Moments

/-- Executable version of recurrence (2.15).  Only earlier coefficients are
used, so this is a terminating rational-arithmetic program. -/
def rationalLogCoeff (M : ℕ → ℚ) (j : ℕ) : ℚ :=
  if h : j = 0 then 0 else
    M j - (1 / (j : ℚ)) *
      ∑ i : Fin j, (i.val : ℚ) * rationalLogCoeff M i.val * M (j - i.val)
termination_by j
decreasing_by exact i.isLt

@[simp] theorem rationalLogCoeff_zero (M : ℕ → ℚ) : rationalLogCoeff M 0 = 0 := by
  rw [rationalLogCoeff]
  simp

/-- The program satisfies exactly the recurrence used for logarithmic
coefficients, with no hypothesis about a purported program output. -/
theorem rationalLogCoeff_eq (M : ℕ → ℚ) {j : ℕ} (hj : 1 ≤ j) :
    rationalLogCoeff M j = M j - (1 / (j : ℚ)) *
      ∑ i ∈ Finset.range j, (i : ℚ) * rationalLogCoeff M i * M (j - i) := by
  rw [rationalLogCoeff, dif_neg (by omega)]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℚ) * rationalLogCoeff M i * M (j - i))]

/-- Casting the executable rational recurrence gives the real recurrence. -/
theorem rationalLogCoeff_cast_recurrence (M : ℕ → ℚ) :
    Recurrence (fun j => (M j : ℝ)) (fun j => (rationalLogCoeff M j : ℝ)) := by
  constructor
  · simp
  · intro j hj
    dsimp only
    rw [rationalLogCoeff_eq M hj]
    push_cast
    rfl

/-- Consequently the rational program agrees with every real sequence that
satisfies the exact recurrence for the same rational moments. -/
theorem rationalLogCoeff_cast_eq (M : ℕ → ℚ) (d : ℕ → ℝ)
    (hd : Recurrence (fun j => (M j : ℝ)) d) (j : ℕ) :
    (rationalLogCoeff M j : ℝ) = d j :=
  recurrence_unique (rationalLogCoeff_cast_recurrence M) hd j

/-- Sums of rationals with denominators dividing `D` have the same common
denominator. -/
theorem rational_sum_den_dvd {α : Type*} (S : Finset α) (f : α → ℚ) (D : ℕ)
    (h : ∀ a ∈ S, (f a).den ∣ D) : (∑ a ∈ S, f a).den ∣ D := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    apply (Rat.add_den_dvd_lcm _ _).trans
    exact Nat.lcm_dvd (h a (Finset.mem_insert_self _ _))
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

/-- Multiplication by an integer cannot enlarge the denominator. -/
theorem rational_nat_mul_den_dvd (k : ℕ) (x : ℚ) : ((k : ℚ) * x).den ∣ x.den := by
  simpa only [Rat.den_natCast, one_mul] using Rat.mul_den_dvd (k : ℚ) x

/-- Division by a positive integer enlarges a common denominator by at most
that integer. -/
theorem rational_div_nat_den_dvd (x : ℚ) {j : ℕ} (hj : 0 < j) :
    (x / (j : ℚ)).den ∣ x.den * j := by
  simpa only [div_eq_mul_inv, Rat.inv_natCast_den_of_pos hj] using
    Rat.mul_den_dvd x ((j : ℚ)⁻¹)

/-- The denominator envelope in §4 for the coefficient of degree `j`. -/
def coefficientDenominator (D j : ℕ) : ℕ := D ^ j * Nat.factorial j

lemma coefficientDenominator_mono (D : ℕ) {i j : ℕ} (hij : i ≤ j) :
    coefficientDenominator D i ∣ coefficientDenominator D j := by
  exact Nat.mul_dvd_mul (pow_dvd_pow D hij) (Nat.factorial_dvd_factorial hij)

lemma denominator_step_dvd (D : ℕ) {i j : ℕ} (hij : i < j) :
    coefficientDenominator D i * D * j ∣ coefficientDenominator D j := by
  have hj : 1 ≤ j := by omega
  have hfac : Nat.factorial i * j ∣ Nat.factorial j := by
    have hfi := Nat.factorial_dvd_factorial (show i ≤ j - 1 by omega)
    have h := Nat.mul_dvd_mul hfi (dvd_refl j)
    have heq : j = (j - 1) + 1 := by omega
    conv_rhs => rw [heq, Nat.factorial_succ]
    simpa only [Nat.sub_add_cancel hj, Nat.mul_comm] using h
  have hpow : D ^ (i + 1) ∣ D ^ j := pow_dvd_pow D (by omega)
  have h := Nat.mul_dvd_mul hpow hfac
  simpa only [coefficientDenominator, pow_succ, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using h

/-- Actual canonical denominators returned by the rational recurrence divide
`D^j j!`, whenever every input moment through degree `j` has denominator
dividing `D`.  This is the induction claimed after (4.4). -/
theorem rationalLogCoeff_den_dvd (M : ℕ → ℚ) (D : ℕ) (j : ℕ)
    (hD : 1 ≤ D) (hM : ∀ i, 1 ≤ i → i ≤ j → (M i).den ∣ D) :
    (rationalLogCoeff M j).den ∣ coefficientDenominator D j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases hj : j = 0
    · subst j
      simp [coefficientDenominator]
    have hjp : 1 ≤ j := by omega
    rw [rationalLogCoeff_eq M hjp]
    apply (Rat.sub_den_dvd_lcm _ _).trans
    apply Nat.lcm_dvd
    · exact (hM j hjp le_rfl).trans
        ((dvd_pow_self D (by omega : j ≠ 0)).trans (dvd_mul_right _ _))
    · have hsum :
          (∑ i ∈ Finset.range j, (i : ℚ) * rationalLogCoeff M i * M (j - i)).den ∣
            D ^ j * Nat.factorial (j - 1) := by
        apply rational_sum_den_dvd
        intro i hi
        have hij : i < j := Finset.mem_range.mp hi
        have hji : 1 ≤ j - i := by omega
        have hcoeff := ih i hij (fun k hk hki => hM k hk (by omega))
        have hprod := (Rat.mul_den_dvd ((i : ℚ) * rationalLogCoeff M i) (M (j - i))).trans
          (Nat.mul_dvd_mul ((rational_nat_mul_den_dvd i _).trans hcoeff)
            (hM (j - i) hji (by omega)))
        have hpow : D ^ (i + 1) ∣ D ^ j := pow_dvd_pow D (by omega)
        have hfac := Nat.factorial_dvd_factorial (show i ≤ j - 1 by omega)
        have hdvd := Nat.mul_dvd_mul hpow hfac
        have hdvd' : coefficientDenominator D i * D ∣ D ^ j * Nat.factorial (j - 1) := by
          simpa only [coefficientDenominator, pow_succ, Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm] using hdvd
        exact hprod.trans hdvd'
      have hdiv := (rational_div_nat_den_dvd
        (∑ i ∈ Finset.range j, (i : ℚ) * rationalLogCoeff M i * M (j - i)) hjp).trans
        (Nat.mul_dvd_mul hsum (dvd_refl j))
      have hfac : (D ^ j * Nat.factorial (j - 1)) * j = coefficientDenominator D j := by
        unfold coefficientDenominator
        have heq : j = (j - 1) + 1 := by omega
        conv_rhs => rw [heq, Nat.factorial_succ]
        simp only [Nat.sub_add_cancel hjp]
        ring
      rw [hfac] at hdiv
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hdiv

/-- All coefficients through degree `s`, including coefficients computed for
different subcollections, share the denominator `D^s s!`. -/
theorem rationalLogCoeff_common_denominator (M : ℕ → ℚ) (D s : ℕ)
    (hD : 1 ≤ D) (hM : ∀ i, 1 ≤ i → i ≤ s → (M i).den ∣ D)
    {j : ℕ} (hj : j ≤ s) :
    (rationalLogCoeff M j).den ∣ coefficientDenominator D s :=
  (rationalLogCoeff_den_dvd M D j hD (fun i hi hij => hM i hi (hij.trans hj))).trans
    (coefficientDenominator_mono D hj)


/-- A uniform binary envelope for factorials, convenient for converting exact
denominator divisibility to a bit bound. -/
lemma factorial_le_two_pow_square (s : ℕ) : Nat.factorial s ≤ 2 ^ (s * s) := by
  calc
    Nat.factorial s ≤ s ^ s := Nat.factorial_le_pow s
    _ ≤ (2 ^ s) ^ s := Nat.pow_le_pow_left (Nat.le_of_lt s.lt_two_pow_self) s
    _ = 2 ^ (s * s) := (pow_mul 2 s s).symm

/-- The common denominator of §4 is bounded by an explicit power of two. -/
theorem common_denominator_le_two_pow (P s r J : ℕ) :
    coefficientDenominator (denomBound P s r J) s ≤
      2 ^ ((P * s + r * J) * s + s ^ 3 + s ^ 2) := by
  have hf := factorial_le_two_pow_square s
  have hD : denomBound P s r J ≤ 2 ^ (P * s + r * J + s * s) := by
    unfold denomBound
    simpa only [pow_add] using Nat.mul_le_mul_left (2 ^ (P * s + r * J)) hf
  have hp := Nat.mul_le_mul (Nat.pow_le_pow_left hD s) hf
  unfold coefficientDenominator
  convert hp using 1 <;> simp only [← pow_mul, ← pow_add] <;> congr 1 <;> ring

/-- Actual denominators of all computed logarithmic coefficients through
order `s` have the explicit polynomial bit bound used in (4.5). -/
theorem rationalLogCoeff_den_size_le (M : ℕ → ℚ) (P s r J : ℕ)
    (hM : ∀ i, 1 ≤ i → i ≤ s → (M i).den ∣ denomBound P s r J)
    {j : ℕ} (hj : j ≤ s) :
    (rationalLogCoeff M j).den.size ≤
      (P * s + r * J) * s + s ^ 3 + s ^ 2 + 1 := by
  have hd := rationalLogCoeff_common_denominator M (denomBound P s r J) s
    (denomBound_pos P s r J) hM hj
  have hpos : 0 < coefficientDenominator (denomBound P s r J) s := by
    unfold coefficientDenominator
    exact Nat.mul_pos (pow_pos (by have := denomBound_pos P s r J; omega) _)
      (Nat.factorial_pos _)
  have hle := (Nat.le_of_dvd hpos hd).trans (common_denominator_le_two_pow P s r J)
  apply Nat.size_le.mpr
  rw [pow_succ]
  have hp : 0 < (2 : ℕ) ^ ((P * s + r * J) * s + s ^ 3 + s ^ 2) := by positivity
  omega

end Moments
namespace Algorithm

/-- The finite rational Taylor polynomial `P_N(t)` from §4. -/
def expPolynomial (t : ℚ) (N : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (N + 1), t ^ j / (Nat.factorial j : ℚ)

/-- A rational upper bound for the Taylor remainder on `[-1/2,1/2]`. -/
def expTailBound (N : ℕ) : ℚ :=
  (1 / 2 : ℚ) ^ N / (Nat.factorial (N + 1) : ℚ)

/-- The analytic error bound of the actual rational Taylor program. -/
theorem expPolynomial_error (t : ℚ) (N : ℕ) (ht : |(t : ℝ)| ≤ 1 / 2) :
    |(expPolynomial t N : ℝ) - Real.exp (t : ℝ)| ≤ (expTailBound N : ℝ) := by
  have h := Real.exp_bound (x := (t : ℝ)) (by linarith : |(t : ℝ)| ≤ 1)
    (by omega : 0 < N + 1)
  have hpow : |(t : ℝ)| ^ (N + 1) ≤ (1 / 2 : ℝ) ^ (N + 1) :=
    pow_le_pow_left₀ (abs_nonneg _) ht _
  have hfac : (0 : ℝ) < Nat.factorial (N + 1) := by positivity
  have hn : (0 : ℝ) < N + 1 := by positivity
  have hratio : (((N + 1).succ : ℕ) : ℝ) /
      ((Nat.factorial (N + 1) : ℝ) * ((N + 1 : ℕ) : ℝ)) ≤
        2 / (Nat.factorial (N + 1) : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hfac (by exact_mod_cast (by omega : 0 < N + 1))) hfac).mpr
    push_cast
    nlinarith
  have hmul := mul_le_mul hpow hratio (by positivity)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)
  have heq : (1 / 2 : ℝ) ^ (N + 1) * (2 / (Nat.factorial (N + 1) : ℝ)) =
      (1 / 2 : ℝ) ^ N / (Nat.factorial (N + 1) : ℝ) := by
    rw [pow_succ]
    ring
  rw [heq] at hmul
  have hcast : (expPolynomial t N : ℝ) =
      ∑ j ∈ Finset.range (N + 1), (t : ℝ) ^ j / (Nat.factorial j : ℝ) := by
    simp only [expPolynomial, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  rw [hcast, abs_sub_comm]
  exact h.trans (by simpa only [expTailBound, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using hmul)

/-- A computable scaling exponent obtained from a binary ceiling logarithm. -/
def exponentialScale (L : ℚ) : ℕ := Nat.clog 2 ⌈2 * |L|⌉₊

/-- The scaling exponent puts the actual argument in `[-1/2,1/2]`. -/
theorem exponentialScale_bound (L : ℚ) :
    |L / (2 : ℚ) ^ exponentialScale L| ≤ 1 / 2 := by
  have hceil : 2 * |L| ≤ (⌈2 * |L|⌉₊ : ℚ) := Nat.le_ceil _
  have hp : (⌈2 * |L|⌉₊ : ℚ) ≤ (2 : ℚ) ^ exponentialScale L := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) ⌈2 * |L|⌉₊
  rw [abs_div, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ exponentialScale L)]
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ exponentialScale L)).mpr
  linarith

/-- The number of Taylor terms is chosen by rational arithmetic. -/
def exponentialDegree (a : ℚ) : ℕ := Nat.clog 2 ⌈1 / a⌉₊

/-- The computable choice of Taylor degree meets the requested rational
absolute tolerance. -/
theorem expTailBound_degree_le {a : ℚ} (ha : 0 < a) :
    expTailBound (exponentialDegree a) ≤ a := by
  have hceil : 1 / a ≤ (⌈1 / a⌉₊ : ℚ) := Nat.le_ceil _
  have hp : (⌈1 / a⌉₊ : ℚ) ≤ (2 : ℚ) ^ exponentialDegree a := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) ⌈1 / a⌉₊
  have h1 : 1 / a ≤ (2 : ℚ) ^ exponentialDegree a := hceil.trans hp
  have h2 : (1 / 2 : ℚ) ^ exponentialDegree a ≤ a := by
    rw [div_pow, one_pow]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ exponentialDegree a)).mpr
    have := (div_le_iff₀ ha).mp h1
    nlinarith
  unfold expTailBound
  have hfac : (1 : ℚ) ≤ Nat.factorial (exponentialDegree a + 1) := by
    exact_mod_cast Nat.factorial_pos (exponentialDegree a + 1)
  exact (div_le_self (by positivity : (0 : ℚ) ≤ (1 / 2) ^ exponentialDegree a) hfac).trans h2

/-- The rational output construction in step 4, including its effective
choices of the scaling exponent and Taylor degree. -/
def rationalExp (L ε : ℚ) : ℚ :=
  let h := exponentialScale L
  let a := ε / (12 * (2 : ℚ) ^ h)
  expPolynomial (L / (2 : ℚ) ^ h) (exponentialDegree a) ^ (2 ^ h)


/-- `log` is 4-Lipschitz on `[1/4,∞)`, by rescaling the basic unit-bound
logarithm inequality. -/
theorem log_abs_sub_le_four {x y : ℝ} (hx : 1 / 4 ≤ x) (hy : 1 / 4 ≤ y) :
    |Real.log x - Real.log y| ≤ 4 * |x - y| := by
  have h := Paper08.log_abs_sub_le_abs_sub (by linarith : 1 ≤ 4 * x)
    (by linarith : 1 ≤ 4 * y)
  have hxp : 0 < x := by linarith
  have hyp : 0 < y := by linarith
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hxp.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hyp.ne'] at h
  have heq : 4 * x - 4 * y = 4 * (x - y) := by ring
  simpa [heq, abs_mul] using h

/-- The Taylor polynomial is positive, and has the required logarithmic
accuracy, under the paper's final-step tolerance. -/
theorem expPolynomial_log_error (t : ℚ) (N : ℕ) {a : ℝ}
    (ht : |(t : ℝ)| ≤ 1 / 2) (ha : a ≤ 1 / 24)
    (herr : (expTailBound N : ℝ) ≤ a) :
    0 < (expPolynomial t N : ℝ) ∧
      |Real.log (expPolynomial t N : ℝ) - (t : ℝ)| ≤ 4 * a := by
  have he := expPolynomial_error t N ht
  have heb : (1 / 2 : ℝ) ≤ Real.exp (t : ℝ) := by
    have hl := (abs_le.mp ht).1
    linarith [Real.add_one_le_exp (t : ℝ)]
  have hp : (1 / 4 : ℝ) ≤ (expPolynomial t N : ℝ) := by
    have he' := (abs_le.mp (he.trans herr)).1
    linarith
  refine ⟨by linarith, ?_⟩
  calc
    |Real.log (expPolynomial t N : ℝ) - (t : ℝ)| =
        |Real.log (expPolynomial t N : ℝ) - Real.log (Real.exp (t : ℝ))| := by rw [Real.log_exp]
    _ ≤ 4 * |(expPolynomial t N : ℝ) - Real.exp (t : ℝ)| :=
      log_abs_sub_le_four hp (by linarith)
    _ ≤ 4 * a := by linarith

/-- The actual executable final output is a positive rational and achieves
logarithmic error `ε/3`. No accuracy or positivity of its output is assumed. -/
theorem rationalExp_spec (L ε : ℚ) (hε : 0 < ε) (hεu : ε ≤ 1 / 2) :
    0 < rationalExp L ε ∧
      |Real.log (rationalExp L ε : ℝ) - (L : ℝ)| ≤ (ε : ℝ) / 3 := by
  let h := exponentialScale L
  let a : ℚ := ε / (12 * (2 : ℚ) ^ h)
  let t : ℚ := L / (2 : ℚ) ^ h
  let N := exponentialDegree a
  have ha : 0 < a := by dsimp [a]; positivity
  have hau : a ≤ 1 / 24 := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 12 * 2 ^ h)).mpr
    have hp : (1 : ℚ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
    nlinarith
  have ht : |(t : ℝ)| ≤ 1 / 2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (exponentialScale_bound L)
    simpa only [t, h, Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hh
  have htail : (expTailBound N : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast expTailBound_degree_le ha
  have hauR : (a : ℝ) ≤ 1 / 24 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hau
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hh
  have hs := expPolynomial_log_error t N (a := (a : ℝ)) ht hauR htail
  have hp : 0 < expPolynomial t N := by exact_mod_cast hs.1
  have hout : rationalExp L ε = expPolynomial t N ^ (2 ^ h) := rfl
  constructor
  · rw [hout]
    positivity
  · rw [hout, Rat.cast_pow, Real.log_pow]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
    have htcast : (t : ℝ) = (L : ℝ) / (2 : ℝ) ^ h := by
      simp only [t, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
    have heq : ((2 ^ h : ℕ) : ℝ) * Real.log (expPolynomial t N : ℝ) - (L : ℝ) =
        (2 : ℝ) ^ h * (Real.log (expPolynomial t N : ℝ) - (t : ℝ)) := by
      rw [htcast, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
    rw [heq, abs_mul, abs_of_pos h2]
    have hmul := mul_le_mul_of_nonneg_left hs.2 h2.le
    have haCast : (a : ℝ) = (ε : ℝ) / (12 * (2 : ℝ) ^ h) := by
      simp only [a, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
    rw [haCast] at hmul
    convert hmul using 1 <;> field_simp <;> ring

/-- The exact scaling power is at most linear in `|L|`; in particular,
raising the rational Taylor sum to this power has polynomial output length. -/
theorem exponentialScale_power_bound (L : ℚ) :
    ((2 ^ exponentialScale L : ℕ) : ℚ) ≤ 4 * |L| + 2 := by
  let x : ℕ := ⌈2 * |L|⌉₊
  by_cases hx : x ≤ 1
  · have hh : exponentialScale L = 0 := Nat.clog_of_right_le_one hx 2
    rw [hh]
    norm_num
    linarith [abs_nonneg L]
  · have hx2 : 1 < x := by omega
    have hc : 0 < Nat.clog 2 x := Nat.clog_pos (by decide) (by omega)
    have hb := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hx2
    have heq : 2 ^ Nat.clog 2 x = 2 * 2 ^ (Nat.clog 2 x).pred := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hc, pow_succ]
      ring
    have hp : (2 ^ Nat.clog 2 x : ℕ) < 2 * x := by rw [heq]; omega
    have hceil : (x : ℚ) < 2 * |L| + 1 := Nat.ceil_lt_add_one (by positivity)
    have hpq : ((2 ^ exponentialScale L : ℕ) : ℚ) < 2 * (x : ℚ) := by
      exact_mod_cast hp
    linarith

end Algorithm
end Paper08
