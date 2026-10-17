import Paper37.MultisetDP
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Appendix C.3: sizes of the actual integer DP values

The estimates refer to the independent multiset sums in `MultisetDP` and,
through `run_correct`, to the materialized integer tables.  The common
denominator is the product in (C.12).  `Nat.size` is the actual binary length.
These bounds do not assert a Turing-machine simulation or an unproved cost
model for the arithmetic primitives.
-/
namespace Paper37.DP

open Finset

/-- A numeric bound for the marked aggregate, including states of count zero. -/
theorem S_le_power (a : ℕ → ℕ) (s : Finset ℕ) (A k u N : ℕ)
    (hN : 0 < N) (hcard : s.card ≤ N) (hsize : s.sum a + k ≤ N) :
    S a s A k u ≤ N ^ (2 * N + 1) := by
  have hk : k ≤ N := by omega
  calc
    _ ≤ k * G a s k u := S_le_mul_G _ _ _ _ _
    _ ≤ N * (N ^ N * N ^ N) := Nat.mul_le_mul hk
      (G_le_square_power _ _ _ _ _ hN hcard hsize)
    _ = _ := by simp [pow_add, pow_mul]; ring

/-- Convert a power bound into a bound for the binary integer encoding. -/
theorem binarySize_le_of_le_pow (x B e : ℕ) (hx : x ≤ B ^ e) :
    x.size ≤ e * B.size + 1 := by
  calc
    _ ≤ (B ^ e).size := Nat.size_le_size hx
    _ ≤ ((2 ^ B.size) ^ e).size := Nat.size_le_size
      (Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_size_self B)) e)
    _ = _ := by rw [← pow_mul, Nat.size_pow, Nat.mul_comm]

/-- The unmarked DP entry has at most `2 N size(N)+1` bits. -/
theorem G_binarySize (a : ℕ → ℕ) (s : Finset ℕ) (k u N : ℕ)
    (hN : 0 < N) (hcard : s.card ≤ N) (hsize : s.sum a + k ≤ N) :
    (G a s k u).size ≤ (2 * N) * N.size + 1 := by
  apply binarySize_le_of_le_pow
  simpa only [two_mul, pow_add] using G_le_square_power a s k u N hN hcard hsize

/-- The marked DP entry adds at most one factor `N` to the magnitude bound. -/
theorem S_binarySize (a : ℕ → ℕ) (s : Finset ℕ) (A k u N : ℕ)
    (hN : 0 < N) (hcard : s.card ≤ N) (hsize : s.sum a + k ≤ N) :
    (S a s A k u).size ≤ (2 * N + 1) * N.size + 1 :=
  binarySize_le_of_le_pow _ _ _ (S_le_power a s A k u N hN hcard hsize)

/-- Product of every possible empirical-likelihood denominator in (C.12). -/
def commonDenominator (N : ℕ) : ℕ := ∏ K ∈ Icc 1 N, K ^ K

@[simp] theorem commonDenominator_zero : commonDenominator 0 = 1 := by
  simp [commonDenominator]

/-- Every empirical denominator divides the one denominator used for the sum. -/
theorem power_dvd_commonDenominator (N K : ℕ) (hK : K ≤ N) :
    K ^ K ∣ commonDenominator N := by
  by_cases hz : K = 0
  · subst K; simp
  · exact dvd_prod_of_mem (fun k : ℕ => k ^ k) (mem_Icc.mpr ⟨by omega, hK⟩)

/-- The common denominator is positive, even at horizon zero. -/
theorem commonDenominator_pos (N : ℕ) : 0 < commonDenominator N := by
  unfold commonDenominator
  apply prod_pos
  intro K hK
  exact Nat.pow_pos (mem_Icc.mp hK).1

private theorem sum_Icc_one (N : ℕ) :
    ∑ K ∈ Icc 1 N, K = N * (N + 1) / 2 := by
  calc
    _ = ∑ K ∈ range (N + 1), K := by
      apply sum_subset
      · intro K hK
        simp only [mem_range, mem_Icc] at *
        omega
      · intro K hK hnot
        simp only [mem_range, mem_Icc, not_and] at *
        omega
    _ = _ := by rw [sum_range_id]; simp [Nat.mul_comm]

/-- The exponent in (C.12) is the triangular number `N(N+1)/2`. -/
theorem commonDenominator_le (N : ℕ) :
    commonDenominator N ≤ N ^ (N * (N + 1) / 2) := by
  unfold commonDenominator
  calc
    _ ≤ ∏ K ∈ Icc 1 N, N ^ K := by
      apply prod_le_prod'
      intro K hK
      exact Nat.pow_le_pow_left (mem_Icc.mp hK).2 K
    _ = _ := by rw [prod_pow_eq_pow_sum, sum_Icc_one]

/-- An explicit bound for the actual binary length of the common denominator. -/
theorem commonDenominator_binarySize (N : ℕ) :
    (commonDenominator N).size ≤ (N * (N + 1) / 2) * N.size + 1 :=
  binarySize_le_of_le_pow _ _ _ (commonDenominator_le N)

/-- A fully polynomial envelope, requiring no logarithmic asymptotics library. -/
theorem binarySize_le_self (N : ℕ) : N.size ≤ N := by
  exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := N))

/-- The common denominator has a cubic polynomial bound on binary length. -/
theorem commonDenominator_binarySize_polynomial (N : ℕ) :
    (commonDenominator N).size ≤ N * (N + 1) * N + 1 := by
  calc
    _ ≤ (N * (N + 1) / 2) * N.size + 1 := commonDenominator_binarySize N
    _ ≤ (N * (N + 1)) * N + 1 := Nat.add_le_add_right
      (Nat.mul_le_mul (Nat.div_le_self _ _) (binarySize_le_self N)) _

/-- All materialized states are covered, including infeasible count states:
`r≤N` and `k≤N` imply `r+k≤2N`. -/
theorem run_binarySize (N : ℕ) (a : ℕ → ℕ) (A d : ℕ)
    (k u : Fin (N + 1)) (hN : 0 < N) (hd : d ≤ N)
    (ha : (gapSet d).sum a ≤ N) :
    ((run N a A d)[k.val][u.val]).1.size ≤ (4 * N) * (2 * N).size + 1 ∧
    ((run N a A d)[k.val][u.val]).2.size ≤ (4 * N + 1) * (2 * N).size + 1 := by
  rw [run_correct]
  have hB : 0 < 2 * N := by omega
  have hcard : (gapSet d).card ≤ 2 * N := by
    simp only [gapSet, Nat.card_Icc]
    omega
  have hsize : (gapSet d).sum a + k.val ≤ 2 * N := by omega
  constructor
  · change (G a (gapSet d) k.val u.val).size ≤ _
    convert G_binarySize a (gapSet d) k.val u.val (2 * N) hB hcard hsize using 1; ring
  · change (S a (gapSet d) A k.val u.val).size ≤ _
    convert S_binarySize a (gapSet d) A k.val u.val (2 * N) hB hcard hsize using 1; ring

/-- The exact number of bits in the integer payload of one materialized layer.
Vector/object metadata is not included in this encoding quantity. -/
def layerBinarySize {N : ℕ} (v : Layer N) : ℕ :=
  ∑ k : Fin (N + 1), ∑ u : Fin (N + 1),
    ((v[k.val][u.val]).1.size + (v[k.val][u.val]).2.size)

/-- A rolling layer has quadratic many entries, each of logarithmic-linear
binary size.  The factor 2 covers retaining the old and the new layer. -/
theorem rollingBinarySize (N : ℕ) (a : ℕ → ℕ) (A d : ℕ)
    (hN : 0 < N) (hd : d ≤ N) (ha : (gapSet d).sum a ≤ N) :
    2 * layerBinarySize (run N a A d) ≤
      2 * (N + 1) ^ 2 * ((8 * N + 1) * (2 * N).size + 2) := by
  have h : layerBinarySize (run N a A d) ≤
      (N + 1) ^ 2 * ((8 * N + 1) * (2 * N).size + 2) := by
    unfold layerBinarySize
    calc
      _ ≤ ∑ _k : Fin (N + 1), ∑ _u : Fin (N + 1),
          ((8 * N + 1) * (2 * N).size + 2) := by
        apply sum_le_sum
        intro k hk
        apply sum_le_sum
        intro u hu
        have hb := run_binarySize N a A d k u hN hd ha
        calc
          _ ≤ ((4 * N) * (2 * N).size + 1) +
              ((4 * N + 1) * (2 * N).size + 1) := Nat.add_le_add hb.1 hb.2
          _ = _ := by ring
      _ = _ := by simp [pow_two, mul_assoc]
  simpa only [mul_assoc] using Nat.mul_le_mul_left 2 h

/-- The Pascal-table values used in the recurrence also have linear bit length. -/
theorem choose_binarySize (N k b : ℕ) (hk : k ≤ N) :
    (k.choose b).size ≤ N + 1 := by
  calc
    _ ≤ (2 ^ k).size := Nat.size_le_size (Nat.choose_le_two_pow k b)
    _ = k + 1 := Nat.size_pow
    _ ≤ _ := by omega

/-- All tabulated powers used by the DP have a polynomial binary length. -/
theorem selfPower_binarySize (N c : ℕ) (hc : c ≤ N) :
    (c ^ c).size ≤ N * N.size + 1 := by
  have hp : c ^ c ≤ N ^ N := by
    by_cases hN : N = 0
    · subst N; have : c = 0 := by omega
      subst c; rfl
    · exact (Nat.pow_le_pow_left hc c).trans
        (Nat.pow_le_pow_right (by omega) hc)
  exact binarySize_le_of_le_pow _ _ _ hp

/-- Scale one likelihood numerator to (C.12) by certified exact division. -/
def scaledNumerator (N p K : ℕ) : ℕ :=
  p * (commonDenominator N / K ^ K)

/-- Scaling preserves the exact rational represented by the integer pair. -/
theorem scaledNumerator_exact (N p K : ℕ) (hK : K ≤ N) :
    (scaledNumerator N p K : ℚ) / (commonDenominator N : ℚ) =
      (p : ℚ) / ((K ^ K : ℕ) : ℚ) := by
  have hD : (commonDenominator N : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (commonDenominator_pos N))
  have hpow : ((K ^ K : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.pow_self_pos (n := K)))
  apply (div_eq_div_iff hD hpow).mpr
  have he : scaledNumerator N p K * K ^ K = p * commonDenominator N := by
    unfold scaledNumerator
    rw [mul_assoc, Nat.div_mul_cancel (power_dvd_commonDenominator N K hK)]
  exact_mod_cast he

/-- Scaling grows a numerator by no more than the common denominator. -/
theorem scaledNumerator_le (N p K : ℕ) :
    scaledNumerator N p K ≤ p * commonDenominator N :=
  Nat.mul_le_mul_left p (Nat.div_le_self _ _)

/-- A finite sum of empirical-likelihood terms is represented by one exact
integer numerator over the common denominator. -/
theorem sum_scaledNumerator_exact {α : Type*} (N : ℕ) (t : Finset α)
    (p K : α → ℕ) (hK : ∀ i ∈ t, K i ≤ N) :
    ((∑ i ∈ t, scaledNumerator N (p i) (K i) : ℕ) : ℚ) /
        (commonDenominator N : ℚ) =
      ∑ i ∈ t, (p i : ℚ) / (((K i) ^ (K i) : ℕ) : ℚ) := by
  rw [Nat.cast_sum, sum_div]
  exact sum_congr rfl fun i hi => scaledNumerator_exact N (p i) (K i) (hK i hi)

/-- A common-denominator numerator is bounded by the number of terms times
the largest numerator times `D_N`; this applies to nonnegative prefix sums. -/
theorem sum_scaledNumerator_le {α : Type*} (N : ℕ) (t : Finset α)
    (p K : α → ℕ) (B : ℕ) (hp : ∀ i ∈ t, p i ≤ B) :
    ∑ i ∈ t, scaledNumerator N (p i) (K i) ≤
      t.card * B * commonDenominator N := by
  calc
    _ ≤ ∑ _i ∈ t, B * commonDenominator N := by
      apply sum_le_sum
      intro i hi
      exact (scaledNumerator_le N (p i) (K i)).trans
        (Nat.mul_le_mul_right _ (hp i hi))
    _ = _ := by simp [mul_assoc]

end Paper37.DP
