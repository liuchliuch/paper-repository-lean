import Paper08.FPTASAlgorithm
import Paper08.BoundedRuleQ
import Paper08.BitComplexity
import Mathlib.Data.Nat.Factorial.BigOperators

/-! # Representation bounds for the actual moment and coefficient programs -/

open scoped BigOperators

namespace Paper08.MomentArithmetic
open PrimitiveMomentsQ

/-- The product of local factorials is absorbed by the total degree factorial. -/
theorem factorialWeight_dvd_degree_factorial {m : ℕ} (d : Fin m →₀ ℕ) :
    factorialWeight d ∣ Nat.factorial d.degree := by
  exact Nat.prod_factorial_dvd_factorial_sum d.support (fun e => d e)

/-- Canonical denominator of the actual sparse primitive program. -/
theorem primitiveQ_den_dvd {n m r s C : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes)
    (d : Fin m →₀ ℕ) (hd : d.degree ≤ s) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (primitiveQ scopes query d s C τ).den ∣ 2 ^ (P * s + r * J) := by
  have ht : d.support.card ≤ s := (Support.finsupp_support_card_le_degree d).trans hd
  exact RationalQuadrature.primitiveRuleQ_den_dvd _ (fun i => hscopes _) _ _ ht τ

/-- The actual multinomial moment program has the common denominator
`D0 = 2^(Ps+rJ) s!`, including its exactly-one constant moment. -/
theorem momentQ_den_dvd {n m r s C j : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes)
    (B : Finset (Fin m)) (hj : j ≤ s) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (momentQ scopes query B j s C τ).den ∣ Moments.denomBound P s r J := by
  let J := Oracle.totalLevelChoice s C τ
  let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
  dsimp only
  by_cases hj0 : j = 0
  · subst j
    simp
  rw [momentQ, if_neg hj0]
  apply Moments.rational_sum_den_dvd
  intro d hd
  have hdeg : d.degree ≤ s := by
    have hh := (Finset.mem_finsuppAntidiag'.mp hd).1
    change (∑ e ∈ d.support, d e) = j at hh
    change (∑ e ∈ d.support, d e) ≤ s
    omega
  have hprimitive := primitiveQ_den_dvd (C := C) scopes hscopes query d hdeg τ
  have hweight : factorialWeight d ∣ Nat.factorial s :=
    (factorialWeight_dvd_degree_factorial d).trans (Nat.factorial_dvd_factorial hdeg)
  exact (Moments.rational_div_nat_den_dvd _ (factorialWeight_pos d)).trans
    (Nat.mul_dvd_mul hprimitive hweight)

/-- The actual local coefficient program shares the §4 denominator for every
subcollection and degree through `s`. -/
theorem localCoeff_den_dvd {n m r s C j : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes)
    (B : Finset (Fin m)) (hj : j ≤ s) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (FPTASAlgorithm.localCoeff scopes query B j s C τ).den ∣
      Moments.coefficientDenominator (Moments.denomBound P s r J) s := by
  dsimp only
  apply Moments.rationalLogCoeff_common_denominator _ _ s
    (Moments.denomBound_pos _ _ _ _)
    (fun i _ hi => momentQ_den_dvd scopes hscopes query B hi τ) hj

/-- The accumulated logarithm approximation itself retains that common
reduced denominator across all supports and all degrees. -/
theorem logApprox_den_dvd {n m r c s C : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (FPTASAlgorithm.logApprox scopes query r c s C τ).den ∣
      Moments.coefficientDenominator (Moments.denomBound P s r J) s := by
  dsimp only
  unfold FPTASAlgorithm.logApprox
  apply Moments.rational_sum_den_dvd
  intro j hj
  apply Moments.rational_sum_den_dvd
  intro AB _
  have hd := localCoeff_den_dvd (C := C) scopes hscopes query AB.2 (Finset.mem_Icc.mp hj).2 τ
  apply (Rat.mul_den_dvd _ _).trans
  simpa only [Rat.den_pow, show (-1 : ℚ).den = 1 by norm_num, one_pow, one_mul] using hd

/-- Actual local coefficients obey the complete numerator/denominator bit
bound, using the computed quadrature's proved magnitude bounds. -/
theorem localCoeff_bits_le {n m r s C j : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes)
    (B : Finset (Fin m)) (hB : B.card ≤ s) (hj : j ≤ s) (hs : 1 ≤ s) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    BitComplexity.rationalBits (FPTASAlgorithm.localCoeff scopes query B j s C τ) ≤
      ((J + 4) * s * s + s) + 2 * ((P * s + r * J) * s + s ^ 3 + s ^ 2) + 3 := by
  dsimp only
  exact BitComplexity.rationalLogCoeff_bits_le _ _ s r _ _
    (fun i _ hi => momentQ_den_dvd scopes hscopes query B hi τ)
    (fun i _ hi => BoundedRuleQ.abs_momentQ_le_coarse scopes query B hB hi hs τ) hj


/-- The actual nested degree/support loops, flattened only for bounding
arbitrary partial sums of the same computed terms. -/
def occurrences {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (r c s : ℕ) :
    Finset (Σ _j : ℕ, Finset (Fin m) × Finset (Fin m)) :=
  (Finset.Icc 1 s).sigma (fun j => FPTASAlgorithm.pairs scopes r c s j)

def occurrenceValue {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (s C : ℕ) (τ : ℚ) (o : Σ _j : ℕ, Finset (Fin m) × Finset (Fin m)) : ℚ :=
  (-1 : ℚ) ^ (o.2.1.card - o.2.2.card) * FPTASAlgorithm.localCoeff scopes query o.2.2 o.1 s C τ

lemma logApprox_eq_sum {n m r c s C : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (τ : ℚ) :
    FPTASAlgorithm.logApprox scopes query r c s C τ =
      ∑ o ∈ occurrences scopes r c s, occurrenceValue scopes query s C τ o := by
  simp only [occurrences, Finset.sum_sigma', occurrenceValue, FPTASAlgorithm.logApprox]

lemma occurrences_card_le {n m r c s : ℕ} (scopes : Fin m → Finset (Fin n)) :
    (occurrences scopes r c s).card ≤ s * (m * (8 * FPTASAlgorithm.degreeBound r c) ^ s) := by
  unfold occurrences
  rw [Finset.card_sigma]
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 s, m * (8 * FPTASAlgorithm.degreeBound r c) ^ s :=
      Finset.sum_le_sum (fun j _ => FPTASAlgorithm.pairs_card scopes)
    _ = _ := by simp

lemma occurrences_card_le_two_pow {n m r c s : ℕ} (scopes : Fin m → Finset (Fin n)) :
    (occurrences scopes r c s).card ≤
      2 ^ (s + m.size + (8 * FPTASAlgorithm.degreeBound r c).size * s) := by
  have h := Nat.mul_le_mul
    (Nat.lt_two_pow_self (n := s)).le
    (Nat.mul_le_mul (Nat.lt_size_self m).le
      (Nat.pow_le_pow_left (Nat.lt_size_self (8 * FPTASAlgorithm.degreeBound r c)).le s))
  apply (occurrences_card_le scopes).trans
  simpa only [← pow_mul, ← pow_add, Nat.add_assoc] using h

lemma occurrence_den_dvd {n m r c s C : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes) (τ : ℚ)
    (o : Σ _j : ℕ, Finset (Fin m) × Finset (Fin m)) (ho : o ∈ occurrences scopes r c s) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (occurrenceValue scopes query s C τ o).den ∣
      Moments.coefficientDenominator (Moments.denomBound P s r J) s := by
  have hj := (Finset.mem_sigma.mp ho).1
  have hd := localCoeff_den_dvd (C := C) scopes hscopes query o.2.2 (Finset.mem_Icc.mp hj).2 τ
  apply (Rat.mul_den_dvd _ _).trans
  simpa only [Rat.den_pow, show (-1 : ℚ).den = 1 by norm_num, one_pow, one_mul] using hd

lemma occurrence_abs_le {n m r c s C : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (hs : 1 ≤ s) (τ : ℚ)
    (o : Σ _j : ℕ, Finset (Fin m) × Finset (Fin m)) (ho : o ∈ occurrences scopes r c s) :
    |occurrenceValue scopes query s C τ o| ≤
      (2 : ℚ) ^ ((Oracle.totalLevelChoice s C τ + 4) * s * s + s) := by
  have hj := (Finset.mem_sigma.mp ho).1
  have hb := FPTASAlgorithm.pair_subset scopes (Finset.mem_sigma.mp ho).2
  have hB : o.2.2.card ≤ s := (Finset.card_le_card hb.1).trans hb.2
  have h := Moments.rationalLogCoeff_abs_le_two_pow
    (fun i => momentQ scopes query o.2.2 i s C τ) (Oracle.totalLevelChoice s C τ + 3) s
    (fun i _ hi => BoundedRuleQ.abs_momentQ_le_coarse scopes query o.2.2 hB hi hs τ)
    (Finset.mem_Icc.mp hj).2
  simpa only [occurrenceValue, FPTASAlgorithm.localCoeff, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul] using h

/-- Every partial support-extraction sum has a polynomial encoding bound,
using the denominators and magnitudes of the actual computed moments. -/
theorem logApprox_partial_bits_le {n m r c s C : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes) (hs : 1 ≤ s) (τ : ℚ)
    (T : Finset (Σ _j : ℕ, Finset (Fin m) × Finset (Fin m)))
    (hT : T ⊆ occurrences scopes r c s) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    BitComplexity.rationalBits (∑ o ∈ T, occurrenceValue scopes query s C τ o) ≤
      ((J + 4) * s * s + s) +
        (s + m.size + (8 * FPTASAlgorithm.degreeBound r c).size * s) +
        2 * ((P * s + r * J) * s + s ^ 3 + s ^ 2) + 3 := by
  let J := Oracle.totalLevelChoice s C τ
  let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
  dsimp only
  apply BitComplexity.partial_sum_bits_le (occurrences scopes r c s) T hT
    (occurrenceValue scopes query s C τ)
    (Moments.coefficientDenominator (Moments.denomBound P s r J) s)
    ((J + 4) * s * s + s)
    ((P * s + r * J) * s + s ^ 3 + s ^ 2)
    (s + m.size + (8 * FPTASAlgorithm.degreeBound r c).size * s)
  · unfold Moments.coefficientDenominator
    have hp : 0 < Moments.denomBound P s r J := Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Moments.denomBound_pos P s r J)
    exact Nat.mul_pos (pow_pos hp _) (Nat.factorial_pos _)
  · exact Moments.common_denominator_le_two_pow P s r J
  · exact occurrence_den_dvd scopes hscopes query τ
  · exact occurrence_abs_le scopes query hs τ
  · exact occurrences_card_le_two_pow scopes

/-- In particular, the actual argument sent to final exponentiation has that
same encoding bound. -/
theorem logApprox_bits_le {n m r c s C : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes) (hs : 1 ≤ s) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    BitComplexity.rationalBits (FPTASAlgorithm.logApprox scopes query r c s C τ) ≤
      ((J + 4) * s * s + s) +
        (s + m.size + (8 * FPTASAlgorithm.degreeBound r c).size * s) +
        2 * ((P * s + r * J) * s + s ^ 3 + s ^ 2) + 3 := by
  rw [logApprox_eq_sum scopes query τ]
  exact logApprox_partial_bits_le scopes hscopes query hs τ _ Finset.Subset.rfl

end Paper08.MomentArithmetic
