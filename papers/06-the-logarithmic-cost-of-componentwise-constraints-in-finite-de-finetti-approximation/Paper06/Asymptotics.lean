import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Bertrand

/-!
The number-theoretic and asymptotic parts of (16)--(19).
The results in this file concern explicit prime and sample-size sequences.  They do not
assert existence of an admissible probability law or import the external prime-field
game estimate used in Corollary 3.6.
-/

open Filter Asymptotics Real
open scoped Topology

namespace Paper06

/-- The least prime greater than or equal to a natural-number threshold. -/
noncomputable def leastPrimeGE (N : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes N)

theorem leastPrimeGE_spec (N : ℕ) :
    N ≤ leastPrimeGE N ∧ Nat.Prime (leastPrimeGE N) :=
  Nat.find_spec (Nat.exists_infinite_primes N)

theorem leastPrimeGE_le {N p : ℕ} (hp : Nat.Prime p) (hNp : N ≤ p) :
    leastPrimeGE N ≤ p :=
  Nat.find_min' _ ⟨hNp, hp⟩

/-- The factor-two assertion in the paragraph preceding (16), including leastness. -/
theorem leastPrimeGE_bertrand (N : ℕ) (hN : 0 < N) :
    N ≤ leastPrimeGE N ∧ leastPrimeGE N ≤ 2 * N ∧ Nat.Prime (leastPrimeGE N) := by
  obtain ⟨p, hp, hNp, hpN⟩ := Nat.exists_prime_lt_and_le_two_mul N (ne_of_gt hN)
  exact ⟨(leastPrimeGE_spec N).1, (leastPrimeGE_le hp hNp.le).trans hpN,
    (leastPrimeGE_spec N).2⟩

/-- The prime used in (16), with `A = 2e` and `p = 1/(1/2-θ)`. -/
noncomputable def polynomialPrime (A p : ℝ) (n : ℕ) : ℕ :=
  leastPrimeGE ⌈(A * ((n : ℝ) - 1)) ^ p⌉₊

noncomputable def polynomialAlphabet (A p : ℝ) (n : ℕ) : ℕ :=
  polynomialPrime A p n ^ 2

theorem polynomialPrime_prime (A p : ℝ) (n : ℕ) :
    Nat.Prime (polynomialPrime A p n) :=
  (leastPrimeGE_spec _).2

theorem polynomialPrime_threshold (A p : ℝ) (n : ℕ) :
    (A * ((n : ℝ) - 1)) ^ p ≤ polynomialPrime A p n :=
  (Nat.le_ceil _).trans (by
    dsimp [polynomialPrime]
    exact_mod_cast (leastPrimeGE_spec ⌈(A * ((n : ℝ) - 1)) ^ p⌉₊).1)

/-- The selected prime satisfies the parameter inequality required by Theorem 3.1. -/
theorem polynomialPrime_parameter {A p : ℝ} (hA : 0 ≤ A) (hp : 0 < p)
    {n : ℕ} (hn : 1 ≤ n) :
    A * ((n : ℝ) - 1) ≤ (polynomialPrime A p n : ℝ) ^ (1 / p) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : 0 ≤ A * ((n : ℝ) - 1) := mul_nonneg hA (by linarith)
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hb p)
    (polynomialPrime_threshold A p n) (by positivity : 0 ≤ 1 / p)
  simpa only [← Real.rpow_mul hb, mul_one_div_cancel (ne_of_gt hp), Real.rpow_one] using h

/-- Explicit bounds proving the polynomial prime growth claimed in (16). -/
theorem polynomialPrime_bounds {A p : ℝ} (hA : 2 ≤ A) (hp : 0 < p)
    {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ p ≤ polynomialPrime A p n ∧
      (polynomialPrime A p n : ℝ) ≤ (4 * A ^ p) * (n : ℝ) ^ p := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : (1 : ℝ) ≤ A * ((n : ℝ) - 1) := by nlinarith
  have hthreshold : (1 : ℝ) ≤ (A * ((n : ℝ) - 1)) ^ p :=
    Real.one_le_rpow hbase hp.le
  have hceil : 0 < ⌈(A * ((n : ℝ) - 1)) ^ p⌉₊ := by
    exact Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one hthreshold)
  have hprime := (leastPrimeGE_bertrand _ hceil).2.1
  have hceilR : (⌈(A * ((n : ℝ) - 1)) ^ p⌉₊ : ℝ) ≤
      2 * (A * ((n : ℝ) - 1)) ^ p := by
    have := Nat.ceil_lt_add_one (le_trans zero_le_one hthreshold)
    linarith
  have hprimeR : (polynomialPrime A p n : ℝ) ≤
      2 * (⌈(A * ((n : ℝ) - 1)) ^ p⌉₊ : ℝ) := by
    dsimp [polynomialPrime]
    exact_mod_cast hprime
  constructor
  · refine le_trans (Real.rpow_le_rpow (by positivity) ?_ hp.le)
      (polynomialPrime_threshold A p n)
    nlinarith
  · have hb : (A * ((n : ℝ) - 1)) ^ p ≤ (A * (n : ℝ)) ^ p := by
      apply Real.rpow_le_rpow (by positivity) _ hp.le
      nlinarith
    conv_rhs at hb => rw [Real.mul_rpow (by linarith : 0 ≤ A) (by positivity)]
    nlinarith

theorem polynomialAlphabet_bounds {A p : ℝ} (hA : 2 ≤ A) (hp : 0 < p)
    {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ (2 * p) ≤ polynomialAlphabet A p n ∧
      (polynomialAlphabet A p n : ℝ) ≤ (4 * A ^ p) ^ 2 * (n : ℝ) ^ (2 * p) := by
  obtain ⟨hl, hu⟩ := polynomialPrime_bounds hA hp hn
  have hs : ((n : ℝ) ^ p) ^ 2 = (n : ℝ) ^ (2 * p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have hc : (0 : ℝ) ≤ 4 * A ^ p := by positivity
  have hd : (polynomialAlphabet A p n : ℝ) = (polynomialPrime A p n : ℝ) ^ 2 := by
    simp [polynomialAlphabet]
  rw [hd, ← hs]
  constructor <;> nlinarith [Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) p]

theorem polynomialPrime_isTheta {A p : ℝ} (hA : 2 ≤ A) (hp : 0 < p) :
    (fun n : ℕ => (polynomialPrime A p n : ℝ)) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ p) := by
  constructor
  · apply IsBigO.of_bound (4 * A ^ p)
    filter_upwards [eventually_ge_atTop 2] with n hn
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact (polynomialPrime_bounds hA hp hn).2
  · apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop 2] with n hn
    simp only [Real.norm_eq_abs, one_mul]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact (polynomialPrime_bounds hA hp hn).1

theorem polynomialAlphabet_isTheta {A p : ℝ} (hA : 2 ≤ A) (hp : 0 < p) :
    (fun n : ℕ => (polynomialAlphabet A p n : ℝ)) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (2 * p)) := by
  constructor
  · apply IsBigO.of_bound ((4 * A ^ p) ^ 2)
    filter_upwards [eventually_ge_atTop 2] with n hn
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact (polynomialAlphabet_bounds hA hp hn).2
  · apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop 2] with n hn
    simp only [Real.norm_eq_abs, one_mul]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact (polynomialAlphabet_bounds hA hp hn).1

theorem polynomialAlphabet_tendsto {A p : ℝ} (hA : 2 ≤ A) (hp : 0 < p) :
    Tendsto (polynomialAlphabet A p) atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply tendsto_atTop_mono' _ ?_ ((tendsto_rpow_atTop (by positivity : 0 < 2 * p)).comp
    tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (polynomialAlphabet_bounds hA hp hn).1

/-- The sample size prescribed in (17). -/
noncomputable def asymptoticSampleSize (n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊

theorem asymptoticSampleSize_equiv :
    (fun n : ℕ => (asymptoticSampleSize n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)) := by
  exact Asymptotics.isEquivalent_nat_floor.comp_tendsto
    ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 4 : ℝ))).comp
      tendsto_natCast_atTop_atTop)

theorem asymptoticSampleSize_tendsto : Tendsto asymptoticSampleSize atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  exact asymptoticSampleSize_equiv.symm.tendsto_atTop
    ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 4 : ℝ))).comp
      tendsto_natCast_atTop_atTop)

theorem asymptoticSampleSize_sq_le {n : ℕ} (hn : 1 ≤ n) :
    asymptoticSampleSize n * asymptoticSampleSize n ≤ n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hk : (asymptoticSampleSize n : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
    Nat.floor_le (by positivity)
  have hs : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num [Real.sqrt_eq_rpow]
  have hsn : Real.sqrt (n : ℝ) ≤ n := (Real.sqrt_le_iff).mpr ⟨hn0.le, by nlinarith⟩
  have hk0 : (0 : ℝ) ≤ asymptoticSampleSize n := by positivity
  have hroot0 : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have hsq : (asymptoticSampleSize n : ℝ) * asymptoticSampleSize n ≤ n := by nlinarith
  exact_mod_cast hsq

theorem asymptoticSampleSize_sub_one_equiv :
    (fun n : ℕ => (asymptoticSampleSize n : ℝ) - 1) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)) := by
  have hnorm : Tendsto (fun n : ℕ => ‖(n : ℝ) ^ (1 / 4 : ℝ)‖) atTop atTop := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      using (tendsto_rpow_atTop (by norm_num : 0 < (1 / 4 : ℝ))).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [sub_eq_add_neg] using
    asymptoticSampleSize_equiv.add_const_of_norm_tendsto_atTop (c := (-1 : ℝ)) hnorm

theorem asymptoticSampleSize_littleO :
    (fun n : ℕ => (asymptoticSampleSize n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  apply asymptoticSampleSize_equiv.isBigO.trans_isLittleO
  apply (isLittleO_iff_tendsto' _).mpr
  · have hlim := (tendsto_rpow_neg_atTop (by norm_num : 0 < (3 / 4 : ℝ))).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    dsimp
    calc
      (n : ℝ) ^ (-(3 / 4 : ℝ)) = (n : ℝ) ^ ((1 / 4 : ℝ) - 1) := by norm_num
      _ = (n : ℝ) ^ (1 / 4 : ℝ) / n := by rw [Real.rpow_sub hnR, Real.rpow_one]
  · filter_upwards with n hn
    simp [hn]

theorem asymptoticDenominator_equiv :
    (fun n : ℕ => (n : ℝ) - asymptoticSampleSize n + 1) ~[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  have hnorm : Tendsto (fun n : ℕ => ‖(n : ℝ)‖) atTop atTop := by
    simpa using (tendsto_natCast_atTop_atTop (R := ℝ))
  exact (Asymptotics.IsEquivalent.refl.sub_isLittleO
    asymptoticSampleSize_littleO).add_const_of_norm_tendsto_atTop hnorm

/-- The exact scale in (17), including the floor and the finite-population denominator. -/
noncomputable def asymptoticScale (d : ℕ → ℕ) (n : ℕ) : ℝ :=
  (asymptoticSampleSize n : ℝ) * ((asymptoticSampleSize n : ℝ) - 1) *
    Real.log (d n) / ((n : ℝ) - asymptoticSampleSize n + 1)

/-- The purely sampling part of (17) is asymptotic to `1/√n`. -/
theorem asymptoticSamplingFactor_equiv :
    (fun n : ℕ => (asymptoticSampleSize n : ℝ) *
      ((asymptoticSampleSize n : ℝ) - 1) /
        ((n : ℝ) - asymptoticSampleSize n + 1)) ~[atTop]
      (fun n : ℕ => 1 / Real.sqrt n) := by
  have he := (asymptoticSampleSize_equiv.mul
    asymptoticSampleSize_sub_one_equiv).div asymptoticDenominator_equiv
  apply he.congr_right
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  dsimp
  rw [← Real.rpow_add hnR, show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow]
  have hs := Real.sq_sqrt hnR.le
  have hs0 : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnR)
  field_simp
  nlinarith

/-- Polynomial alphabet growth supplies the logarithmic factor in (17). -/
theorem polynomialAlphabet_log_isTheta {A p : ℝ} (hA : 2 ≤ A) (hp : 0 < p) :
    (fun n : ℕ => Real.log (polynomialAlphabet A p n)) =Θ[atTop]
      (fun n : ℕ => Real.log n) := by
  let C := (4 * A ^ p) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hlogN : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb : ∀ᶠ n : ℕ in atTop,
      0 ≤ Real.log n ∧ 0 ≤ Real.log (polynomialAlphabet A p n) ∧
      (2 * p) * Real.log n ≤ Real.log (polynomialAlphabet A p n) ∧
      Real.log (polynomialAlphabet A p n) ≤ (2 * p + 1) * Real.log n := by
    filter_upwards [eventually_ge_atTop 2, hlogN.eventually_ge_atTop (Real.log C)] with n hn hlog
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hdn : (0 : ℝ) < polynomialAlphabet A p n := by
      exact_mod_cast (pow_pos (polynomialPrime_prime A p n).pos 2)
    obtain ⟨hl, hu⟩ := polynomialAlphabet_bounds hA hp hn
    have hlow := Real.log_le_log (Real.rpow_pos_of_pos hnR (2 * p)) hl
    rw [Real.log_rpow hnR] at hlow
    have hupp := Real.log_le_log hdn hu
    rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hnR _).ne', Real.log_rpow hnR] at hupp
    have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    refine ⟨hln, le_trans (by positivity) hlow, hlow, ?_⟩
    linarith
  constructor
  · apply IsBigO.of_bound (2 * p + 1)
    filter_upwards [hb] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn.1, abs_of_nonneg hn.2.1] using hn.2.2.2
  · apply IsBigO.of_bound (1 / (2 * p))
    filter_upwards [hb] with n hn
    simp only [Real.norm_eq_abs, abs_of_nonneg hn.1, abs_of_nonneg hn.2.1]
    calc
      Real.log n ≤ Real.log (polynomialAlphabet A p n) / (2 * p) :=
        (le_div_iff₀ (by positivity : 0 < 2 * p)).mpr (by nlinarith [hn.2.2.1])
      _ = (1 / (2 * p)) * Real.log (polynomialAlphabet A p n) := by ring

/-- The full asymptotic assertion in (17). -/
theorem asymptoticScale_isTheta {A p : ℝ} (hA : 2 ≤ A) (hp : 0 < p) :
    asymptoticScale (polynomialAlphabet A p) =Θ[atTop]
      (fun n : ℕ => Real.log n / Real.sqrt n) := by
  have h := asymptoticSamplingFactor_equiv.isTheta.mul (polynomialAlphabet_log_isTheta hA hp)
  convert h using 1 <;> ext n <;> simp [asymptoticScale] <;> ring

theorem log_div_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log n / Real.sqrt n) atTop (𝓝 0) := by
  simpa only [Real.sqrt_eq_rpow] using
    (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- In particular the matching scale tends to zero, as asserted in (17). -/
theorem asymptoticScale_tendsto_zero {A p : ℝ} (hA : 2 ≤ A) (hp : 0 < p) :
    Tendsto (asymptoticScale (polynomialAlphabet A p)) atTop (𝓝 0) := by
  exact (asymptoticScale_isTheta hA hp).isBigO.trans_tendsto log_div_sqrt_tendsto_zero

/-- The polynomial exponent arithmetic in (16). -/
theorem theta_polynomial_exponents {θ : ℝ} (_hθ : 0 < θ) (hθhalf : θ < 1 / 2) :
    0 < 1 / (1 / 2 - θ) ∧
      1 / (1 / 2 - θ) = 2 / (1 - 2 * θ) ∧
      2 * (1 / (1 / 2 - θ)) = 4 / (1 - 2 * θ) := by
  have hden : 0 < 1 / 2 - θ := by linarith
  refine ⟨by positivity, ?_, ?_⟩ <;> field_simp <;> ring

/-- The `4 + δ` alphabet exponent and lower-bound coefficient in (19). -/
theorem delta_polynomial_exponents {δ : ℝ} (hδ : 0 < δ) :
    0 < δ / (2 * (4 + δ)) ∧ δ / (2 * (4 + δ)) < 1 / 2 ∧
      4 / (1 - 2 * (δ / (2 * (4 + δ)))) = 4 + δ ∧
      3 * (δ / (2 * (4 + δ))) / 32 = 3 * δ / (64 * (4 + δ)) := by
  have hd : 0 < 4 + δ := by linarith
  refine ⟨by positivity, (div_lt_iff₀ (by positivity)).mpr (by linarith), ?_, ?_⟩
  · field_simp
    <;> ring
  · field_simp
    <;> ring

/-- The elementary exponent range used in Corollary 3.6.  The game-value
estimate of Bavarian--Shor is a separate, unformalized dependency. -/
theorem improved_polynomial_exponent {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    2 < 4 / (1 + ε) ∧ 4 / (1 + ε) < 4 ∧ 0 < 3 * ε / 128 := by
  have hden : 0 < 1 + ε := by linarith
  constructor
  · exact (lt_div_iff₀ hden).mpr (by nlinarith)
  constructor
  · exact (div_lt_iff₀ hden).mpr (by nlinarith)
  · positivity

/-- The least-prime sequence chosen in the paper immediately before (16). -/
noncomputable def paperPrime (θ : ℝ) : ℕ → ℕ :=
  polynomialPrime (2 * Real.exp 1) (1 / (1 / 2 - θ))

noncomputable def paperAlphabet (θ : ℝ) : ℕ → ℕ :=
  polynomialAlphabet (2 * Real.exp 1) (1 / (1 / 2 - θ))

private theorem paperPrime_base_bound : 2 ≤ 2 * Real.exp 1 := by
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

/-- Equation (16), with the paper's exact least-prime construction. -/
theorem equation16 {θ : ℝ} (hθ : 0 < θ) (hθhalf : θ < 1 / 2) :
    (fun n : ℕ => (paperPrime θ n : ℝ)) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ (2 / (1 - 2 * θ))) ∧
      (fun n : ℕ => (paperAlphabet θ n : ℝ)) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ (4 / (1 - 2 * θ))) := by
  obtain ⟨hp, heq, heq2⟩ := theta_polynomial_exponents hθ hθhalf
  constructor
  · simpa only [paperPrime, heq] using polynomialPrime_isTheta paperPrime_base_bound hp
  · simpa only [paperAlphabet, heq2] using polynomialAlphabet_isTheta paperPrime_base_bound hp

theorem paperPrime_parameter {θ : ℝ} (hθhalf : θ < 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) :
    2 * Real.exp 1 * ((n : ℝ) - 1) ≤ (paperPrime θ n : ℝ) ^ (1 / 2 - θ) := by
  have hden : 0 < 1 / 2 - θ := sub_pos.mpr hθhalf
  have hp : 0 < 1 / (1 / 2 - θ) := by positivity
  simpa only [paperPrime, one_div_one_div] using
    polynomialPrime_parameter (by positivity : 0 ≤ 2 * Real.exp 1) hp hn

/-- Equation (17), including both its Θ assertion and its zero limit. -/
theorem equation17 {θ : ℝ} (hθhalf : θ < 1 / 2) :
    asymptoticScale (paperAlphabet θ) =Θ[atTop]
        (fun n : ℕ => Real.log n / Real.sqrt n) ∧
      Tendsto (asymptoticScale (paperAlphabet θ)) atTop (𝓝 0) := by
  have hden : 0 < 1 / 2 - θ := sub_pos.mpr hθhalf
  have hp : 0 < 1 / (1 / 2 - θ) := by positivity
  exact ⟨asymptoticScale_isTheta paperPrime_base_bound hp,
    asymptoticScale_tendsto_zero paperPrime_base_bound hp⟩

theorem paperAlphabet_tendsto {θ : ℝ} (hθhalf : θ < 1 / 2) :
    Tendsto (paperAlphabet θ) atTop atTop := by
  have hden : 0 < 1 / 2 - θ := sub_pos.mpr hθhalf
  exact polynomialAlphabet_tendsto paperPrime_base_bound (by positivity)

/-- The alphabet-growth assertion of (19). -/
theorem equation19_alphabet {δ : ℝ} (hδ : 0 < δ) :
    (fun n : ℕ => (paperAlphabet (δ / (2 * (4 + δ))) n : ℝ)) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (4 + δ)) := by
  obtain ⟨hθ, hθhalf, hexp, _⟩ := delta_polynomial_exponents hδ
  simpa only [hexp] using (equation16 hθ hθhalf).2

/-- The contradiction in Corollary 3.5 after the positive sampling factor has
been cancelled.  This lemma retains the full little-o and diverging-alphabet quantifiers. -/
theorem no_sublogarithmic_sequence_bound (d : ℕ → ℕ)
    (hd : Tendsto d atTop atTop) (h : ℕ → ℝ)
    (hh : h =o[atTop] (fun d : ℕ => Real.log d))
    {a C : ℝ} (ha : 0 < a) (_hC : 0 < C) :
    ¬ (∀ᶠ n in atTop, a ≤ C * h (d n) / Real.log (d n)) := by
  intro hbound
  have hlim : Tendsto (fun n => C * h (d n) / Real.log (d n)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using
      tendsto_const_nhds.mul (hh.tendsto_div_nhds_zero.comp hd)
  have hzero : a ≤ 0 := ge_of_tendsto hlim hbound
  linarith

/-- A lower-bound family with a positive sampling factor excludes the proposed
uniform sublogarithmic bound.  Both bounds have their original factor, which is
cancelled in the proof.  Admissibility and the construction of the lower-bound
family are handled by the matching-law theorems, rather than assumed here as conclusions. -/
theorem no_sublogarithmic_error_bound (d : ℕ → ℕ)
    (hd : Tendsto d atTop atTop) (h : ℕ → ℝ)
    (hh : h =o[atTop] (fun d : ℕ => Real.log d))
    (E s : ℕ → ℝ) {a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (hs : ∀ᶠ n in atTop, 0 < s n)
    (hlow : ∀ᶠ n in atTop, a * s n * Real.log (d n) ≤ E n) :
    ¬ (∀ᶠ n in atTop, E n ≤ C * s n * h (d n)) := by
  intro hupp
  apply no_sublogarithmic_sequence_bound d hd h hh ha hC
  filter_upwards [hs, hlow, hupp, hd.eventually_ge_atTop 2] with n hs hl hu hd2
  have hdR : (1 : ℝ) < d n := by exact_mod_cast hd2
  have hlog : 0 < Real.log (d n) := Real.log_pos hdR
  have hcan : s n * (a * Real.log (d n)) ≤ s n * (C * h (d n)) := by
    nlinarith [hl.trans hu]
  have hcan' : a * Real.log (d n) ≤ C * h (d n) :=
    (mul_le_mul_left hs).mp hcan
  exact (le_div_iff₀ hlog).mpr hcan'

end Paper06
