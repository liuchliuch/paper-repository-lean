import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Sign
import Mathlib.Tactic

/-!
Algebraic and analytic ingredients of Section 5 and Appendix A.

The lemmas in this file are components of the lower-bound proof.  In particular,
the scalar energy-split lemmas do not assert Theorems 5.1 or 5.2: their use in
those theorems additionally requires the auxiliary trajectory law and its
moment estimates.
-/

namespace CalibrationDistance

open scoped BigOperators

/-- The mean-reversion drift in (5.3), with the source convention `sgn 0 = 0`. -/
noncomputable def lowerDrift (a : ℕ) (μ : ℝ) : ℝ :=
  Real.sign (μ - 1 / 2) * |μ - 1 / 2| ^ a

/-- The Bernoulli parameter in the auxiliary adversary (5.3). -/
noncomputable def lowerQ (a : ℕ) (μ : ℝ) : ℝ := μ - lowerDrift a μ

theorem abs_lowerDrift (a : ℕ) (ha : 1 ≤ a) (μ : ℝ) :
    |lowerDrift a μ| = |μ - 1 / 2| ^ a := by
  rcases lt_trichotomy (μ - 1 / 2) 0 with h | h | h
  · unfold lowerDrift
    rw [Real.sign_of_neg h, neg_one_mul, abs_neg,
      abs_of_nonneg (pow_nonneg (abs_nonneg (μ - 1 / 2)) a)]
  · unfold lowerDrift
    rw [h]
    simp [zero_pow (by omega : a ≠ 0)]
  · unfold lowerDrift
    rw [Real.sign_of_pos h, one_mul,
      abs_of_nonneg (pow_nonneg (abs_nonneg (μ - 1 / 2)) a)]

theorem lowerDrift_energy (a : ℕ) (μ : ℝ) :
    (μ - 1 / 2) * lowerDrift a μ = |μ - 1 / 2| ^ (a + 1) := by
  rcases lt_trichotomy (μ - 1 / 2) 0 with h | h | h
  · simp only [lowerDrift, Real.sign_of_neg h, abs_of_neg h, pow_succ]
    ring
  · unfold lowerDrift
    rw [h]
    simp
  · simp only [lowerDrift, Real.sign_of_pos h, abs_of_pos h, one_mul, pow_succ]
    ring

theorem lowerDrift_eq_mul_pow {a : ℕ} (ha : 1 ≤ a) (μ : ℝ) :
    lowerDrift a μ = (μ - 1 / 2) * |μ - 1 / 2| ^ (a - 1) := by
  have ha' : a = (a - 1) + 1 := by omega
  have hp : |μ - 1 / 2| ^ a = |μ - 1 / 2| ^ (a - 1) * |μ - 1 / 2| := by
    conv_lhs => rw [ha', pow_succ]
  rcases lt_trichotomy (μ - 1 / 2) 0 with h | h | h
  · rw [lowerDrift, Real.sign_of_neg h, hp]
    rw [abs_of_neg h]
    ring
  · unfold lowerDrift
    rw [h]
    simp
  · rw [lowerDrift, Real.sign_of_pos h, hp]
    rw [abs_of_pos h]
    ring

/-- Although `sgn` itself jumps at zero, the drift used by the paper is
continuous, and hence is a Borel function of the conditional mean. -/
theorem continuous_lowerDrift {a : ℕ} (ha : 1 ≤ a) : Continuous (lowerDrift a) := by
  have hid : lowerDrift a = fun μ : ℝ => (μ - 1 / 2) * |μ - 1 / 2| ^ (a - 1) := by
    funext μ
    exact lowerDrift_eq_mul_pow ha μ
  rw [hid]
  fun_prop

theorem continuous_lowerQ {a : ℕ} (ha : 1 ≤ a) : Continuous (lowerQ a) :=
  continuous_id.sub (continuous_lowerDrift ha)

/-- The auxiliary coin always lies between the conditional mean and `1/2`.
This is the feasibility assertion immediately following (5.3). -/
theorem lowerQ_between {a : ℕ} (ha : 1 ≤ a) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    min μ (1 / 2) ≤ lowerQ a μ ∧ lowerQ a μ ≤ max μ (1 / 2) := by
  have he : |μ - 1 / 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hμ.1, hμ.2]
  have hp : |μ - 1 / 2| ^ a ≤ |μ - 1 / 2| := by
    simpa using pow_le_pow_of_le_one (abs_nonneg (μ - 1 / 2)) he ha
  have hn : 0 ≤ |μ - 1 / 2| ^ a := pow_nonneg (abs_nonneg _) _
  rcases lt_trichotomy (μ - 1 / 2) 0 with h | h | h
  · have hμh : μ ≤ 1 / 2 := by linarith
    simp only [lowerQ, lowerDrift, Real.sign_of_neg h, neg_one_mul,
      min_eq_left hμh, max_eq_right hμh, sub_neg_eq_add]
    have habs := abs_of_neg h
    constructor <;> linarith
  · have hμh : μ = 1 / 2 := by linarith
    simp [hμh, lowerQ, lowerDrift]
  · have hhμ : 1 / 2 ≤ μ := by linarith
    simp only [lowerQ, lowerDrift, Real.sign_of_pos h, one_mul,
      min_eq_right hhμ, max_eq_left hhμ]
    have habs := abs_of_pos h
    constructor <;> linarith

theorem lowerQ_mem_Icc {a : ℕ} (ha : 1 ≤ a) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) : lowerQ a μ ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hl, hu⟩ := lowerQ_between ha hμ
  constructor
  · exact (le_min hμ.1 (by norm_num)).trans hl
  · exact hu.trans (max_le hμ.2 (by norm_num))

/-- The good-round conditional Bernoulli variance bound used in (A.2). -/
theorem lowerQ_variance {a : ℕ} (ha : 1 ≤ a) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hgood : |μ - 1 / 2| ≤ 1 / 4) :
    (3 : ℝ) / 16 ≤ lowerQ a μ * (1 - lowerQ a μ) := by
  obtain ⟨hl, hu⟩ := lowerQ_between ha hμ
  have hm : 1 / 4 ≤ μ ∧ μ ≤ 3 / 4 := by
    rw [abs_le] at hgood
    constructor <;> linarith [hgood.1, hgood.2]
  have hq0 : 1 / 4 ≤ lowerQ a μ :=
    (le_min hm.1 (by norm_num)).trans hl
  have hq1 : lowerQ a μ ≤ 3 / 4 :=
    hu.trans (max_le hm.2 (by norm_num))
  nlinarith [mul_nonneg (sub_nonneg.mpr hq0) (sub_nonneg.mpr hq1)]

/-- The polynomial identity behind the conditional energy identity (5.6).
The last two terms have zero conditional expectation when `μ` is the mean. -/
theorem lower_energy_expansion (a : ℕ) (μ p : ℝ) :
    (1 / 2 - p) * (lowerQ a μ - p) =
      |μ - 1 / 2| ^ (a + 1) + (p - μ) ^ 2 +
      (2 * μ - 1 / 2 - lowerQ a μ) * (p - μ) := by
  have h := lowerDrift_energy a μ
  unfold lowerQ
  nlinarith

/-- Integrating the Bernoulli outcome of the auxiliary transition first. -/
theorem lower_bernoulli_energy (q p : ℝ) :
    (1 - q) * ((1 / 2 - p) * (0 - p)) +
      q * ((1 / 2 - p) * (1 - p)) = (1 / 2 - p) * (q - p) := by
  ring

theorem lower_bernoulli_centered_first (q μ p : ℝ) :
    (1 - q) * ((0 - q) - (p - μ)) +
      q * ((1 - q) - (p - μ)) = -(p - μ) := by
  ring

theorem lower_bernoulli_centered_second (q μ p : ℝ) :
    (1 - q) * (((0 - q) - (p - μ)) ^ 2) +
      q * (((1 - q) - (p - μ)) ^ 2) = q * (1 - q) + (p - μ) ^ 2 := by
  ring

/-- The pointwise residual decomposition (5.16). -/
theorem lower_residual_decomposition {ι : Type*} [Fintype ι]
    (a : ℕ) (μ p y : ι → ℝ) :
    (∑ t, (y t - p t)) =
      (∑ t, ((y t - lowerQ a (μ t)) - (p t - μ t))) -
        ∑ t, lowerDrift a (μ t) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [lowerQ]
  ring

/-- The bad-round counting inequality in Appendix A.1 is pathwise. -/
theorem lower_bad_count {ι : Type*} [Fintype ι] (a : ℕ) (ε v : ι → ℝ)
    (hv : ∀ t, 0 ≤ v t) :
    (∑ t, if (1 / 4 : ℝ) < |ε t| then (1 : ℝ) else 0) ≤
      (4 : ℝ) ^ (a + 1) * ∑ t, (|ε t| ^ (a + 1) + v t) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  by_cases hb : (1 / 4 : ℝ) < |ε t|
  · rw [if_pos hb]
    have h1 : (1 : ℝ) ≤ 4 * |ε t| := by linarith
    have hp : (1 : ℝ) ≤ (4 * |ε t|) ^ (a + 1) := one_le_pow₀ h1
    rw [mul_pow] at hp
    have hpos : (0 : ℝ) ≤ 4 ^ (a + 1) := by positivity
    nlinarith [mul_nonneg hpos (hv t)]
  · rw [if_neg hb]
    exact mul_nonneg (by positivity) (add_nonneg (pow_nonneg (abs_nonneg _) _) (hv t))

/-- Summing the good-round variance bound, before taking expectations. -/
theorem lower_variance_sum {ι : Type*} [Fintype ι] {a : ℕ} (ha : 1 ≤ a)
    (μ v : ι → ℝ) (hμ : ∀ t, μ t ∈ Set.Icc (0 : ℝ) 1) (hv : ∀ t, 0 ≤ v t) :
    (3 / 16 : ℝ) * ((Fintype.card ι : ℝ) -
      ∑ t, if (1 / 4 : ℝ) < |μ t - 1 / 2| then (1 : ℝ) else 0) ≤
        ∑ t, (lowerQ a (μ t) * (1 - lowerQ a (μ t)) + v t) := by
  have hid : (3 / 16 : ℝ) * ((Fintype.card ι : ℝ) -
      ∑ t, if (1 / 4 : ℝ) < |μ t - 1 / 2| then (1 : ℝ) else 0) =
        ∑ t, (3 / 16 : ℝ) * (1 -
          if (1 / 4 : ℝ) < |μ t - 1 / 2| then (1 : ℝ) else 0) := by
    simp only [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub, mul_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hid]
  apply Finset.sum_le_sum
  intro t _
  by_cases hb : (1 / 4 : ℝ) < |μ t - 1 / 2|
  · rw [if_pos hb]
    obtain ⟨hq0, hq1⟩ := lowerQ_mem_Icc ha (hμ t)
    have hq : 0 ≤ lowerQ a (μ t) * (1 - lowerQ a (μ t)) :=
      mul_nonneg hq0 (by linarith)
    linarith [hv t]
  · rw [if_neg hb]
    have hq := lowerQ_variance ha (hμ t) (le_of_not_gt hb)
    linarith [hv t]

/-- An exact algebraic part of (A.2), before martingale orthogonality is used. -/
theorem randomized_variance_constant {T N V : ℝ} (hN : N ≤ T / 45)
    (hV : (3 / 16 : ℝ) * (T - N) ≤ V) : (11 / 60 : ℝ) * T ≤ V := by
  linarith

theorem deterministic_variance_constant {T N V : ℝ} (hN : N ≤ 2 * T / 25)
    (hV : (3 / 16 : ℝ) * (T - N) ≤ V) : (69 / 400 : ℝ) * T ≤ V := by
  linarith

/-- The full scalar multiplication estimate behind (A.1) and (A.6). -/
theorem lower_bad_expectation {T R c E N F : ℝ} (hT : 0 < T)
    (hc : 0 < c) (hR : R ≤ Real.sqrt T) (hE0 : 0 ≤ E) (hE : E < c * R)
    (hF : F ≤ 16 * Real.sqrt T) (hN : N ≤ F * E) : N < 16 * c * T := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsq := Real.sq_sqrt (le_of_lt hT)
  calc
    N ≤ F * E := hN
    _ ≤ 16 * Real.sqrt T * E := mul_le_mul_of_nonneg_right hF hE0
    _ < 16 * Real.sqrt T * (c * R) :=
      mul_lt_mul_of_pos_left hE (by positivity)
    _ ≤ 16 * Real.sqrt T * (c * Real.sqrt T) := by
      gcongr
    _ = 16 * c * T := by nlinarith

/-- Appendix A.2's exact rational square-root comparison. -/
theorem randomized_constant_exact :
    (1 / 4320 : ℝ) < (11 * Real.sqrt 165 - 60 * Real.sqrt 5) / 3600 := by
  have h165 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 165)
  have h5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h165n := Real.sqrt_nonneg (165 : ℝ)
  have h5n := Real.sqrt_nonneg (5 : ℝ)
  have h165l : (64 / 5 : ℝ) < Real.sqrt 165 := by nlinarith
  have h5u : Real.sqrt 5 < (9 / 4 : ℝ) := by nlinarith
  linarith

/-- Appendix A.3's exact rational square-root comparison. -/
theorem deterministic_constant_exact :
    (1 / 1200 : ℝ) < (207 * Real.sqrt 69 - 1200 * Real.sqrt 2) / 24000 := by
  have h69 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 69)
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h69n := Real.sqrt_nonneg (69 : ℝ)
  have h2n := Real.sqrt_nonneg (2 : ℝ)
  have h69l : (83 / 10 : ℝ) < Real.sqrt 69 := by nlinarith
  have h2u : Real.sqrt 2 < (99 / 70 : ℝ) := by nlinarith
  linarith

/-- The randomized constant in the moment form actually used in (5.17). -/
theorem randomized_moment_constant :
    (1 / 4320 : ℝ) <
      (1 / 2 : ℝ) * (11 / 60) * Real.sqrt (11 / 60) - 1 / Real.sqrt 720 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11 / 60)
  have ht := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 720)
  have hsn := Real.sqrt_nonneg (11 / 60 : ℝ)
  have htn := Real.sqrt_nonneg (720 : ℝ)
  have hsl : (21 / 50 : ℝ) < Real.sqrt (11 / 60) := by nlinarith
  have htl : (53 / 2 : ℝ) < Real.sqrt 720 := by nlinarith
  have htp : 0 < Real.sqrt 720 := by positivity
  have hi : (1 : ℝ) / Real.sqrt 720 < 2 / 53 := by
    apply (div_lt_iff₀ htp).mpr
    linarith
  linarith

/-- The deterministic constant in the moment form actually used in (5.21). -/
theorem deterministic_moment_constant :
    (1 / 1200 : ℝ) <
      (69 / 400 : ℝ) * Real.sqrt (69 / 400) - 1 / Real.sqrt 200 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 69 / 400)
  have ht := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 200)
  have hsn := Real.sqrt_nonneg (69 / 400 : ℝ)
  have htn := Real.sqrt_nonneg (200 : ℝ)
  have hsl : (83 / 200 : ℝ) < Real.sqrt (69 / 400) := by nlinarith
  have htl : (1400 / 99 : ℝ) < Real.sqrt 200 := by nlinarith
  have htp : 0 < Real.sqrt 200 := by positivity
  have hi : (1 : ℝ) / Real.sqrt 200 < 99 / 1400 := by
    apply (div_lt_iff₀ htp).mpr
    linarith
  linarith

theorem randomized_rpow_constant :
    (1 / 4320 : ℝ) <
      (1 / 2 : ℝ) * (11 / 60 : ℝ) ^ (3 / 2 : ℝ) - 1 / Real.sqrt 720 := by
  have hid : (11 / 60 : ℝ) ^ (3 / 2 : ℝ) =
      (11 / 60 : ℝ) * Real.sqrt (11 / 60) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 11 / 60), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [hid]
  simpa only [mul_assoc] using randomized_moment_constant

theorem deterministic_rpow_constant :
    (1 / 1200 : ℝ) <
      (69 / 400 : ℝ) ^ (3 / 2 : ℝ) - 1 / Real.sqrt 200 := by
  have hid : (69 / 400 : ℝ) ^ (3 / 2 : ℝ) =
      (69 / 400 : ℝ) * Real.sqrt (69 / 400) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 69 / 400), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [hid]
  exact deterministic_moment_constant

/-- Cancelling the horizon factors in moment interpolation. -/
theorem lower_moment_cubic_reduction {T c b M₁ M₂ M₄ : ℝ}
    (hT : 0 < T) (hc : 0 ≤ c) (hM₂ : c * T ≤ M₂)
    (hM₄ : M₄ ≤ b * T ^ 2) (hI : M₂ ^ 3 ≤ M₁ ^ 2 * M₄) :
    c ^ 3 * T ≤ b * M₁ ^ 2 := by
  have hcube : (c * T) ^ 3 ≤ M₂ ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg hc hT.le) hM₂ 3
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hT)).mp
  calc
    T ^ 2 * (c ^ 3 * T) = (c * T) ^ 3 := by ring
    _ ≤ M₂ ^ 3 := hcube
    _ ≤ M₁ ^ 2 * M₄ := hI
    _ ≤ M₁ ^ 2 * (b * T ^ 2) :=
      mul_le_mul_of_nonneg_left hM₄ (sq_nonneg M₁)
    _ = T ^ 2 * (b * M₁ ^ 2) := by ring

/-- The moment-interpolation implication (5.14), with no probabilistic
estimates concealed in the conclusion. -/
theorem randomized_abs_moment_lower {T M₁ M₂ M₄ : ℝ} (hT : 0 < T)
    (hM₁ : 0 ≤ M₁) (hM₂ : (11 / 60 : ℝ) * T ≤ M₂)
    (hM₄ : M₄ ≤ 4 * T ^ 2) (hI : M₂ ^ 3 ≤ M₁ ^ 2 * M₄) :
    (1 / 2 : ℝ) * (11 / 60) * Real.sqrt (11 / 60) * Real.sqrt T ≤ M₁ := by
  have hc := lower_moment_cubic_reduction hT (by norm_num : (0 : ℝ) ≤ 11 / 60)
    hM₂ hM₄ hI
  have hid : ((1 / 2 : ℝ) * (11 / 60) * Real.sqrt (11 / 60) * Real.sqrt T) ^ 2 =
      (11 / 60 : ℝ) ^ 3 * T / 4 := by
    simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11 / 60),
      Real.sq_sqrt (le_of_lt hT)]
    ring
  have hsq : ((1 / 2 : ℝ) * (11 / 60) * Real.sqrt (11 / 60) * Real.sqrt T) ^ 2 ≤
      M₁ ^ 2 := by rw [hid]; linarith
  exact (sq_le_sq₀ (by positivity) hM₁).mp hsq

/-- The deterministic companion of (5.14), namely (A.8). -/
theorem deterministic_abs_moment_lower {T M₁ M₂ M₄ : ℝ} (hT : 0 < T)
    (hM₁ : 0 ≤ M₁) (hM₂ : (69 / 400 : ℝ) * T ≤ M₂)
    (hM₄ : M₄ ≤ T ^ 2) (hI : M₂ ^ 3 ≤ M₁ ^ 2 * M₄) :
    (69 / 400 : ℝ) * Real.sqrt (69 / 400) * Real.sqrt T ≤ M₁ := by
  have hc := lower_moment_cubic_reduction hT (by norm_num : (0 : ℝ) ≤ 69 / 400)
    hM₂ (b := 1) (by simpa using hM₄) hI
  have hid : ((69 / 400 : ℝ) * Real.sqrt (69 / 400) * Real.sqrt T) ^ 2 =
      (69 / 400 : ℝ) ^ 3 * T := by
    simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 69 / 400),
      Real.sq_sqrt (le_of_lt hT)]
    ring
  have hsq : ((69 / 400 : ℝ) * Real.sqrt (69 / 400) * Real.sqrt T) ^ 2 ≤ M₁ ^ 2 := by
    rw [hid]
    simpa using hc
  exact (sq_le_sq₀ (by positivity) hM₁).mp hsq

/-- High-energy arithmetic (5.9), stated as a reusable scalar step. -/
theorem randomized_high_energy {T R E L : ℝ}
    (hR : Real.sqrt T / 4 ≤ R) (hE : R / 720 ≤ E)
    (hL : (2 / 3 : ℝ) * E ≤ L) : Real.sqrt T / 4320 ≤ L := by
  linarith

theorem deterministic_high_energy {T R E L : ℝ}
    (hR : Real.sqrt T / 4 ≤ R) (hE : R / 200 ≤ E)
    (hL : (2 / 3 : ℝ) * E ≤ L) : Real.sqrt T / 1200 ≤ L := by
  linarith

/-- Low-energy arithmetic (5.17), after the actual law's moment and drift
estimates have been established. -/
theorem randomized_low_energy {T Z D L : ℝ} (hT : 0 < T)
    (hZ : (1 / 2 : ℝ) * (11 / 60) * Real.sqrt (11 / 60) * Real.sqrt T ≤ Z)
    (hD : D ≤ Real.sqrt T / Real.sqrt 720) (hL : Z - D ≤ L) :
    Real.sqrt T / 4320 < L := by
  have hc := mul_lt_mul_of_pos_right randomized_moment_constant
    (Real.sqrt_pos.mpr hT)
  simp only [div_eq_mul_inv, one_mul] at hc hD ⊢
  nlinarith

theorem deterministic_low_energy {T Z D L : ℝ} (hT : 0 < T)
    (hZ : (69 / 400 : ℝ) * Real.sqrt (69 / 400) * Real.sqrt T ≤ Z)
    (hD : D ≤ Real.sqrt T / Real.sqrt 200) (hL : Z - D ≤ L) :
    Real.sqrt T / 1200 < L := by
  have hc := mul_lt_mul_of_pos_right deterministic_moment_constant
    (Real.sqrt_pos.mpr hT)
  simp only [div_eq_mul_inv, one_mul] at hc hD ⊢
  nlinarith

end CalibrationDistance
