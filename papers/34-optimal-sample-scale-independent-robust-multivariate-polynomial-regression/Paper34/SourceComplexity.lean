import Paper34.Parameters
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The source grid, sample counts, and fixed refinement budget

This file records uniform scalar bounds with explicit constants. All constants
are independent of the polynomial, noise, `d`, `eps`, and `delta`; their allowed
parameters are stated explicitly. No complexity bound is an external input.
-/

namespace Paper34.SourceComplexity

noncomputable section

/-- The maximum in source (2.2), before taking its least integral value. -/
def gridThreshold (A : ℝ) (n d : ℕ) (rho eps : ℝ) : ℝ :=
  max 1 (max (A * d / zeta rho) (6 * Real.pi * n * d / beta eps))

/-- Exactly the least positive grid size prescribed by (2.2). -/
def gridSize (A : ℝ) (n d : ℕ) (rho eps : ℝ) : ℕ :=
  Nat.ceil (gridThreshold A n d rho eps)

theorem grid_constraints (A : ℝ) (n d : ℕ) (rho eps : ℝ) :
    (1 : ℝ) ≤ gridSize A n d rho eps ∧
    A * d / zeta rho ≤ gridSize A n d rho eps ∧
    6 * Real.pi * n * d / beta eps ≤ gridSize A n d rho eps := by
  have hc := Nat.le_ceil (gridThreshold A n d rho eps)
  exact ⟨(le_max_left _ _).trans hc,
    ((le_max_left _ _).trans (le_max_right _ _)).trans hc,
    ((le_max_right _ _).trans (le_max_right _ _)).trans hc⟩

theorem gridSize_pos (A : ℝ) (n d : ℕ) (rho eps : ℝ) :
    0 < gridSize A n d rho eps := by
  have h := (grid_constraints A n d rho eps).1
  exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h)

theorem gridSize_least (A : ℝ) (n d : ℕ) (rho eps : ℝ) (m : ℕ)
    (h1 : (1 : ℝ) ≤ m) (hA : A * d / zeta rho ≤ m)
    (hB : 6 * Real.pi * n * d / beta eps ≤ m) :
    gridSize A n d rho eps ≤ m := by
  exact Nat.ceil_le.mpr (max_le h1 (max_le hA hB))

theorem degree_le_gridSize {A rho eps : ℝ} {n d : ℕ} (hA : 1 ≤ A)
    (hr0 : 0 ≤ rho) (hr : rho < 1 / 2) (he0 : 0 < eps) (he : eps ≤ 1 / 2) :
    d ≤ gridSize A n d rho eps := by
  have hp := parameter_ranges hr0 hr he0 he
  have hz : 0 < zeta rho := hp.2.2.1.2.1
  have hzA : zeta rho ≤ A := by linarith [hp.2.2.1.2.2]
  have hd : (d : ℝ) ≤ A * d / zeta rho := by
    apply (le_div_iff₀ hz).2
    nlinarith [mul_le_mul_of_nonneg_left hzA (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  exact_mod_cast hd.trans (grid_constraints A n d rho eps).2.1

theorem gamma_le_beta_div_six {A rho eps : ℝ} {n d : ℕ}
    (he0 : 0 < eps) :
    Real.pi * n * d / gridSize A n d rho eps ≤ beta eps / 6 := by
  have hb : 0 < beta eps := by unfold beta; positivity
  have hm : (0 : ℝ) < gridSize A n d rho eps := by
    exact_mod_cast gridSize_pos A n d rho eps
  apply (div_le_iff₀ hm).2
  have h := (div_le_iff₀ hb).mp (grid_constraints A n d rho eps).2.2
  nlinarith

/-- A dimension/contamination constant for the uniform upper bound on `m`. -/
def gridConstant (A : ℝ) (n : ℕ) (rho : ℝ) : ℝ :=
  2 + A / zeta rho + 72 * Real.pi * n

theorem gridConstant_ge_two {A rho eps : ℝ} {n : ℕ} (hA : 1 ≤ A)
    (hr0 : 0 ≤ rho) (hr : rho < 1 / 2) (he0 : 0 < eps) (he : eps ≤ 1 / 2) :
    2 ≤ gridConstant A n rho := by
  have hz : 0 < zeta rho := (parameter_ranges hr0 hr he0 he).2.2.1.2.1
  unfold gridConstant
  have hdiv : 0 ≤ A / zeta rho := by positivity
  have hn : 0 ≤ 72 * Real.pi * (n : ℝ) := by positivity
  linarith

theorem scale_ge_two {d : ℕ} {eps : ℝ} (hd : 1 ≤ d) (he0 : 0 < eps)
    (he : eps ≤ 1 / 2) : 2 ≤ (d : ℝ) / eps := by
  apply (le_div_iff₀ he0).2
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

/-- The uniform upper half of source (2.3). -/
theorem gridSize_upper {A rho eps : ℝ} {n d : ℕ} (hA : 1 ≤ A)
    (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1 / 2)
    (he0 : 0 < eps) (he : eps ≤ 1 / 2) :
    (gridSize A n d rho eps : ℝ) ≤ gridConstant A n rho * ((d : ℝ) / eps) := by
  have hz : 0 < zeta rho := (parameter_ranges hr0 hr he0 he).2.2.1.2.1
  have hAd : 0 ≤ A / zeta rho := by positivity
  have hn : 0 ≤ 72 * Real.pi * (n : ℝ) := by positivity
  have hx : 1 ≤ (d : ℝ) / eps := by linarith [scale_ge_two hd he0 he]
  have hdx : (d : ℝ) ≤ (d : ℝ) / eps := by
    apply (le_div_iff₀ he0).2
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have htA : A * d / zeta rho ≤ (A / zeta rho) * ((d : ℝ) / eps) := by
    convert mul_le_mul_of_nonneg_left hdx hAd using 1 <;> ring
  have htB : 6 * Real.pi * n * d / beta eps =
      (72 * Real.pi * n) * ((d : ℝ) / eps) := by
    unfold beta
    field_simp
    <;> ring
  have hmax : gridThreshold A n d rho eps ≤
      (1 + A / zeta rho + 72 * Real.pi * n) * ((d : ℝ) / eps) := by
    apply max_le
    · nlinarith [mul_nonneg hAd (le_trans zero_le_one hx),
        mul_nonneg hn (le_trans zero_le_one hx)]
    · apply max_le
      · nlinarith [mul_nonneg hn (le_trans zero_le_one hx)]
      · rw [htB]
        nlinarith [mul_nonneg hAd (le_trans zero_le_one hx)]
  have ht0 : 0 ≤ gridThreshold A n d rho eps :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hc := (Nat.ceil_lt_add_one ht0).le
  change (Nat.ceil (gridThreshold A n d rho eps) : ℝ) ≤ _
  unfold gridConstant
  nlinarith

/-- The uniform lower half of (2.3), with a strictly positive dimension constant
when `n ≥ 1`. -/
theorem gridSize_lower (A rho : ℝ) (n d : ℕ) {eps : ℝ} (he0 : 0 < eps) :
    (72 * Real.pi * n) * ((d : ℝ) / eps) ≤ gridSize A n d rho eps := by
  convert (grid_constraints A n d rho eps).2.2 using 1
  unfold beta
  field_simp
  <;> ring

/-- The exact constant in source (2.5) and Lemma 6.1. -/
def contaminationConstant (rho : ℝ) : ℝ := 16 / (1 - 2 * rho) ^ 2

/-- One formula covers both designs: `e=n` for Chebyshev, `e=2*n` for uniform. -/
def sampleCount (e : ℕ) (A : ℝ) (n d : ℕ) (rho eps delta : ℝ) : ℕ :=
  Nat.ceil (contaminationConstant rho * (gridSize A n d rho eps : ℝ) ^ e *
    Real.log (2 * (gridSize A n d rho eps : ℝ) ^ n / delta))

def chebyshevSamples (A : ℝ) (n d : ℕ) (rho eps delta : ℝ) : ℕ :=
  sampleCount n A n d rho eps delta

def uniformSamples (A : ℝ) (n d : ℕ) (rho eps delta : ℝ) : ℕ :=
  sampleCount (2 * n) A n d rho eps delta

theorem sampleCount_threshold (e : ℕ) (A : ℝ) (n d : ℕ) (rho eps delta : ℝ) :
    contaminationConstant rho * (gridSize A n d rho eps : ℝ) ^ e *
      Real.log (2 * (gridSize A n d rho eps : ℝ) ^ n / delta) ≤
      (sampleCount e A n d rho eps delta : ℝ) :=
  Nat.le_ceil _

/-- Positivity already holds in the wider source range `0 < delta ≤ 1`. -/
theorem sampleCount_pos (e : ℕ) (A : ℝ) (n d : ℕ) (rho eps delta : ℝ)
    (hr : rho < 1 / 2) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    0 < sampleCount e A n d rho eps delta := by
  have hm1 := (grid_constraints A n d rho eps).1
  have hm0 : (0 : ℝ) < gridSize A n d rho eps := by linarith
  have hpow : 1 ≤ (gridSize A n d rho eps : ℝ) ^ n := one_le_pow₀ hm1
  have harg : 1 < 2 * (gridSize A n d rho eps : ℝ) ^ n / delta := by
    apply (lt_div_iff₀ hdelta).2
    nlinarith
  have hCC : 0 < contaminationConstant rho := by
    unfold contaminationConstant
    have hh : 0 < 1 - 2 * rho := by linarith
    positivity
  have hraw : 0 < contaminationConstant rho * (gridSize A n d rho eps : ℝ) ^ e *
      Real.log (2 * (gridSize A n d rho eps : ℝ) ^ n / delta) :=
    mul_pos (mul_pos hCC (pow_pos hm0 e)) (Real.log_pos harg)
  exact_mod_cast hraw.trans_le (sampleCount_threshold e A n d rho eps delta)

def sampleLogConstant (C : ℝ) (n : ℕ) : ℝ :=
  (Real.log 2 + n * Real.log C) / Real.log 2 + n + 1

/-- The occupancy logarithm costs only a dimension-dependent multiple of
`log(d/delta)`, uniformly even when `delta ≤ eps` is very small. -/
theorem occupancy_log_upper {m n d : ℕ} {C eps delta : ℝ}
    (hm : 0 < m) (hd : 1 ≤ d) (hC : 1 ≤ C) (he0 : 0 < eps)
    (hde : delta ≤ eps) (he : eps ≤ 1 / 2) (hdelta : 0 < delta)
    (hms : (m : ℝ) ≤ C * ((d : ℝ) / eps)) :
    Real.log (2 * (m : ℝ) ^ n / delta) ≤
      sampleLogConstant C n * Real.log ((d : ℝ) / delta) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hR2 : 2 ≤ (d : ℝ) / delta := scale_ge_two hd hdelta (hde.trans he)
  have hR0 : 0 < (d : ℝ) / delta := by positivity
  have hxR : (d : ℝ) / eps ≤ (d : ℝ) / delta := by
    apply (div_le_div_iff₀ he0 hdelta).2
    exact mul_le_mul_of_nonneg_left hde hd0.le
  have hmR : (m : ℝ) ≤ C * ((d : ℝ) / delta) :=
    hms.trans (mul_le_mul_of_nonneg_left hxR hC0.le)
  have hlogm : Real.log m ≤ Real.log C + Real.log ((d : ℝ) / delta) := by
    simpa only [Real.log_mul hC0.ne' hR0.ne'] using Real.log_le_log hm0 hmR
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hdeltalog : -Real.log delta ≤ Real.log ((d : ℝ) / delta) := by
    rw [Real.log_div hd0.ne' hdelta.ne']
    linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hLR : Real.log 2 ≤ Real.log ((d : ℝ) / delta) :=
    Real.log_le_log (by norm_num) hR2
  have hB : 0 ≤ Real.log 2 + (n : ℝ) * Real.log C := by
    exact add_nonneg hlog2.le (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hC))
  have hBbound : Real.log 2 + (n : ℝ) * Real.log C ≤
      ((Real.log 2 + (n : ℝ) * Real.log C) / Real.log 2) *
        Real.log ((d : ℝ) / delta) := by
    have hmul := mul_le_mul_of_nonneg_left hLR (div_nonneg hB hlog2.le)
    simpa only [div_mul_cancel₀ _ hlog2.ne'] using hmul
  rw [Real.log_div (by positivity : 2 * (m : ℝ) ^ n ≠ 0) hdelta.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero n hm0.ne'), Real.log_pow]
  have hnlog := mul_le_mul_of_nonneg_left hlogm (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  unfold sampleLogConstant
  nlinarith

def sampleConstant (e n : ℕ) (A rho : ℝ) : ℝ :=
  contaminationConstant rho * gridConstant A n rho ^ e *
    sampleLogConstant (gridConstant A n rho) n + 1 / Real.log 2

/-- A concrete pointwise constant, independent of `d`, `eps`, and `delta`. -/
theorem sampleCount_upper {A rho eps delta : ℝ} {n d e : ℕ}
    (hA : 1 ≤ A) (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1 / 2)
    (he0 : 0 < eps) (hde : delta ≤ eps) (he : eps ≤ 1 / 2) (hdelta : 0 < delta) :
    (sampleCount e A n d rho eps delta : ℝ) ≤
      sampleConstant e n A rho * ((d : ℝ) / eps) ^ e * Real.log ((d : ℝ) / delta) := by
  let m := gridSize A n d rho eps
  let C := gridConstant A n rho
  let L := sampleLogConstant C n
  let x := (d : ℝ) / eps
  let R := (d : ℝ) / delta
  have hC2 : 2 ≤ C := gridConstant_ge_two hA hr0 hr he0 he
  have hC : 1 ≤ C := by linarith
  have hx2 : 2 ≤ x := scale_ge_two hd he0 he
  have hR2 : 2 ≤ R := scale_ge_two hd hdelta (hde.trans he)
  have hx0 : 0 ≤ x := by positivity
  have hm1 : (1 : ℝ) ≤ m := (grid_constraints A n d rho eps).1
  have hm0 : (0 : ℝ) < m := by linarith
  have hCC : 0 < contaminationConstant rho := by
    unfold contaminationConstant
    have hh : 0 < 1 - 2 * rho := by linarith
    positivity
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogR : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR2
  have hL : 0 < L := by
    dsimp [L, sampleLogConstant]
    have hcLog : 0 ≤ Real.log C := Real.log_nonneg hC
    positivity
  have hmlog := occupancy_log_upper (n := n) (gridSize_pos A n d rho eps) hd hC he0 hde he hdelta
    (gridSize_upper hA hd hr0 hr he0 he)
  have harg : 1 ≤ 2 * (m : ℝ) ^ n / delta := by
    apply (le_div_iff₀ hdelta).2
    have hpow := one_le_pow₀ hm1 (n := n)
    linarith [hde.trans he]
  have hlog0 : 0 ≤ Real.log (2 * (m : ℝ) ^ n / delta) := Real.log_nonneg harg
  have hraw0 : 0 ≤ contaminationConstant rho * (m : ℝ) ^ e *
      Real.log (2 * (m : ℝ) ^ n / delta) := by positivity
  have hceil := (Nat.ceil_lt_add_one hraw0).le
  have hpow : (m : ℝ) ^ e ≤ (C * x) ^ e :=
    pow_le_pow_left₀ hm0.le (gridSize_upper hA hd hr0 hr he0 he) e
  have hraw : contaminationConstant rho * (m : ℝ) ^ e *
      Real.log (2 * (m : ℝ) ^ n / delta) ≤
      (contaminationConstant rho * C ^ e * L) * x ^ e * Real.log R := by
    calc
      _ ≤ (contaminationConstant rho * (C * x) ^ e) * (L * Real.log R) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hCC.le) hmlog hlog0 (by positivity)
      _ = _ := by rw [mul_pow]; ring
  have hunit : 1 ≤ (1 / Real.log 2) * x ^ e * Real.log R := by
    have hxpow : 1 ≤ x ^ e := one_le_pow₀ (by linarith : (1 : ℝ) ≤ x)
    have hh : Real.log 2 ≤ x ^ e * Real.log R := by
      nlinarith [mul_le_mul_of_nonneg_right hxpow (hlog2.le.trans hlogR)]
    have hh' : 1 ≤ (x ^ e * Real.log R) / Real.log 2 :=
      (le_div_iff₀ hlog2).2 (by simpa only [one_mul] using hh)
    convert hh' using 1 <;> ring
  change (Nat.ceil (contaminationConstant rho * (m : ℝ) ^ e *
    Real.log (2 * (m : ℝ) ^ n / delta)) : ℝ) ≤ _
  dsimp [sampleConstant]
  change _ ≤ (contaminationConstant rho * C ^ e * L + 1 / Real.log 2) * x ^ e * Real.log R
  nlinarith

/-- Positivity of the sample bound constant, uniformly in the varying inputs. -/
theorem sampleConstant_positive {A rho : ℝ} (e n : ℕ) (hA : 1 ≤ A)
    (hr0 : 0 ≤ rho) (hr : rho < 1 / 2) : 0 < sampleConstant e n A rho := by
  have hC2 := gridConstant_ge_two (eps := (1 / 2 : ℝ)) (n := n)
    hA hr0 hr (by norm_num) (by norm_num)
  have hC0 : 0 < gridConstant A n rho := by linarith
  have hlogC : 0 ≤ Real.log (gridConstant A n rho) := Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hCC : 0 < contaminationConstant rho := by
    unfold contaminationConstant
    have hh : 0 < 1 - 2 * rho := by linarith
    positivity
  unfold sampleConstant sampleLogConstant
  positivity

/-- Both source sample rates, with constants quantified before `d,eps,delta`.
This is a uniform pointwise formulation of the two `O_{n,rho}` claims once
the allowed fixed dimension constant `A=A_n` has been selected. -/
theorem source_sample_uniform_bounds (A : ℝ) (n : ℕ) (rho : ℝ)
    (hA : 1 ≤ A) (hr0 : 0 ≤ rho) (hr : rho < 1 / 2) :
    ∃ KC KU : ℝ, 0 < KC ∧ 0 < KU ∧
      ∀ (d : ℕ) (eps delta : ℝ), 1 ≤ d → 0 < delta → delta ≤ eps → eps ≤ 1 / 2 →
        (chebyshevSamples A n d rho eps delta : ℝ) ≤
          KC * ((d : ℝ) / eps) ^ n * Real.log ((d : ℝ) / delta) ∧
        (uniformSamples A n d rho eps delta : ℝ) ≤
          KU * ((d : ℝ) / eps) ^ (2 * n) * Real.log ((d : ℝ) / delta) := by
  refine ⟨sampleConstant n n A rho, sampleConstant (2 * n) n A rho,
    sampleConstant_positive n n hA hr0 hr,
    sampleConstant_positive (2 * n) n hA hr0 hr, ?_⟩
  intro d eps delta hd hdelta hde he
  have he0 : 0 < eps := hdelta.trans_le hde
  exact ⟨sampleCount_upper hA hd hr0 hr he0 hde he hdelta,
    sampleCount_upper hA hd hr0 hr he0 hde he hdelta⟩

/-- Uniform positive constants for the `Theta` statement (2.3). -/
theorem source_grid_uniform_bounds (A : ℝ) (n : ℕ) (rho : ℝ)
    (hn : 1 ≤ n) (hA : 1 ≤ A) (hr0 : 0 ≤ rho) (hr : rho < 1 / 2) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (d : ℕ) (eps : ℝ), 1 ≤ d → 0 < eps → eps ≤ 1 / 2 →
        c * ((d : ℝ) / eps) ≤ gridSize A n d rho eps ∧
        (gridSize A n d rho eps : ℝ) ≤ C * ((d : ℝ) / eps) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hC2 := gridConstant_ge_two (eps := (1 / 2 : ℝ)) (n := n)
    hA hr0 hr (by norm_num) (by norm_num)
  refine ⟨72 * Real.pi * n, gridConstant A n rho, by positivity, by linarith, ?_⟩
  intro d eps hd he0 he
  exact ⟨gridSize_lower A rho n d he0, gridSize_upper hA hd hr0 hr he0 he⟩

/-- Logarithms give a sufficient budget for any positive geometric factor. -/
theorem geometric_budget_of_log_bound {b K eps : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hK : 0 < K) (heps : 0 < eps) (t : ℕ)
    (ht : Real.log (2 * K / eps) / (-Real.log b) ≤ t) :
    b ^ t * K ≤ eps / 2 := by
  have hlogb : Real.log b < 0 := Real.log_neg hb0 hb1
  have ht' := (div_le_iff₀ (neg_pos.mpr hlogb)).mp ht
  apply (Real.log_le_log_iff (mul_pos (pow_pos hb0 t) hK) (half_pos heps)).mp
  rw [Real.log_mul (pow_ne_zero t hb0.ne') hK.ne', Real.log_pow,
    Real.log_div heps.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Real.log_div (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hK.ne') heps.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hK.ne'] at ht'
  nlinarith

theorem log_bound_of_geometric_budget {b K eps : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hK : 0 < K) (heps : 0 < eps) (t : ℕ) (ht : b ^ t * K ≤ eps / 2) :
    Real.log (2 * K / eps) / (-Real.log b) ≤ t := by
  have hlogb : Real.log b < 0 := Real.log_neg hb0 hb1
  have hlog := Real.log_le_log (mul_pos (pow_pos hb0 t) hK) ht
  rw [Real.log_mul (pow_ne_zero t hb0.ne') hK.ne', Real.log_pow,
    Real.log_div heps.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlog
  apply (div_le_iff₀ (neg_pos.mpr hlogb)).2
  rw [Real.log_div (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hK.ne') heps.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hK.ne']
  nlinarith

def budgetLogQuotient (n d : ℕ) (rho eps : ℝ) : ℝ :=
  Real.log (2 * initializationFactor n d rho / eps) / (-Real.log (beta eps))

/-- The least source budget is bounded by the exact natural log-ceiling. -/
theorem refinementBudget_le_logCeil (n d : ℕ) (rho eps : ℝ)
    (hr : rho < 1 / 2) (he0 : 0 < eps) (he : eps ≤ 1 / 2) :
    refinementBudget n d rho eps he0 he ≤ Nat.ceil (budgetLogQuotient n d rho eps) := by
  have hg : 0 < gap rho := by unfold gap; linarith
  have hK : 0 < initializationFactor n d rho := by
    unfold initializationFactor
    positivity
  have hb0 : 0 < beta eps := by unfold beta; positivity
  have hb1 : beta eps < 1 := by unfold beta; linarith
  apply refinementBudget_minimal
  apply geometric_budget_of_log_bound hb0 hb1 hK he0
  exact Nat.le_ceil (budgetLogQuotient n d rho eps)

theorem refinementBudget_eq_logCeil (n d : ℕ) (rho eps : ℝ)
    (hr : rho < 1 / 2) (he0 : 0 < eps) (he : eps ≤ 1 / 2) :
    refinementBudget n d rho eps he0 he = Nat.ceil (budgetLogQuotient n d rho eps) := by
  apply Nat.le_antisymm (refinementBudget_le_logCeil n d rho eps hr he0 he)
  have hg : 0 < gap rho := by unfold gap; linarith
  have hK : 0 < initializationFactor n d rho := by
    unfold initializationFactor
    positivity
  have hb0 : 0 < beta eps := by unfold beta; positivity
  have hb1 : beta eps < 1 := by unfold beta; linarith
  apply Nat.ceil_le.mpr
  exact log_bound_of_geometric_budget hb0 hb1 hK he0 _
    (refinementBudget_spec n d rho eps he0 he)

theorem budget_denominator (eps : ℝ) (he0 : 0 < eps) :
    -Real.log (beta eps) = Real.log (12 / eps) := by
  rw [beta, Real.log_div he0.ne' (by norm_num : (12 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (12 : ℝ) ≠ 0) he0.ne']
  ring

theorem budgetLogQuotient_source (n d : ℕ) (rho eps : ℝ) (he0 : 0 < eps) :
    budgetLogQuotient n d rho eps =
      Real.log (8 * (2 * (d : ℝ) + 1) ^ n / (gap rho * eps)) / Real.log (12 / eps) := by
  rw [budgetLogQuotient, budget_denominator eps he0]
  congr 2
  unfold initializationFactor
  ring

theorem budget_denominator_lower {eps : ℝ} (he0 : 0 < eps) (he : eps ≤ 1 / 2) :
    Real.log 24 ≤ -Real.log (beta eps) := by
  rw [budget_denominator eps he0]
  apply Real.log_le_log (by norm_num)
  apply (le_div_iff₀ he0).2
  linarith

def budgetConstant (n : ℕ) (rho : ℝ) : ℝ :=
  1 + (Real.log (8 / gap rho) + n * Real.log 3 + ((n : ℝ) + 1)) / Real.log 24

theorem budget_numerator_upper {n d : ℕ} {rho eps : ℝ}
    (hd : 1 ≤ d) (hr : rho < 1 / 2) (he0 : 0 < eps) (he : eps ≤ 1 / 2) :
    Real.log (2 * initializationFactor n d rho / eps) ≤
      Real.log (8 / gap rho) + (n : ℝ) * Real.log 3 +
        ((n : ℝ) + 1) * Real.log ((d : ℝ) / eps) := by
  have hg : 0 < gap rho := by unfold gap; linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase : 0 < 2 * (d : ℝ) + 1 := by positivity
  have heq : 2 * initializationFactor n d rho / eps =
      (8 / gap rho) * (2 * (d : ℝ) + 1) ^ n / eps := by
    unfold initializationFactor
    ring
  rw [heq, Real.log_div (by positivity : (8 / gap rho) * (2 * (d : ℝ) + 1) ^ n ≠ 0) he0.ne',
    Real.log_mul (by positivity : (8 / gap rho) ≠ 0) (pow_ne_zero n hbase.ne'), Real.log_pow]
  have hb : Real.log (2 * (d : ℝ) + 1) ≤ Real.log 3 + Real.log (d : ℝ) := by
    simpa only [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hd0.ne'] using
      Real.log_le_log hbase (by linarith : 2 * (d : ℝ) + 1 ≤ 3 * d)
  have hlogeps : Real.log eps ≤ 0 := Real.log_nonpos he0.le (by linarith)
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1
  have hlogR : Real.log ((d : ℝ) / eps) = Real.log (d : ℝ) - Real.log eps :=
    Real.log_div hd0.ne' he0.ne'
  have hnb := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hnlog := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (neg_nonneg.mpr hlogeps)
  nlinarith

/-- A concrete pointwise `O_{n,rho}(1+log(d/eps))` bound for the least budget. -/
theorem refinementBudget_upper {n d : ℕ} {rho eps : ℝ}
    (hd : 1 ≤ d) (hr0 : 0 ≤ rho) (hr : rho < 1 / 2)
    (he0 : 0 < eps) (he : eps ≤ 1 / 2) :
    (refinementBudget n d rho eps he0 he : ℝ) ≤
      budgetConstant n rho * (1 + Real.log ((d : ℝ) / eps)) := by
  let B := Real.log (8 / gap rho) + (n : ℝ) * Real.log 3
  let R := Real.log ((d : ℝ) / eps)
  let Y := (B + ((n : ℝ) + 1) * R) / Real.log 24
  have hp := parameter_ranges hr0 hr he0 he
  have hg : 0 < gap rho := hp.2.1.1
  have hg8 : 1 ≤ 8 / gap rho := by
    apply (le_div_iff₀ hg).2
    linarith [hp.2.1.2]
  have hB : 0 ≤ B := add_nonneg (Real.log_nonneg hg8)
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
  have hR : 0 ≤ R := Real.log_nonneg (by linarith [scale_ge_two hd he0 he])
  have h24 : 0 < Real.log (24 : ℝ) := Real.log_pos (by norm_num)
  have hden := budget_denominator_lower he0 he
  have hden0 : 0 < -Real.log (beta eps) := h24.trans_le hden
  have hnum := budget_numerator_upper (n := n) hd hr he0 he
  have hN : 0 ≤ B + ((n : ℝ) + 1) * R := by positivity
  have hq : budgetLogQuotient n d rho eps ≤ Y := by
    apply (div_le_div_iff₀ hden0 h24).2
    exact (mul_le_mul_of_nonneg_right hnum h24.le).trans
      (mul_le_mul_of_nonneg_left hden hN)
  have hY : 0 ≤ Y := div_nonneg hN h24.le
  have hceil := Nat.ceil_mono hq
  have hceilY := (Nat.ceil_lt_add_one hY).le
  have hT : (refinementBudget n d rho eps he0 he : ℝ) ≤ (Nat.ceil Y : ℝ) := by
    exact_mod_cast (refinementBudget_le_logCeil n d rho eps hr he0 he).trans hceil
  have hdiff : budgetConstant n rho * (1 + R) - (Y + 1) =
      R + (B * R + ((n : ℝ) + 1)) / Real.log 24 := by
    dsimp [budgetConstant, Y, B]
    ring
  have hright : 0 ≤ R + (B * R + ((n : ℝ) + 1)) / Real.log 24 := by positivity
  change _ ≤ budgetConstant n rho * (1 + R)
  linarith

/-- The iteration constant is fixed before the accuracy and degree inputs. -/
theorem source_budget_uniform_bound (n : ℕ) (rho : ℝ)
    (hr0 : 0 ≤ rho) (hr : rho < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (eps : ℝ) (hd : 1 ≤ d)
      (he0 : 0 < eps) (he : eps ≤ 1 / 2),
      (refinementBudget n d rho eps he0 he : ℝ) ≤
        C * (1 + Real.log ((d : ℝ) / eps)) := by
  have hp := parameter_ranges (eps := (1 / 2 : ℝ)) hr0 hr (by norm_num) (by norm_num)
  have hg8 : 1 ≤ 8 / gap rho := by
    apply (le_div_iff₀ hp.2.1.1).2
    linarith [hp.2.1.2]
  have hlog8 : 0 ≤ Real.log (8 / gap rho) := Real.log_nonneg hg8
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog24 : 0 < Real.log (24 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨budgetConstant n rho, ?_, ?_⟩
  · unfold budgetConstant
    positivity
  · intro d eps hd he0 he
    exact refinementBudget_upper hd hr0 hr he0 he

/-- Absorbing `1` into `log(d/eps)` gives the source's exact stated logarithmic
order, with the fixed constant chosen before all degree/accuracy inputs. -/
theorem source_budget_log_uniform_bound (n : ℕ) (rho : ℝ)
    (hr0 : 0 ≤ rho) (hr : rho < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (eps : ℝ) (hd : 1 ≤ d)
      (he0 : 0 < eps) (he : eps ≤ 1 / 2),
      (refinementBudget n d rho eps he0 he : ℝ) ≤ C * Real.log ((d : ℝ) / eps) := by
  obtain ⟨C, hC, hu⟩ := source_budget_uniform_bound n rho hr0 hr
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨C * (1 + 1 / Real.log 2), by positivity, ?_⟩
  intro d eps hd he0 he
  have hlogR : Real.log 2 ≤ Real.log ((d : ℝ) / eps) :=
    Real.log_le_log (by norm_num) (scale_ge_two hd he0 he)
  have hunit : 1 ≤ Real.log ((d : ℝ) / eps) / Real.log 2 :=
    (le_div_iff₀ hlog2).2 (by simpa only [one_mul] using hlogR)
  have hscale : 1 + Real.log ((d : ℝ) / eps) ≤
      (1 + 1 / Real.log 2) * Real.log ((d : ℝ) / eps) := by
    calc
      _ ≤ Real.log ((d : ℝ) / eps) / Real.log 2 + Real.log ((d : ℝ) / eps) :=
        add_le_add_right hunit _
      _ = _ := by ring
  calc
    _ ≤ C * (1 + Real.log ((d : ℝ) / eps)) := hu d eps hd he0 he
    _ ≤ C * ((1 + 1 / Real.log 2) * Real.log ((d : ℝ) / eps)) :=
      mul_le_mul_of_nonneg_left hscale hC.le
    _ = _ := by ring

end

end Paper34.SourceComplexity
