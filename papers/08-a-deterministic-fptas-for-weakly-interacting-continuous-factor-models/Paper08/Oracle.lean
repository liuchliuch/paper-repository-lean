import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic
import Paper08.Basic

/-!
# Assumption 1.1 — effective value access, dyadic arithmetic, log series

Formalises the computational model of Assumption 1.1 and the finite-precision
ingredients of Section 3.2:

* `Oracle k Ψ` — a deterministic value oracle returning binary rationals
  accurate to `2^{-b}`;
* `dyad P y` — floor-based dyadic rounding with error `≤ 2^{-P}`;
* the logarithm series `log y = 2 ∑_j v^{2j+1}/(2j+1)` for `y ∈ [1,2]`,
  `v = (y-1)/(y+1)`, including the tail bound of §3.2;
* the sample-error composition (3.12) of Lemma 3.3.

Completely proved: no `sorry`, no extra axioms.
-/

noncomputable section

open scoped Real BigOperators

namespace Paper08
namespace Oracle

/-! ## Binary (dyadic) rationals -/

/-- A rational is binary when it equals `m / 2^k` for some `m : ℤ`, `k : ℕ`. -/
def IsBinary (y : ℚ) : Prop :=
  ∃ (m : ℤ) (k : ℕ), y = m / (2:ℚ) ^ k

lemma isBinary_zero : IsBinary (0 : ℚ) :=
  ⟨0, 0, by norm_num⟩

lemma isBinary_one : IsBinary (1 : ℚ) :=
  ⟨1, 0, by norm_num⟩

lemma isBinary_add {a b : ℚ} (ha : IsBinary a) (hb : IsBinary b) : IsBinary (a + b) := by
  obtain ⟨m₁, k₁, rfl⟩ := ha
  obtain ⟨m₂, k₂, rfl⟩ := hb
  refine ⟨m₁ * 2 ^ k₂ + m₂ * 2 ^ k₁, k₁ + k₂, ?_⟩
  have h1 : (2:ℚ) ^ (k₁ + k₂) = (2:ℚ) ^ k₁ * (2:ℚ) ^ k₂ := by ring
  rw [h1]
  field_simp
  push_cast
  ring

lemma isBinary_mul {a b : ℚ} (ha : IsBinary a) (hb : IsBinary b) : IsBinary (a * b) := by
  obtain ⟨m₁, k₁, rfl⟩ := ha
  obtain ⟨m₂, k₂, rfl⟩ := hb
  refine ⟨m₁ * m₂, k₁ + k₂, ?_⟩
  have h1 : (2:ℚ) ^ (k₁ + k₂) = (2:ℚ) ^ k₁ * (2:ℚ) ^ k₂ := by ring
  rw [h1]
  field_simp
  push_cast
  ring

/-! ## Dyadic rounding -/

/-- Floor-based dyadic approximation of a real to `P` fractional bits. -/
def dyad (P : ℕ) (y : ℝ) : ℝ :=
  (Int.floor (y * (2:ℝ) ^ P) : ℝ) / (2:ℝ) ^ P

/-- The same construction on rationals; the result is binary. -/
def dyadQ (P : ℕ) (y : ℚ) : ℚ :=
  (Int.floor (y * (2:ℚ) ^ P) : ℚ) / (2:ℚ) ^ P

lemma dyadQ_isBinary (P : ℕ) (y : ℚ) : IsBinary (dyadQ P y) :=
  ⟨Int.floor (y * (2:ℚ) ^ P), P, rfl⟩

/-- Rounding never overshoots: `dyad P y ≤ y`. -/
lemma dyad_le (P : ℕ) (y : ℝ) : dyad P y ≤ y := by
  have hpos : (0:ℝ) < (2:ℝ) ^ P := by positivity
  have h := Int.floor_le (y * (2:ℝ) ^ P)
  rw [dyad, div_le_iff₀ hpos]
  nlinarith

/-- Rounding undershoots by less than `2^{-P}`. -/
lemma lt_dyad_add_two_neg (P : ℕ) (y : ℝ) : y < dyad P y + (2:ℝ) ^ (-(P:ℝ)) := by
  have hpos : (0:ℝ) < (2:ℝ) ^ P := by positivity
  have h := Int.lt_floor_add_one (y * (2:ℝ) ^ P)
  have hpow : (2:ℝ) ^ (-(P:ℝ)) = ((2:ℝ) ^ P)⁻¹ := by
    rw [show (-(P:ℝ)) = -((P:ℝ)) by ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [hpow]
  show y < (Int.floor (y * (2:ℝ) ^ P) : ℝ) / (2:ℝ) ^ P + ((2:ℝ) ^ P)⁻¹
  have hform : ((Int.floor (y * (2:ℝ) ^ P) : ℝ) / (2:ℝ) ^ P) + ((2:ℝ) ^ P)⁻¹
      = ((Int.floor (y * (2:ℝ) ^ P) : ℝ) + 1) / (2:ℝ) ^ P := by
    field_simp
  rw [hform]
  rw [lt_div_iff₀ hpos]
  nlinarith

/-- Main rounding estimate: `|dyad P y - y| ≤ 2^{-P}`. -/
lemma abs_dyad_sub_le (P : ℕ) (y : ℝ) :
    |dyad P y - y| ≤ (2:ℝ) ^ (-(P:ℝ)) := by
  have h1 : dyad P y ≤ y := dyad_le P y
  have h2 : y < dyad P y + (2:ℝ) ^ (-(P:ℝ)) := lt_dyad_add_two_neg P y
  have hnonpos : dyad P y - y ≤ 0 := by linarith
  have habs : |dyad P y - y| = y - dyad P y := by
    rw [abs_of_nonpos hnonpos]; ring
  rw [habs]
  linarith

/-- Rounding is the identity on values already given to `P` fractional bits. -/
lemma dyad_dyadic {P : ℕ} {k : ℤ} :
    dyad P ((k : ℝ) / (2:ℝ) ^ P) = (k : ℝ) / (2:ℝ) ^ P := by
  have hmul : ((k : ℝ) / (2:ℝ) ^ P) * (2:ℝ) ^ P = (k : ℝ) := by
    have hpos : (0:ℝ) < (2:ℝ) ^ P := by positivity
    field_simp
  rw [dyad, hmul, Int.floor_intCast]

/-- Projection onto `[1,2]`, as used in the proof of Lemma 3.3
(`q < 1/3` under (1.3) gives `e^q < 2`). -/
def project12 (y : ℝ) : ℝ := min 2 (max 1 y)

lemma one_le_project12 (y : ℝ) : 1 ≤ project12 y := by
  unfold project12
  have h1 : (1:ℝ) ≤ max 1 y := le_max_left 1 y
  have h2 : (1:ℝ) ≤ 2 := by norm_num
  exact le_min h2 h1

lemma project12_le_two (y : ℝ) : project12 y ≤ 2 :=
  min_le_left _ _

/-- Projection onto `[1,2]` does not increase the distance to a point of `[1,2]`. -/
lemma abs_project12_sub_le {y z : ℝ} (hz : 1 ≤ z) (hz2 : z ≤ 2) :
    |project12 y - z| ≤ |y - z| := by
  have h1 : |max 1 y - z| ≤ |y - z| := by
    rcases le_total y 1 with hy | hy
    · rw [max_eq_left hy]
      rw [abs_of_nonpos (by linarith : (1:ℝ) - z ≤ 0)]
      rw [abs_of_nonpos (by linarith : y - z ≤ 0)]
      linarith
    · rw [max_eq_right hy]
  have h2 : |min 2 (max 1 y) - z| ≤ |max 1 y - z| := by
    rcases le_total (max 1 y) 2 with hm | hm
    · rw [min_eq_right hm]
    · rw [min_eq_left hm]
      rw [abs_of_nonneg (by linarith : (2:ℝ) - z ≥ 0)]
      rw [abs_of_nonneg (by linarith : max 1 y - z ≥ 0)]
      have : (1:ℝ) ≤ max 1 y := le_max_left 1 y
      linarith
  unfold project12
  exact le_trans h2 h1

/-! ## The value oracle (Assumption 1.1) -/

/-- Assumption 1.1: a deterministic value oracle for a local function
`Ψ : (Fin k → ℝ) → ℝ`.  `query x b` is a binary rational with
`|query x b - Ψ x| ≤ 2^{-b}`. -/
structure Oracle (k : ℕ) (Ψ : (Fin k → ℝ) → ℝ) where
  /-- Deterministic answer at a rational point, to precision `2^{-b}`. -/
  query : (x : Fin k → ℚ) → (b : ℕ) → ℚ
  /-- Accuracy: `|query x b - Ψ x| ≤ 2^{-b}` (Assumption 1.1). -/
  query_approx : ∀ (x : Fin k → ℚ) (b : ℕ),
      (∀ i, 0 ≤ x i ∧ x i ≤ 1) → 1 ≤ b →
      |((query x b : ℚ) : ℝ) - Ψ (fun i => (x i : ℝ))| ≤ (2:ℝ) ^ (-(b:ℝ))
  /-- The answer is a binary rational (Assumption 1.1). -/
  query_binary : ∀ (x : Fin k → ℚ) (b : ℕ), IsBinary (query x b)

/-- A family of oracles, one per factor occurrence. -/
structure OracleFamily (ι : Type*) (k : ℕ) (Ψ : ι → (Fin k → ℝ) → ℝ) where
  /-- The oracle of factor `e`. -/
  get : (e : ι) → Oracle k (Ψ e)

/-- Accuracy after projection onto `[1,2]`: for a true value in `[1,2]`,
projection cannot increase the error of a `2^{-b}`-accurate answer. -/
lemma projected_query_error {y z b : ℝ} (hz : 1 ≤ z) (hz2 : z ≤ 2)
    (herr : |y - z| ≤ (2:ℝ) ^ (-(b:ℝ))) :
    |project12 y - z| ≤ (2:ℝ) ^ (-(b:ℝ)) :=
  le_trans (abs_project12_sub_le hz hz2) herr

/-! ## Logarithm series of §3.2 -/

/-- Partial sums `logSeries N v = 2 ∑_{j < N} v^{2j+1} / (2j+1)`. -/
def logSeries (N : ℕ) (v : ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.range N, v ^ (2 * j + 1) / (2 * (j:ℝ) + 1)

lemma logSeries_eq_sum (N : ℕ) (v : ℝ) :
    logSeries N v = ∑ j ∈ Finset.range N, (2:ℝ) * (v ^ (2 * j + 1) / (2 * (j:ℝ) + 1)) := by
  simp [logSeries, Finset.mul_sum]

/-- For `y > 0` and `v = (y-1)/(y+1)` one has `log y = log(1+v) - log(1-v)`. -/
lemma log_eq_log_sub_log {y v : ℝ} (hy : 0 < y) (hv : v = (y - 1) / (y + 1)) :
    Real.log y = Real.log (1 + v) - Real.log (1 - v) := by
  have hne : y + 1 ≠ 0 := by
    have : 0 < y + 1 := by linarith
    exact ne_of_gt this
  have h1 : 1 + v = 2 * y / (y + 1) := by
    rw [hv]; field_simp; ring
  have h2 : 1 - v = 2 / (y + 1) := by
    rw [hv]; field_simp; ring
  have hpos1 : 0 < 1 + v := by rw [h1]; positivity
  have hpos2 : 0 < 1 - v := by rw [h2]; positivity
  have harg : (1 + v) / (1 - v) = y := by
    rw [h1, h2]; field_simp
  rw [← harg]
  exact Real.log_div hpos1.ne' hpos2.ne'

/-- Range of `v = (y-1)/(y+1)` for `y ∈ [1,2]`: `v ≥ 0`. -/
lemma v_nonneg {y : ℝ} (hy : 1 ≤ y) (v : ℝ) (hv : v = (y - 1) / (y + 1)) :
    0 ≤ v := by
  rw [hv]
  exact div_nonneg (sub_nonneg.mpr hy) (by linarith)

lemma v_le_one_third {y : ℝ} (hy : 1 ≤ y) (hy2 : y ≤ 2) (v : ℝ)
    (hv : v = (y - 1) / (y + 1)) :
    v ≤ 1 / 3 := by
  rw [hv]
  have hpos : 0 < y + 1 := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith

lemma abs_v_lt_one {y : ℝ} (hy : 1 ≤ y) (v : ℝ) (hv : v = (y - 1) / (y + 1)) :
    |v| < 1 := by
  rw [hv]
  have hpos : 0 < y + 1 := by linarith
  rw [abs_div, abs_of_pos hpos, div_lt_one hpos]
  rcases le_total 1 y with h1 | h1
  · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonpos (by linarith)]; linarith

/-- The series sums to `log y` for `y ∈ [1,2]` under `v = (y-1)/(y+1)`. -/
theorem logSeries_tsum {y v : ℝ} (hy : 1 ≤ y) (hv : v = (y - 1) / (y + 1)) :
    (∑' j : ℕ, (2:ℝ) * (v ^ (2 * j + 1) / (2 * (j:ℝ) + 1))) = Real.log y := by
  have hlt : |v| < 1 := abs_v_lt_one hy v hv
  have h := Real.hasSum_log_sub_log_of_abs_lt_one hlt
  have hser : (fun k : ℕ => (2:ℝ) * (1 / (2 * (k:ℝ) + 1)) * v ^ (2 * k + 1))
      = (fun k : ℕ => (2:ℝ) * (v ^ (2 * k + 1) / (2 * (k:ℝ) + 1))) := by
    funext k; ring
  rw [hser] at h
  rw [h.tsum_eq]
  exact (log_eq_log_sub_log (by linarith : 0 < y) hv).symm

/-- The partial sums never overshoot `log y` (all series terms are nonnegative
for `y ∈ [1,2]`). -/
lemma logSeries_le_log {y v : ℝ} (hy : 1 ≤ y) (hv : v = (y - 1) / (y + 1)) (N : ℕ) :
    logSeries N v ≤ Real.log y := by
  have hv0 : 0 ≤ v := v_nonneg hy v hv
  have hlt : |v| < 1 := abs_v_lt_one hy v hv
  have hsummable : Summable fun j : ℕ => (2:ℝ) * (v ^ (2 * j + 1) / (2 * (j:ℝ) + 1)) := by
    have h := (Real.hasSum_log_sub_log_of_abs_lt_one hlt).summable
    have hser : (fun k : ℕ => (2:ℝ) * (1 / (2 * (k:ℝ) + 1)) * v ^ (2 * k + 1))
        = (fun k : ℕ => (2:ℝ) * (v ^ (2 * k + 1) / (2 * (k:ℝ) + 1))) := by
      funext k; ring
    rw [← hser]
    exact h
  have hnonneg : ∀ j : ℕ, 0 ≤ (2:ℝ) * (v ^ (2 * j + 1) / (2 * (j:ℝ) + 1)) := by
    intro j
    positivity
  have hpartial : ∑ j ∈ Finset.range N, (2:ℝ) * (v ^ (2 * j + 1) / (2 * (j:ℝ) + 1))
      ≤ ∑' j : ℕ, (2:ℝ) * (v ^ (2 * j + 1) / (2 * (j:ℝ) + 1)) :=
    hsummable.sum_le_tsum (Finset.range N) (fun j _ => hnonneg j)
  rw [logSeries_eq_sum]
  rw [logSeries_tsum hy hv] at hpartial
  exact hpartial

/-- The tail of the logarithm series is nonnegative. -/
lemma log_nonneg_sub_logSeries {y v : ℝ} (hy : 1 ≤ y) (hv : v = (y - 1) / (y + 1)) (N : ℕ) :
    0 ≤ Real.log y - logSeries N v := by
  linarith [logSeries_le_log hy hv N, Real.log_nonneg hy]

/-- Helper: `v^{2(j+N)+1} = v^{2N+1} · v^{2j}`. -/
lemma pow_two_mul_add_shift {v : ℝ} (j N : ℕ) :
    v ^ (2 * (j + N) + 1) = v ^ (2 * N + 1) * v ^ (2 * j) := by
  have h : (2 * (j + N) + 1 : ℕ) = (2 * N + 1) + 2 * j := by omega
  rw [h, pow_add]

/-- Helper: `(1/2)^{2N+1} = 2^{-(2N+1)}`. -/
lemma one_div_two_pow (n : ℕ) : (1 / 2 : ℝ) ^ n = (2:ℝ) ^ (-(n:ℝ)) := by
  have h : (1 / 2 : ℝ) = (2:ℝ)⁻¹ := by norm_num
  rw [h, ← Real.rpow_natCast, ← Real.rpow_neg_one, ← Real.rpow_mul]
  · congr 1
    push_cast
    ring
  · norm_num

/-- Tail majorant of §3.2:
`log y - logSeries N v ≤ 2 v^{2N+1} / ((2N+1)(1-v^2))`. -/
lemma log_tail_le {y v : ℝ} (hy : 1 ≤ y) (hv : v = (y - 1) / (y + 1)) (N : ℕ) :
    Real.log y - logSeries N v
      ≤ 2 * v ^ (2 * N + 1) / ((2 * (N:ℝ) + 1) * (1 - v ^ 2)) := by
  have hy0 : 0 < y := by linarith
  have hv0 : 0 ≤ v := v_nonneg hy v hv
  have hlt : |v| < 1 := abs_v_lt_one hy v hv
  have hlt2 : v ^ 2 < 1 := by
    have : v ^ 2 = |v| ^ 2 := by simp [sq_abs]
    rw [this]
    nlinarith [abs_nonneg v]
  have hgt2 : 0 < 1 - v ^ 2 := by linarith
  set f : ℕ → ℝ := fun j => (2:ℝ) * (v ^ (2 * j + 1) / (2 * (j:ℝ) + 1)) with hf
  have hfsum : (∑' j : ℕ, f j) = Real.log y := by
    rw [hf]
    exact logSeries_tsum hy hv
  have hsummable : Summable f := by
    rw [hf]
    have h := (Real.hasSum_log_sub_log_of_abs_lt_one hlt).summable
    have hser : (fun k : ℕ => (2:ℝ) * (1 / (2 * (k:ℝ) + 1)) * v ^ (2 * k + 1))
        = (fun k : ℕ => (2:ℝ) * (v ^ (2 * k + 1) / (2 * (k:ℝ) + 1))) := by
      funext k; ring
    rw [← hser]
    exact h
  have hsplit : (∑' j : ℕ, f j)
      = (∑ j ∈ Finset.range N, f j) + (∑' j : ℕ, f (j + N)) :=
    (hsummable.sum_add_tsum_nat_add N).symm
  have hlogSeries : logSeries N v = ∑ j ∈ Finset.range N, f j := by
    rw [hf, logSeries_eq_sum]
  -- rewrite the goal as an inequality on the tail
  have hgoal : Real.log y - logSeries N v = ∑' j : ℕ, f (j + N) := by
    rw [← hfsum, hlogSeries, hsplit]
    ring
  rw [hgoal]
  -- rewrite f (j+N)
  have hshift : ∀ j : ℕ,
      f (j + N) = 2 * v ^ (2 * N + 1) * (v ^ (2 * j) / (2 * ((j:ℝ) + N) + 1)) := by
    intro j
    unfold f
    rw [pow_two_mul_add_shift j N]
    push_cast
    ring
  have hts : (∑' j : ℕ, f (j + N))
      = ∑' j : ℕ, 2 * v ^ (2 * N + 1) * (v ^ (2 * j) / (2 * ((j:ℝ) + N) + 1)) :=
    tsum_congr hshift
  rw [hts]
  have hmul : (∑' j : ℕ, 2 * v ^ (2 * N + 1) * (v ^ (2 * j) / (2 * ((j:ℝ) + N) + 1)))
      = 2 * v ^ (2 * N + 1) * (∑' j : ℕ, v ^ (2 * j) / (2 * ((j:ℝ) + N) + 1)) := by
    rw [← tsum_mul_left]
  rw [hmul]
  have hden : ∀ j : ℕ, (2:ℝ) * ((j:ℝ) + N) + 1 = 2 * (N:ℝ) + 1 + 2 * j := by
    intro j; ring
  have htermle : ∀ j : ℕ,
      0 ≤ v ^ (2 * j) / (2 * ((j:ℝ) + N) + 1) ∧
        v ^ (2 * j) / (2 * ((j:ℝ) + N) + 1) ≤ v ^ (2 * j) / (2 * (N:ℝ) + 1) := by
    intro j
    have hpos : 0 < 2 * (N:ℝ) + 1 := by positivity
    have hpos2 : (0:ℝ) < 2 * ((j:ℝ) + N) + 1 := by
      rw [hden j]; positivity
    have hle : (2 * (N:ℝ) + 1) ≤ 2 * ((j:ℝ) + N) + 1 := by
      rw [hden j]; linarith
    have hpow : 0 ≤ v ^ (2 * j) := pow_nonneg hv0 _
    exact ⟨div_nonneg hpow (le_of_lt hpos2),
      div_le_div_of_nonneg_left hpow hpos hle⟩
  have hgeo_summable : Summable fun j : ℕ => v ^ (2 * j) / (2 * (N:ℝ) + 1) := by
    have hgeo : Summable fun j : ℕ => (v ^ 2) ^ j :=
      summable_geometric_of_lt_one (sq_nonneg v) hlt2
    have hform : (fun j : ℕ => v ^ (2 * j) / (2 * (N:ℝ) + 1))
        = (fun j : ℕ => (v ^ 2) ^ j / (2 * (N:ℝ) + 1)) := by
      funext j
      rw [← pow_mul, mul_comm 2 j]
    rw [hform]
    exact hgeo.div_const _
  have hsumle : (∑' j : ℕ, v ^ (2 * j) / (2 * ((j:ℝ) + N) + 1))
      ≤ ∑' j : ℕ, v ^ (2 * j) / (2 * (N:ℝ) + 1) := by
    refine Summable.tsum_le_tsum (fun j => (htermle j).2) ?_ hgeo_summable
    exact Summable.of_nonneg_of_le (fun j => (htermle j).1) (fun j => (htermle j).2)
      hgeo_summable
  have hgeo : (∑' j : ℕ, v ^ (2 * j) / (2 * (N:ℝ) + 1))
      = (1 / (2 * (N:ℝ) + 1)) * (1 - v ^ 2)⁻¹ := by
    have hform : (fun j : ℕ => v ^ (2 * j) / (2 * (N:ℝ) + 1))
        = (fun j : ℕ => (v ^ 2) ^ j / (2 * (N:ℝ) + 1)) := by
      funext j
      rw [← pow_mul, mul_comm 2 j]
    rw [hform, tsum_div_const]
    have hgeo2 : (∑' j : ℕ, (v ^ 2) ^ j) = (1 - v ^ 2)⁻¹ :=
      tsum_geometric_of_lt_one (sq_nonneg v) hlt2
    rw [hgeo2]
    ring
  rw [hgeo] at hsumle
  have hpos : (0:ℝ) ≤ 2 * v ^ (2 * N + 1) := by positivity
  have hstep : 2 * v ^ (2 * N + 1) * (∑' j : ℕ, v ^ (2 * j) / (2 * ((j:ℝ) + N) + 1))
      ≤ 2 * v ^ (2 * N + 1) * ((1 / (2 * (N:ℝ) + 1)) * (1 - v ^ 2)⁻¹) :=
    mul_le_mul_of_nonneg_left hsumle hpos
  have heq : 2 * v ^ (2 * N + 1) * ((1 / (2 * (N:ℝ) + 1)) * (1 - v ^ 2)⁻¹)
      = 2 * v ^ (2 * N + 1) / ((2 * (N:ℝ) + 1) * (1 - v ^ 2)) := by
    field_simp
  rw [heq] at hstep
  exact hstep

/-- Sufficient condition for the tail to be at most `2^{-(P+1)}` when `v ≤ 1/2`:
if `P + 2 ≤ 2N` then the tail is at most `2^{-(P+1)}`. -/
lemma log_tail_le_two_neg {y v : ℝ} (hy : 1 ≤ y) (hy2 : y ≤ 2)
    (hv : v = (y - 1) / (y + 1)) (P N : ℕ) (hN : P + 2 ≤ 2 * N) :
    Real.log y - logSeries N v ≤ (2:ℝ) ^ (-((P:ℝ) + 1)) := by
  have htail := log_tail_le hy hv N
  have hv0 : 0 ≤ v := v_nonneg hy v hv
  have hv13 : v ≤ 1 / 3 := v_le_one_third hy hy2 v hv
  have hvle : v ≤ 1 / 2 := by linarith
  have hv2 : v ^ 2 ≤ 1 / 4 := by nlinarith
  have hdenpos : (0:ℝ) < (2 * (N:ℝ) + 1) * (1 - v ^ 2) := by
    nlinarith [show (0:ℝ) < 2 * N + 1 by positivity, sq_nonneg v]
  have hden_lb : (3 / 4 : ℝ) ≤ (2 * (N:ℝ) + 1) * (1 - v ^ 2) := by
    have h1 : (1:ℝ) ≤ 2 * N + 1 := by
      have : (0:ℝ) ≤ 2 * N := by positivity
      linarith
    nlinarith [sq_nonneg v]
  have hvpow : v ^ (2 * N + 1) ≤ (1 / 2 : ℝ) ^ (2 * N + 1) :=
    pow_le_pow_left₀ hv0 hvle _
  have hnum : 2 * v ^ (2 * N + 1) ≤ 2 * (1 / 2 : ℝ) ^ (2 * N + 1) := by
    nlinarith [pow_nonneg hv0 (2 * N + 1)]
  have hnum2 : (0:ℝ) ≤ 2 * (1 / 2 : ℝ) ^ (2 * N + 1) := by positivity
  have hmain : 2 * v ^ (2 * N + 1) / ((2 * (N:ℝ) + 1) * (1 - v ^ 2))
      ≤ (8 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 * N + 1) := by
    have step1 : 2 * v ^ (2 * N + 1) / ((2 * (N:ℝ) + 1) * (1 - v ^ 2))
        ≤ 2 * (1 / 2 : ℝ) ^ (2 * N + 1) / ((2 * (N:ℝ) + 1) * (1 - v ^ 2)) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)
    have step2 : 2 * (1 / 2 : ℝ) ^ (2 * N + 1) / ((2 * (N:ℝ) + 1) * (1 - v ^ 2))
        ≤ 2 * (1 / 2 : ℝ) ^ (2 * N + 1) / (3 / 4 : ℝ) := by
      have hrec : ((2 * (N:ℝ) + 1) * (1 - v ^ 2))⁻¹ ≤ (3 / 4 : ℝ)⁻¹ :=
        inv_anti₀ (by norm_num : (0:ℝ) < 3 / 4) hden_lb
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hrec hnum2
    have step3 : 2 * (1 / 2 : ℝ) ^ (2 * N + 1) / (3 / 4 : ℝ)
        = (8 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 * N + 1) := by
      norm_num
      ring
    calc 2 * v ^ (2 * N + 1) / ((2 * (N:ℝ) + 1) * (1 - v ^ 2))
        ≤ 2 * (1 / 2 : ℝ) ^ (2 * N + 1) / ((2 * (N:ℝ) + 1) * (1 - v ^ 2)) := step1
      _ ≤ 2 * (1 / 2 : ℝ) ^ (2 * N + 1) / (3 / 4 : ℝ) := step2
      _ = (8 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 * N + 1) := step3
  have hpow12 : (1 / 2 : ℝ) ^ (2 * N + 1) = (2:ℝ) ^ (-(2 * N + 1 : ℝ)) :=
    by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using one_div_two_pow (2 * N + 1)
  have hPLE : (P:ℝ) - (2 * N:ℝ) ≤ -2 := by
    have hcast : (P:ℝ) + 2 ≤ 2 * (N:ℝ) := by exact_mod_cast hN
    linarith
  have h2pow : (2:ℝ) ^ ((P:ℝ) - (2 * N:ℝ)) ≤ (2:ℝ) ^ ((-(2:ℝ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hPLE
  have h2pow2 : (2:ℝ) ^ ((P:ℝ) - (2 * N:ℝ)) ≤ 1 / 4 := by
    norm_num at h2pow ⊢
    exact h2pow
  have hsub : (-(2 * N + 1 : ℝ)) = -((P:ℝ) + 1) + ((P:ℝ) - (2 * N:ℝ)) := by ring
  have hpowsplit : (2:ℝ) ^ (-(2 * N + 1 : ℝ))
      = (2:ℝ) ^ (-((P:ℝ) + 1)) * (2:ℝ) ^ ((P:ℝ) - (2 * N:ℝ)) := by
    rw [hsub, Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  have hfin : (8 / 3 : ℝ) * (1 / 2 : ℝ) ^ (2 * N + 1) ≤ (2:ℝ) ^ (-((P:ℝ) + 1)) := by
    rw [hpow12, hpowsplit]
    have h83 : (8 / 3 : ℝ) * ((2:ℝ) ^ (-((P:ℝ) + 1)) * (2:ℝ) ^ ((P:ℝ) - (2 * N:ℝ)))
        = (2:ℝ) ^ (-((P:ℝ) + 1)) * ((8 / 3 : ℝ) * (2:ℝ) ^ ((P:ℝ) - (2 * N:ℝ))) := by ring
    rw [h83]
    have hinner : (8 / 3 : ℝ) * (2:ℝ) ^ ((P:ℝ) - (2 * N:ℝ)) ≤ 1 := by
      have h834 : (8 / 3 : ℝ) * (1 / 4) = 2 / 3 := by norm_num
      have h23 : (2 / 3 : ℝ) ≤ 1 := by norm_num
      have := mul_le_mul_of_nonneg_left h2pow2 (by norm_num : (0:ℝ) ≤ 8/3)
      rw [h834] at this
      linarith
    have hposP : (0:ℝ) ≤ (2:ℝ) ^ (-((P:ℝ) + 1)) := by positivity
    nlinarith
  linarith [htail, hmain, hfin]

/-! ## Sample-error composition (3.12) -/

/-- Integer form of (3.12): for `1 ≤ α_e ≤ s`,
`α_e (2^{-b} + 2^{-P}) + 2^{-P} ≤ s 2^{-b} + (s+1) 2^{-P}`. -/
lemma sample_error_nat {s : ℕ} {αe : ℕ} (hα : 1 ≤ αe) (hαs : αe ≤ s) (b P : ℕ) :
    (αe:ℝ) * ((2:ℝ) ^ (-(b:ℝ)) + (2:ℝ) ^ (-(P:ℝ))) + (2:ℝ) ^ (-(P:ℝ))
      ≤ (s:ℝ) * (2:ℝ) ^ (-(b:ℝ)) + ((s:ℝ) + 1) * (2:ℝ) ^ (-(P:ℝ)) := by
  have h1 : (αe:ℝ) * (2:ℝ) ^ (-(b:ℝ)) ≤ (s:ℝ) * (2:ℝ) ^ (-(b:ℝ)) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hαs) (by positivity)
  have h2 : (αe:ℝ) * (2:ℝ) ^ (-(P:ℝ)) ≤ (s:ℝ) * (2:ℝ) ^ (-(P:ℝ)) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hαs) (by positivity)
  have h3 : (0:ℝ) ≤ (2:ℝ) ^ (-(b:ℝ)) := by positivity
  have h4 : (0:ℝ) ≤ (2:ℝ) ^ (-(P:ℝ)) := by positivity
  have h5 : (αe:ℝ) * ((2:ℝ) ^ (-(b:ℝ)) + (2:ℝ) ^ (-(P:ℝ)))
      = (αe:ℝ) * (2:ℝ) ^ (-(b:ℝ)) + (αe:ℝ) * (2:ℝ) ^ (-(P:ℝ)) := by ring
  rw [h5]
  nlinarith

/-- Compact form of the sample budget `s 2^{-b} + (s+1) 2^{-P}` used in (3.13). -/
def sampleBudget (s b P : ℕ) : ℝ :=
  (s:ℝ) * (2:ℝ) ^ (-(b:ℝ)) + ((s:ℝ) + 1) * (2:ℝ) ^ (-(P:ℝ))

lemma sampleBudget_nonneg (s b P : ℕ) : 0 ≤ sampleBudget s b P := by
  unfold sampleBudget
  positivity

/-- When `b = P` the budget simplifies: `s 2^{-P} + (s+1) 2^{-P} = (2s+1) 2^{-P}`. -/
lemma sampleBudget_eq (s P : ℕ) :
    sampleBudget s P P = ((2 * s + 1 : ℕ) : ℝ) * (2:ℝ) ^ (-(P:ℝ)) := by
  unfold sampleBudget
  push_cast
  ring

/-! ## Effective rational samples for Lemma 3.3 -/

/-- Coercing rational floor rounding agrees with the real rounding operation. -/
lemma dyadQ_cast (P : ℕ) (y : ℚ) : (dyadQ P y : ℝ) = dyad P y := by
  simp only [dyadQ, dyad, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
  congr 1
  rw [← Rat.floor_cast (α := ℝ) (y * (2:ℚ) ^ P)]
  push_cast
  rfl

lemma abs_dyadQ_sub_le (P : ℕ) (y : ℚ) :
    |(dyadQ P y : ℝ) - y| ≤ (2:ℝ) ^ (-(P:ℝ)) := by
  rw [dyadQ_cast]
  exact abs_dyad_sub_le P y

/-- The logarithm series evaluated entirely in rational arithmetic. -/
def logSeriesQ (N : ℕ) (v : ℚ) : ℚ :=
  2 * ∑ j ∈ Finset.range N, v ^ (2 * j + 1) / (2 * (j:ℚ) + 1)

lemma logSeriesQ_cast (N : ℕ) (v : ℚ) :
    (logSeriesQ N v : ℝ) = logSeries N v := by
  simp [logSeriesQ, logSeries]

/-- Projection implemented over rationals. -/
def project12Q (y : ℚ) : ℚ := min 2 (max 1 y)

lemma project12Q_cast (y : ℚ) : (project12Q y : ℝ) = project12 y := by
  simp [project12Q, project12]

/-- Projection onto the unit interval. -/
def project01 (y : ℝ) : ℝ := min 1 (max 0 y)

def project01Q (y : ℚ) : ℚ := min 1 (max 0 y)

lemma project01Q_cast (y : ℚ) : (project01Q y : ℝ) = project01 y := by
  simp [project01Q, project01]

lemma project01_range (y : ℝ) : 0 ≤ project01 y ∧ project01 y ≤ 1 := by
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

lemma abs_project01_sub_le {y z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |project01 y - z| ≤ |y - z| := by
  unfold project01
  rcases le_total y 0 with hy | hy
  · rw [max_eq_left hy, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rw [max_eq_right hy]
    rcases le_total y 1 with hy1 | hy1
    · rw [min_eq_right hy1]
    · rw [min_eq_left hy1, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith

lemma two_neg_succ_add (P : ℕ) :
    (2:ℝ) ^ (-((P:ℝ) + 1)) + (2:ℝ) ^ (-((P:ℝ) + 1)) = (2:ℝ) ^ (-(P:ℝ)) := by
  rw [show -((P:ℝ) + 1) = -(P:ℝ) + (-1) by ring, Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  norm_num
  ring

/-- A rational logarithm approximation using `P+2` rational series terms and
`P+1` fractional bits before projection. No real arithmetic is used. -/
def logSampleQ (P : ℕ) (y : ℚ) : ℚ :=
  project01Q (dyadQ (P + 1) (logSeriesQ (P + 2) ((y - 1) / (y + 1))))

lemma logSampleQ_range (P : ℕ) (y : ℚ) :
    0 ≤ (logSampleQ P y : ℝ) ∧ (logSampleQ P y : ℝ) ≤ 1 := by
  simpa only [logSampleQ, project01Q_cast] using
    project01_range (dyadQ (P + 1) (logSeriesQ (P + 2) ((y - 1) / (y + 1))))

/-- Correctness of the finite rational logarithm algorithm on `[1,2]`. -/
theorem logSampleQ_error (P : ℕ) (y : ℚ) (hy1 : (1:ℚ) ≤ y) (hy2 : y ≤ 2) :
    |(logSampleQ P y : ℝ) - Real.log y| ≤ (2:ℝ) ^ (-(P:ℝ)) := by
  have hy1R : (1:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy1
  have hy2R : (y:ℝ) ≤ 2 := by exact_mod_cast hy2
  let v : ℚ := (y - 1) / (y + 1)
  have hv : (v:ℝ) = ((y:ℝ) - 1) / ((y:ℝ) + 1) := by simp [v]
  have ht := log_tail_le_two_neg hy1R hy2R hv P (P + 2) (by omega)
  have hnn := log_nonneg_sub_logSeries hy1R hv (P + 2)
  have hser : |(logSeriesQ (P + 2) v : ℝ) - Real.log y| ≤
      (2:ℝ) ^ (-((P:ℝ) + 1)) := by
    rw [logSeriesQ_cast, abs_of_nonpos (by linarith)]
    linarith
  have hround := abs_dyadQ_sub_le (P + 1) (logSeriesQ (P + 2) v)
  have hlogrange := Paper08.log_nonneg_le_one hy1R hy2R
  have hproj := abs_project01_sub_le (y := (dyadQ (P + 1) (logSeriesQ (P + 2) v):ℝ))
    hlogrange.1 hlogrange.2
  have htriangle := abs_sub_le (dyadQ (P + 1) (logSeriesQ (P + 2) v) : ℝ)
    (logSeriesQ (P + 2) v) (Real.log y)
  change |(project01Q (dyadQ (P + 1) (logSeriesQ (P + 2) v)) : ℝ) - Real.log y| ≤ _
  rw [project01Q_cast]
  calc
    _ ≤ |(dyadQ (P + 1) (logSeriesQ (P + 2) v) : ℝ) - Real.log y| := hproj
    _ ≤ |(dyadQ (P + 1) (logSeriesQ (P + 2) v) : ℝ) - (logSeriesQ (P + 2) v : ℝ)| +
        |(logSeriesQ (P + 2) v : ℝ) - Real.log y| := htriangle
    _ ≤ (2:ℝ) ^ (-((P:ℝ) + 1)) + (2:ℝ) ^ (-((P:ℝ) + 1)) := by
      exact add_le_add (by simpa only [Nat.cast_add, Nat.cast_one] using hround) hser
    _ = _ := two_neg_succ_add P

/-- Integer powering on `[0,1]` amplifies an absolute error by at most the exponent. -/
lemma abs_pow_sub_pow_le_on_unit {x y : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : 0 ≤ y) (hy1 : y ≤ 1) (a : ℕ) :
    |x ^ a - y ^ a| ≤ (a:ℝ) * |x - y| := by
  have hmax : max |x| |y| ≤ (1:ℝ) := by
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
    exact max_le hx1 hy1
  have hp : max |x| |y| ^ (a - 1) ≤ (1:ℝ) := by
    simpa using pow_le_pow_left₀ (le_trans (abs_nonneg x) (le_max_left _ _)) hmax (a - 1)
  calc
    _ ≤ |x - y| * (a:ℝ) * max |x| |y| ^ (a - 1) := abs_pow_sub_pow_le _ _ _
    _ ≤ |x - y| * (a:ℝ) * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- The actual rational local sample of `log Ψ ^ a`: project the oracle value,
approximate its logarithm, raise to the integer exponent, and dyadically round. -/
def primitiveSampleQ (P a : ℕ) (answer : ℚ) : ℚ :=
  dyadQ P ((logSampleQ P (project12Q answer)) ^ a)

lemma primitiveSampleQ_binary (P a : ℕ) (answer : ℚ) :
    IsBinary (primitiveSampleQ P a answer) := dyadQ_isBinary _ _

/-- Equation (3.12), with every computed sample explicitly rational. -/
theorem primitiveSampleQ_error (P b a : ℕ) (answer : ℚ) (z : ℝ)
    (hz1 : 1 ≤ z) (hz2 : z ≤ 2)
    (herr : |(answer:ℝ) - z| ≤ (2:ℝ) ^ (-(b:ℝ))) :
    |(primitiveSampleQ P a answer : ℝ) - (Real.log z) ^ a| ≤
      (a:ℝ) * ((2:ℝ) ^ (-(b:ℝ)) + (2:ℝ) ^ (-(P:ℝ))) + (2:ℝ) ^ (-(P:ℝ)) := by
  let y : ℚ := project12Q answer
  have hy1 : (1:ℚ) ≤ y := le_min (by norm_num) (le_max_left _ _)
  have hy2 : y ≤ 2 := min_le_left _ _
  have hy1R : (1:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy1
  have hpr : |(y:ℝ) - z| ≤ (2:ℝ) ^ (-(b:ℝ)) := by
    change |(project12Q answer : ℝ) - z| ≤ _
    rw [project12Q_cast]
    exact projected_query_error hz1 hz2 herr
  have hlog : |Real.log y - Real.log z| ≤ (2:ℝ) ^ (-(b:ℝ)) :=
    (Paper08.log_abs_sub_le_abs_sub hy1R hz1).trans hpr
  have hcomp : |(logSampleQ P y:ℝ) - Real.log z| ≤
      (2:ℝ) ^ (-(b:ℝ)) + (2:ℝ) ^ (-(P:ℝ)) := by
    have htriangle := abs_sub_le (logSampleQ P y:ℝ) (Real.log y) (Real.log z)
    have hs := logSampleQ_error P y hy1 hy2
    linarith
  have hsampleRange := logSampleQ_range P y
  have hlogRange := Paper08.log_nonneg_le_one hz1 hz2
  have hp := abs_pow_sub_pow_le_on_unit hsampleRange.1 hsampleRange.2 hlogRange.1 hlogRange.2 a
  have hp' := hp.trans (mul_le_mul_of_nonneg_left hcomp (Nat.cast_nonneg a))
  have hr := abs_dyadQ_sub_le P ((logSampleQ P y) ^ a)
  push_cast only [Rat.cast_pow] at hr
  have htriangle := abs_sub_le (dyadQ P ((logSampleQ P y) ^ a):ℝ)
    ((logSampleQ P y:ℝ) ^ a) ((Real.log z) ^ a)
  change |(dyadQ P ((logSampleQ P y) ^ a):ℝ) - (Real.log z) ^ a| ≤ _
  linarith

/-- Uniform version of the actual sample guarantee, using the moment order `s`. -/
theorem primitiveSampleQ_error_le_budget (P b a s : ℕ) (answer : ℚ) (z : ℝ)
    (ha : 1 ≤ a) (has : a ≤ s) (hz1 : 1 ≤ z) (hz2 : z ≤ 2)
    (herr : |(answer:ℝ) - z| ≤ (2:ℝ) ^ (-(b:ℝ))) :
    |(primitiveSampleQ P a answer : ℝ) - (Real.log z) ^ a| ≤ sampleBudget s b P :=
  (primitiveSampleQ_error P b a answer z hz1 hz2 herr).trans (sample_error_nat ha has b P)

/-- Dyadic floor rounding preserves the unit interval. -/
lemma dyadQ_range {P : ℕ} {y : ℚ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ dyadQ P y ∧ dyadQ P y ≤ 1 := by
  have hpos : (0:ℚ) < (2:ℚ) ^ P := by positivity
  constructor
  · exact div_nonneg (Int.cast_nonneg.mpr (Int.floor_nonneg.mpr (mul_nonneg hy0 hpos.le))) hpos.le
  · apply le_trans _ hy1
    rw [dyadQ, div_le_iff₀ hpos]
    exact Int.floor_le _

lemma primitiveSampleQ_range (P a : ℕ) (answer : ℚ) :
    0 ≤ primitiveSampleQ P a answer ∧ primitiveSampleQ P a answer ≤ 1 := by
  have hs := logSampleQ_range P (project12Q answer)
  have hs0 : (0:ℚ) ≤ logSampleQ P (project12Q answer) := by exact_mod_cast hs.1
  have hs1 : logSampleQ P (project12Q answer) ≤ 1 := by exact_mod_cast hs.2
  exact dyadQ_range (pow_nonneg hs0 a) (by simpa using pow_le_pow_left₀ hs0 hs1 a)

/-- A dyadic error budget in rational arithmetic. -/
def sampleBudgetQ (s P : ℕ) : ℚ := ((2 * s + 1 : ℕ):ℚ) / (2:ℚ) ^ P

lemma sampleBudgetQ_cast (s P : ℕ) : (sampleBudgetQ s P : ℝ) = sampleBudget s P P := by
  rw [sampleBudget_eq]
  simp only [sampleBudgetQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
  rfl

/-- The least binary precision up to the compulsory lower bound `P ≥ 1`.
`Nat.clog` and rational ceiling are computable integer operations. -/
def samplePrecision (s : ℕ) (ζ : ℚ) : ℕ :=
  max 1 (Nat.clog 2 ⌈((2 * s + 1 : ℕ):ℚ) / ζ⌉₊)

lemma samplePrecision_pos (s : ℕ) (ζ : ℚ) : 1 ≤ samplePrecision s ζ := le_max_left _ _

/-- The computed precision passes the rational comparison in (3.13). -/
theorem samplePrecision_sufficient (s : ℕ) (ζ : ℚ) (hζ : 0 < ζ) :
    sampleBudgetQ s (samplePrecision s ζ) ≤ ζ := by
  have hceil : ((2 * s + 1 : ℕ):ℚ) / ζ ≤ (⌈((2 * s + 1 : ℕ):ℚ) / ζ⌉₊:ℚ) := Nat.le_ceil _
  have hlog : ⌈((2 * s + 1 : ℕ):ℚ) / ζ⌉₊ ≤ 2 ^ samplePrecision s ζ := by
    exact (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp (le_max_right _ _)
  have hp : ((2 * s + 1 : ℕ):ℚ) / ζ ≤ (2:ℚ) ^ samplePrecision s ζ :=
    hceil.trans (by exact_mod_cast hlog)
  have hm : ((2 * s + 1 : ℕ):ℚ) ≤ (2:ℚ) ^ samplePrecision s ζ * ζ :=
    (div_le_iff₀ hζ).mp hp
  unfold sampleBudgetQ
  exact (div_le_iff₀ (by positivity : (0:ℚ) < 2 ^ samplePrecision s ζ)).mpr (by nlinarith)

/-- A candidate precision passing the same rational comparison bounds the chosen precision. -/
theorem samplePrecision_le (s : ℕ) (ζ : ℚ) (hζ : 0 < ζ) (P : ℕ) (hP : 1 ≤ P)
    (hbudget : sampleBudgetQ s P ≤ ζ) : samplePrecision s ζ ≤ P := by
  rw [samplePrecision, max_le_iff]
  refine ⟨hP, (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr ?_⟩
  rw [Nat.ceil_le]
  have hm : ((2 * s + 1 : ℕ):ℚ) ≤ ζ * (2:ℚ) ^ P :=
    (div_le_iff₀ (by positivity : (0:ℚ) < 2 ^ P)).mp hbudget
  have hp : ((2 * s + 1 : ℕ):ℚ) / ζ ≤ (2:ℚ) ^ P :=
    (div_le_iff₀ hζ).mpr (by nlinarith)
  exact_mod_cast hp

/-- The precision selected by rational arithmetic gives the real sample guarantee. -/
theorem primitiveSampleQ_chosen_precision_error {k s : ℕ} {Ψ : (Fin k → ℝ) → ℝ}
    (O : Oracle k Ψ) (x : Fin k → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (a : ℕ) (ha : 1 ≤ a) (has : a ≤ s) (ζ : ℚ) (hζ : 0 < ζ)
    (hΨ1 : 1 ≤ Ψ (fun i => (x i:ℝ))) (hΨ2 : Ψ (fun i => (x i:ℝ)) ≤ 2) :
    let P := samplePrecision s ζ
    |(primitiveSampleQ P a (O.query x P):ℝ) - (Real.log (Ψ (fun i => (x i:ℝ)))) ^ a| ≤ ζ := by
  dsimp only
  have herr := primitiveSampleQ_error_le_budget (samplePrecision s ζ) (samplePrecision s ζ) a s
    (O.query x (samplePrecision s ζ)) (Ψ (fun i => (x i:ℝ))) ha has hΨ1 hΨ2
    (O.query_approx x _ hx (samplePrecision_pos s ζ))
  have hbudget := samplePrecision_sufficient s ζ hζ
  have hbudgetR : sampleBudget s (samplePrecision s ζ) (samplePrecision s ζ) ≤ (ζ:ℝ) := by
    rw [← sampleBudgetQ_cast]
    exact_mod_cast hbudget
  exact herr.trans hbudgetR

/-- The common total level from (3.11), computed with rational arithmetic and
the upper integer binary logarithm. -/
def totalLevelChoice (s C : ℕ) (τ : ℚ) : ℕ :=
  Nat.clog 2 ⌈(2 * ((4 * C : ℕ):ℚ) ^ s / τ) ^ 2⌉₊

lemma totalLevelChoice_pow (s C : ℕ) (τ : ℚ) :
    (2 * ((4 * C : ℕ):ℚ) ^ s / τ) ^ 2 ≤ (2:ℚ) ^ totalLevelChoice s C τ := by
  have hc := Nat.le_ceil ((2 * ((4 * C : ℕ):ℚ) ^ s / τ) ^ 2)
  have hl : ⌈(2 * ((4 * C : ℕ):ℚ) ^ s / τ) ^ 2⌉₊ ≤ 2 ^ totalLevelChoice s C τ := by
    exact Nat.le_pow_clog (by decide : 1 < 2) _
  exact hc.trans (by exact_mod_cast hl)

/-- Minimality of the level choice: any level passing the rational test bounds it. -/
lemma totalLevelChoice_le (s C J : ℕ) (τ : ℚ)
    (hJ : (2 * ((4 * C : ℕ):ℚ) ^ s / τ) ^ 2 ≤ (2:ℚ) ^ J) :
    totalLevelChoice s C τ ≤ J := by
  rw [totalLevelChoice, Nat.clog_le_iff_le_pow (by decide : 1 < 2), Nat.ceil_le]
  exact_mod_cast hJ

/-- The effective level passes the exact-sample truncation bound in (3.5). -/
theorem totalLevelChoice_error (s C t : ℕ) (τ : ℚ) (hτ : 0 < τ)
    (hC : 1 ≤ C) (ht : t ≤ s) :
    (C:ℝ) ^ s * C0 ^ t * (2:ℝ) ^ (-(totalLevelChoice s C τ:ℝ) / 2) ≤ (τ:ℝ) / 2 := by
  let J := totalLevelChoice s C τ
  have hτR : (0:ℝ) < τ := by exact_mod_cast hτ
  have hCJ : (0:ℝ) < (C:ℝ) := by exact_mod_cast hC
  have hpowR : (2 * ((4 * C : ℕ):ℝ) ^ s / (τ:ℝ)) ^ 2 ≤ (2:ℝ) ^ J := by
    exact_mod_cast totalLevelChoice_pow s C τ
  have hhalf : ((2:ℝ) ^ ((J:ℝ) / 2)) ^ 2 = (2:ℝ) ^ J := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    have he : (J:ℝ) / 2 * (2:ℝ) = J := by ring
    norm_num only [Nat.cast_ofNat]
    rw [he, Real.rpow_natCast]
  have hroot : 2 * ((4 * C : ℕ):ℝ) ^ s / (τ:ℝ) ≤ (2:ℝ) ^ ((J:ℝ) / 2) := by
    rw [← hhalf] at hpowR
    have hn : (0:ℝ) ≤ (2:ℝ) ^ ((J:ℝ) / 2) := by positivity
    nlinarith
  have hC0 : C0 ^ t ≤ (4:ℝ) ^ s := by
    calc
      C0 ^ t ≤ (4:ℝ) ^ t := pow_le_pow_left₀ C0_pos.le C0_lt_four.le t
      _ ≤ (4:ℝ) ^ s := pow_le_pow_right₀ (by norm_num) ht
  have hB : (C:ℝ) ^ s * C0 ^ t ≤ ((4 * C : ℕ):ℝ) ^ s := by
    have hh := mul_le_mul_of_nonneg_left hC0 (pow_nonneg hCJ.le s)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_pow, mul_comm] using hh
  have hproduct : 2 * ((4 * C : ℕ):ℝ) ^ s ≤ (2:ℝ) ^ ((J:ℝ) / 2) * (τ:ℝ) :=
    (div_le_iff₀ hτR).mp hroot
  have hhalfpos : (0:ℝ) < (2:ℝ) ^ ((J:ℝ) / 2) := by positivity
  have hinv : (2:ℝ) ^ (-(J:ℝ) / 2) = ((2:ℝ) ^ ((J:ℝ) / 2))⁻¹ := by
    rw [show -(J:ℝ) / 2 = -((J:ℝ) / 2) by ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  change (C:ℝ) ^ s * C0 ^ t * (2:ℝ) ^ (-(J:ℝ) / 2) ≤ _
  rw [hinv, ← div_eq_mul_inv, div_le_iff₀ hhalfpos]
  nlinarith

/-- The uniform rational sample tolerance in (3.13). -/
def primitiveSampleTol (s J C : ℕ) (τ : ℚ) : ℚ :=
  min (1 / (2 * ((J:ℚ) + 1))) (τ / (4 * s * ((J:ℚ) + 1) * 3 ^ (s - 1) * (C:ℚ) ^ s))

lemma primitiveSampleTol_pos {s J C : ℕ} {τ : ℚ} (hs : 1 ≤ s) (hC : 1 ≤ C) (hτ : 0 < τ) :
    0 < primitiveSampleTol s J C τ := by
  have hsR : (0:ℚ) < s := by exact_mod_cast hs
  have hCR : (0:ℚ) < C := by exact_mod_cast hC
  exact lt_min (by positivity) (by positivity)

lemma primitiveSampleTol_hyp (s J C : ℕ) (τ : ℚ) :
    2 * ((J:ℚ) + 1) * primitiveSampleTol s J C τ ≤ 1 := by
  have hh : primitiveSampleTol s J C τ ≤ 1 / (2 * ((J:ℚ) + 1)) := min_le_left _ _
  have hp : (0:ℚ) < 2 * ((J:ℚ) + 1) := by positivity
  have hm := (le_div_iff₀ hp).mp hh
  nlinarith

/-- The sample tolerance pays for the perturbation bound, with `t ≤ s`. -/
lemma primitiveSampleTol_error {s J C t : ℕ} {τ : ℚ} (hs : 1 ≤ s) (hC : 1 ≤ C)
    (hτ : 0 < τ) (ht : t ≤ s) :
    2 * (t:ℚ) * ((J:ℚ) + 1) * 3 ^ (t - 1) * (C:ℚ) ^ s * primitiveSampleTol s J C τ ≤ τ / 2 := by
  have hsR : (0:ℚ) < s := by exact_mod_cast hs
  have hCR : (0:ℚ) < C := by exact_mod_cast hC
  have htol : primitiveSampleTol s J C τ ≤ τ / (4 * s * ((J:ℚ) + 1) * 3 ^ (s - 1) * (C:ℚ) ^ s) := min_le_right _ _
  have hden : (0:ℚ) < 4 * s * ((J:ℚ) + 1) * 3 ^ (s - 1) * (C:ℚ) ^ s := by positivity
  have hm := (le_div_iff₀ hden).mp htol
  have htR : (t:ℚ) ≤ s := by exact_mod_cast ht
  have hp : (3:ℚ) ^ (t - 1) ≤ 3 ^ (s - 1) := pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right ht 1)
  have htpos := primitiveSampleTol_pos (J := J) hs hC hτ
  have hbound : (t:ℚ) * 3 ^ (t - 1) ≤ s * (3:ℚ) ^ (s - 1) :=
    mul_le_mul htR hp (by positivity) hsR.le
  have hh := mul_le_mul_of_nonneg_right hbound
    (show 0 ≤ 2 * ((J:ℚ) + 1) * (C:ℚ) ^ s * primitiveSampleTol s J C τ by positivity)
  nlinarith

/-- The weak-interaction promise implies the fixed range needed for rational
logarithm evaluation. -/
lemma weak_q_lt_third {r c : ℕ} {q σ : ℝ} (hr : 2 ≤ r) (hc : 1 ≤ c)
    (hq : 0 < q) (hσ : 0 < σ)
    (hweak : 3 * (c:ℝ) * Real.sqrt ((r:ℝ) - 1) * q ≤ 1 - σ) : q < 1 / 3 := by
  have hrR : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hcR : (1:ℝ) ≤ c := by exact_mod_cast hc
  have hsqrt : (1:ℝ) ≤ Real.sqrt ((r:ℝ) - 1) := by
    have hh := Real.sqrt_le_sqrt (show (1:ℝ) ≤ (r:ℝ) - 1 by linarith)
    simpa using hh
  have hprod : (1:ℝ) ≤ (c:ℝ) * Real.sqrt ((r:ℝ) - 1) := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hprod hq.le
  nlinarith

lemma exp_lt_two_of_q_lt_third {q : ℝ} (hq : q < 1 / 3) : Real.exp q < 2 := by
  have hlog : q < Real.log 2 := by linarith [Real.log_two_gt_d9]
  calc
    Real.exp q < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hlog
    _ = 2 := Real.exp_log (by norm_num)

lemma log_factor_range {z q : ℝ} (hz1 : 1 ≤ z) (hzq : z ≤ Real.exp q) :
    0 ≤ Real.log z ∧ Real.log z ≤ q := by
  refine ⟨Real.log_nonneg hz1, ?_⟩
  have hz : 0 < z := by linarith
  simpa using (Real.log_le_log hz hzq)

/-- The sup norm and Lipschitz estimates for each primitive factor, equation (3.8). -/
theorem log_power_bounds {z w q K d : ℝ} (a : ℕ) (hq : 0 ≤ q)
    (hz1 : 1 ≤ z) (hzq : z ≤ Real.exp q) (hw1 : 1 ≤ w) (hwq : w ≤ Real.exp q)
    (hd : 0 ≤ d) (hK : 0 ≤ K) (herr : |z - w| ≤ K * d) :
    |(Real.log z) ^ a| ≤ q ^ a ∧
    |(Real.log z) ^ a - (Real.log w) ^ a| ≤ (a:ℝ) * K * q ^ (a - 1) * d := by
  have hzr := log_factor_range hz1 hzq
  have hwr := log_factor_range hw1 hwq
  constructor
  · rw [abs_of_nonneg (pow_nonneg hzr.1 a)]
    exact pow_le_pow_left₀ hzr.1 hzr.2 a
  · have hlog : |Real.log z - Real.log w| ≤ K * d :=
      (Paper08.log_abs_sub_le_abs_sub hz1 hw1).trans herr
    have hm : max |Real.log z| |Real.log w| ≤ q := by
      rw [abs_of_nonneg hzr.1, abs_of_nonneg hwr.1]
      exact max_le hzr.2 hwr.2
    have hp : max |Real.log z| |Real.log w| ^ (a - 1) ≤ q ^ (a - 1) :=
      pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hm _
    calc
      _ ≤ |Real.log z - Real.log w| * (a:ℝ) * max |Real.log z| |Real.log w| ^ (a - 1) :=
        abs_pow_sub_pow_le _ _ _
      _ ≤ (K * d) * (a:ℝ) * q ^ (a - 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg a)) hp
          (by positivity) (by positivity)
      _ = _ := by ring

/-- Per-factor quadrature budget for a primitive exponent. -/
def primitiveFactorBudget (q A : ℝ) (a : ℕ) : ℝ :=
  max 1 (max (q ^ a) (A * (a:ℝ) * q ^ (a - 1)))

/-- Charging a local budget to its own exponent, the first bound in (3.9). -/
theorem primitiveFactorBudget_le {q A C : ℝ} (hq : 0 ≤ q) (hA : 0 ≤ A)
    (hC : 2 ≤ C) (hqC : 2 * q ≤ C) (hAC : 2 * A ≤ C) (a : ℕ) :
    primitiveFactorBudget q A a ≤ C ^ a := by
  have hC0 : 0 ≤ C := by linarith
  have hC1 : 1 ≤ C := by linarith
  have hhalf : 0 ≤ C / 2 := by positivity
  have hqhalf : q ≤ C / 2 := by linarith
  have hAhalf : A ≤ C / 2 := by linarith
  rw [primitiveFactorBudget, max_le_iff, max_le_iff]
  refine ⟨one_le_pow₀ hC1, pow_le_pow_left₀ hq (by linarith) a, ?_⟩
  by_cases ha : a = 0
  · subst a
    simp
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    have hexp : a - 1 + 1 = a := Nat.sub_add_cancel ha1
    have hp : q ^ (a - 1) ≤ (C / 2) ^ (a - 1) := pow_le_pow_left₀ hq hqhalf _
    have hh : A * (a:ℝ) * q ^ (a - 1) ≤ (C / 2) * (a:ℝ) * (C / 2) ^ (a - 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hAhalf (Nat.cast_nonneg a)) hp
        (pow_nonneg hq _) (mul_nonneg hhalf (Nat.cast_nonneg a))
    have heq : (C / 2) * (a:ℝ) * (C / 2) ^ (a - 1) = (a:ℝ) * (C / 2) ^ a := by
      calc
        _ = (a:ℝ) * ((C / 2) ^ (a - 1) * (C / 2)) := by ring
        _ = (a:ℝ) * (C / 2) ^ (a - 1 + 1) := by rw [pow_succ]
        _ = _ := by rw [hexp]
    rw [heq] at hh
    calc
      _ ≤ (a:ℝ) * (C / 2) ^ a := hh
      _ ≤ (2:ℝ) ^ a * (C / 2) ^ a :=
        mul_le_mul_of_nonneg_right (Paper08.nat_le_two_pow a) (pow_nonneg hhalf a)
      _ = C ^ a := by rw [← mul_pow]; congr 1; ring

/-- Combined primitive budget depends on total order, the second bound in (3.9). -/
theorem primitiveFactorBudget_prod_le {ι : Type*} [Fintype ι] (α : ι → ℕ)
    {q A C : ℝ} (hq : 0 ≤ q) (hA : 0 ≤ A) (hC : 2 ≤ C)
    (hqC : 2 * q ≤ C) (hAC : 2 * A ≤ C) {s : ℕ} (hα : ∑ i, α i ≤ s) :
    ∏ i, primitiveFactorBudget q A (α i) ≤ C ^ s := by
  calc
    _ ≤ ∏ i, C ^ α i := Finset.prod_le_prod
      (fun i _ => le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left _ _))
      (fun i _ => primitiveFactorBudget_le hq hA hC hqC hAC (α i))
    _ = C ^ (∑ i, α i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ C ^ s := pow_le_pow_right₀ (by linarith) hα

/-! ## Exact common dyadic denominators for the primitive quadrature -/

/-- A rational with at most `P` fractional binary digits. -/
def IsDyadicAt (P : ℕ) (y : ℚ) : Prop := ∃ m : ℤ, y = m / (2:ℚ) ^ P

lemma dyadQ_isDyadicAt (P : ℕ) (y : ℚ) : IsDyadicAt P (dyadQ P y) :=
  ⟨_, rfl⟩

lemma primitiveSampleQ_isDyadicAt (P a : ℕ) (answer : ℚ) :
    IsDyadicAt P (primitiveSampleQ P a answer) := dyadQ_isDyadicAt _ _

lemma isDyadicAt_zero (P : ℕ) : IsDyadicAt P 0 := ⟨0, by simp⟩

lemma isDyadicAt_one (P : ℕ) : IsDyadicAt P 1 := by
  refine ⟨2 ^ P, ?_⟩
  norm_num

lemma IsDyadicAt.add {P : ℕ} {x y : ℚ} (hx : IsDyadicAt P x) (hy : IsDyadicAt P y) :
    IsDyadicAt P (x + y) := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  refine ⟨m + n, ?_⟩
  push_cast
  ring

lemma IsDyadicAt.neg {P : ℕ} {x : ℚ} (hx : IsDyadicAt P x) : IsDyadicAt P (-x) := by
  obtain ⟨m, rfl⟩ := hx
  refine ⟨-m, ?_⟩
  push_cast
  ring

lemma IsDyadicAt.sub {P : ℕ} {x y : ℚ} (hx : IsDyadicAt P x) (hy : IsDyadicAt P y) :
    IsDyadicAt P (x - y) := by simpa only [sub_eq_add_neg] using hx.add hy.neg

lemma IsDyadicAt.mul {P Q : ℕ} {x y : ℚ} (hx : IsDyadicAt P x) (hy : IsDyadicAt Q y) :
    IsDyadicAt (P + Q) (x * y) := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  refine ⟨m * n, ?_⟩
  push_cast
  rw [pow_add]
  ring

lemma IsDyadicAt.mono {P Q : ℕ} {x : ℚ} (hx : IsDyadicAt P x) (hPQ : P ≤ Q) :
    IsDyadicAt Q x := by
  obtain ⟨m, rfl⟩ := hx
  refine ⟨m * 2 ^ (Q - P), ?_⟩
  have hQ : Q = P + (Q - P) := (Nat.add_sub_of_le hPQ).symm
  have hpow : (2:ℚ) ^ Q = (2:ℚ) ^ P * (2:ℚ) ^ (Q - P) := by
    calc
      _ = (2:ℚ) ^ (P + (Q - P)) := congrArg (fun n : ℕ => (2:ℚ) ^ n) hQ
      _ = _ := pow_add _ _ _
  rw [hpow]
  push_cast
  field_simp

lemma IsDyadicAt.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (P : ℕ)
    (hf : ∀ i ∈ s, IsDyadicAt P (f i)) : IsDyadicAt P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [isDyadicAt_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma IsDyadicAt.prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (P : ℕ)
    (hf : ∀ i ∈ s, IsDyadicAt P (f i)) : IsDyadicAt (P * s.card) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isDyadicAt_one 0
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have hh := (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    convert hh using 1 <;> ring

lemma isDyadicAt_inv_two_pow (P : ℕ) : IsDyadicAt P ((2:ℚ) ^ P)⁻¹ := by
  exact ⟨1, by simp⟩

lemma IsDyadicAt.div_two_pow {P Q : ℕ} {x : ℚ} (hx : IsDyadicAt P x) :
    IsDyadicAt (P + Q) (x / (2:ℚ) ^ Q) := by
  simpa only [div_eq_mul_inv] using hx.mul (isDyadicAt_inv_two_pow Q)

/-- All signed primitive cell terms have a common denominator. This applies
when each factor increment has precision `P` and each cell level is at most `R`. -/
theorem common_dyadic_cell_sum {κ ι : Type*} (T : Finset κ) (s : Finset ι)
    (values : κ → ι → ℚ) (levels : κ → ℕ) (P R : ℕ)
    (hvalues : ∀ k ∈ T, ∀ i ∈ s, IsDyadicAt P (values k i))
    (hlevels : ∀ k ∈ T, levels k ≤ R) :
    IsDyadicAt (P * s.card + R)
      (∑ k ∈ T, (∏ i ∈ s, values k i) / (2:ℚ) ^ levels k) := by
  refine IsDyadicAt.sum T _ _ ?_
  intro k hk
  exact ((IsDyadicAt.prod s _ P (hvalues k hk)).div_two_pow).mono (Nat.add_le_add_left (hlevels k hk) _)

/-- In reduced rational form, the denominator divides the common dyadic denominator. -/
lemma IsDyadicAt.den_dvd {P : ℕ} {x : ℚ} (hx : IsDyadicAt P x) : x.den ∣ 2 ^ P := by
  obtain ⟨m, rfl⟩ := hx
  have hd := Rat.den_dvd m ((2:ℤ) ^ P)
  have he : m / (2:ℚ) ^ P = Rat.divInt m ((2:ℤ) ^ P) := by
    rw [Rat.divInt_eq_div]
    norm_cast
  rw [← he] at hd
  exact_mod_cast hd

end Oracle
end Paper08
