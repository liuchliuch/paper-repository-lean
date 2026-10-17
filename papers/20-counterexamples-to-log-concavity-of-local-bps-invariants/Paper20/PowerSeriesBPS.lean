import Paper20.Semantics

/-! The coefficient-level local BPS definition is exactly the formal power
series identity (24), obtained from (1) by `w=(1-q)^2/q`. This establishes
its semantic content without building a certificate into the definition. -/
namespace Paper20.Semantics
open Finset BigOperators

/-- The Hilbert series, with the genuine integer coefficients as input. -/
def hilbertSeries (H : ℕ → ℤ) : PowerSeries ℤ := PowerSeries.mk H

/-- The right side of (24), as an actual formal power series. -/
noncomputable def bpsSeries (d : ℕ) (n : ℕ → ℤ) : PowerSeries ℤ :=
  ∑ j ∈ range (d+1), PowerSeries.C (n j) *
    (PowerSeries.X^(d-j) * (1-PowerSeries.X)^(2*j))

lemma coeff_one_sub_X_pow (b ℓ : ℕ) :
    PowerSeries.coeff ℓ ((1-PowerSeries.X)^b : PowerSeries ℤ) =
      (-1 : ℤ)^ℓ * (Nat.choose b ℓ : ℤ) := by
  induction b generalizing ℓ with
  | zero =>
    cases ℓ with
    | zero => simp
    | succ ℓ => simp [PowerSeries.coeff_one]
  | succ b ih =>
    have he : ((1-PowerSeries.X)^(b+1) : PowerSeries ℤ) =
        (1-PowerSeries.X)^b - (1-PowerSeries.X)^b * PowerSeries.X := by
      rw [pow_succ, mul_sub, mul_one]
    rw [he, map_sub]
    cases ℓ with
    | zero => simp [ih]
    | succ ℓ =>
      rw [PowerSeries.coeff_succ_mul_X, ih, ih, Nat.choose_succ_succ]
      push_cast
      rw [pow_succ]
      ring

/-- The left side really is multiplication of the Hilbert series by `(1-q)^b`. -/
theorem coeff_hilbert_residual (b ℓ : ℕ) (H : ℕ → ℤ) :
    PowerSeries.coeff ℓ ((1-PowerSeries.X)^b * hilbertSeries H) =
      hilbertResidual b H ℓ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_one_sub_X_pow, hilbertSeries, PowerSeries.coeff_mk, hilbertResidual]

/-- The right side has precisely the binomial coefficient expansion used above. -/
theorem coeff_bpsSeries (d ℓ : ℕ) (n : ℕ → ℤ) :
    PowerSeries.coeff ℓ (bpsSeries d n) = expansionCoeff d n ℓ := by
  unfold bpsSeries expansionCoeff
  rw [map_sum]
  apply sum_congr rfl
  intro j hj
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_one_sub_X_pow]
    ring
  · simp

/-- Exact equivalence with the original local BPS expansion after clearing
negative powers: equality in `ℤ⟦q⟧`, not a certificate-specific predicate. -/
theorem localBPSExpansion_iff_series (b d : ℕ) (H n : ℕ → ℤ) :
    localBPSExpansion b d H n ↔
      (1-PowerSeries.X)^b * hilbertSeries H = bpsSeries d n := by
  constructor
  · intro h
    apply PowerSeries.ext
    intro ℓ
    rw [coeff_hilbert_residual, coeff_bpsSeries]
    exact h ℓ
  · intro h ℓ
    have hc := congrArg (PowerSeries.coeff ℓ) h
    simpa only [coeff_hilbert_residual, coeff_bpsSeries] using hc

end Paper20.Semantics
