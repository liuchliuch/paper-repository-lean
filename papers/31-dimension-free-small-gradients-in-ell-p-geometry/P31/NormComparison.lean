import P31.NormTargets
import Mathlib.Analysis.MeanInequalities

/-! Sharp finite-dimensional stronger-norm conversion, including the exact
factor used for finite support and rectangular Schatten singular values. -/
noncomputable section
open scoped BigOperators
namespace P31
variable {ι : Type*} [Fintype ι]

theorem lpNorm_dimension_comparison {s q : ℝ} (hs : 0 < s) (hsq : s ≤ q)
    (v : ι → ℝ) :
    lpNorm s v ≤ (Fintype.card ι : ℝ)^(1/s-1/q) * lpNorm q v := by
  have hq : 0 < q := lt_of_lt_of_le hs hsq
  have hr : 1 ≤ q/s := (le_div_iff₀ hs).2 (by simpa using hsq)
  have hraw := Real.rpow_sum_le_const_mul_sum_rpow Finset.univ
    (fun i => |v i|^s) hr
  have hpow (i : ι) : (|v i|^s)^(q/s) = |v i|^q := by
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    field_simp
  have hraw' : lpPower s v ^ (q/s) ≤
      (Fintype.card ι : ℝ)^(q/s-1) * lpPower q v := by
    simpa only [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      Finset.card_univ, hpow] using hraw
  have h := Real.rpow_le_rpow (Real.rpow_nonneg (lpPower_nonneg _ _) _) hraw'
    (one_div_nonneg.mpr hq.le)
  rw [← Real.rpow_mul (lpPower_nonneg _ _),
    Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (lpPower_nonneg _ _),
    ← Real.rpow_mul (Nat.cast_nonneg _)] at h
  have hleft : q/s*(1/q) = 1/s := by field_simp
  have hright : (q/s-1)*(1/q) = 1/s-1/q := by field_simp
  rw [hleft, hright] at h
  exact h

/-- The dimension factor is attained by the literal flat vector from §5. -/
theorem lpNorm_dimension_factor_sharp (d : ℕ) (hd : 0 < d) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) :
    lpNorm s (normalizedFlatVector d q) =
      (d:ℝ)^(1/s-1/q) * lpNorm q (normalizedFlatVector d q) := by
  rw [normalizedFlatVector_norm d hd hs, normalizedFlatVector_unit_norm d hd hq, mul_one]

/-- The paired finite-support comparisons in §7.3, with genuine ℓₚ/ℓ₂/ℓ_q norms. -/
theorem finite_support_hilbert_comparisons {p : ℝ} (hp : 2 ≤ p) (v g : ι → ℝ) :
    lpNorm p v ≤ lpNorm 2 v ∧
    lpNorm 2 v ≤ (Fintype.card ι : ℝ)^(1/2-1/p) * lpNorm p v ∧
    lpNorm 2 g ≤ lpNorm (dualExponent p) g ∧
    lpNorm (dualExponent p) g ≤ (Fintype.card ι : ℝ)^(1/2-1/p) * lpNorm 2 g := by
  have hp1 : 1 < p := by linarith
  have hq : 0 < dualExponent p := dualExponent_pos hp1
  have hq2 : dualExponent p ≤ 2 := by
    unfold dualExponent
    apply (div_le_iff₀ (by linarith : 0 < p-1)).2
    linarith
  have hexp : 1/dualExponent p-1/2 = 1/2-1/p := by
    unfold dualExponent
    field_simp; ring
  refine ⟨lpNorm_antitone_exponent (by norm_num) hp v,
    lpNorm_dimension_comparison (by norm_num) hp v,
    lpNorm_antitone_exponent hq hq2 g, ?_⟩
  simpa only [hexp] using lpNorm_dimension_comparison hq hq2 g

end P31
