import P31.PowerGeometry

/-!
# Finite-dimensional target norms (Remark 5.1)

Both monotonicity and the dimension-dependent flat-vector example are proved
for the actual finite-coordinate ℓₚ norm.
-/

noncomputable section
open scoped BigOperators

namespace P31

variable {ι : Type*} [Fintype ι]

/-- Each absolute coordinate is bounded by the finite ℓₚ norm. -/
theorem abs_coordinate_le_lpNorm {p : ℝ} (hp : 0 < p) (v : ι → ℝ) (i : ι) :
    |v i| ≤ lpNorm p v := by
  apply (Real.rpow_le_rpow_iff (abs_nonneg _) (lpNorm_nonneg p v) hp).mp
  rw [lpNorm_rpow p hp]
  exact Finset.single_le_sum (fun j _ ↦ Real.rpow_nonneg (abs_nonneg (v j)) p)
    (Finset.mem_univ i)

/-- Norm monotonicity on counting measure: every exponent `s ≥ q > 0`
gives a weaker target.  This covers the first assertion of Remark 5.1. -/
theorem lpNorm_antitone_exponent {q s : ℝ} (hq : 0 < q) (hqs : q ≤ s)
    (v : ι → ℝ) : lpNorm s v ≤ lpNorm q v := by
  have hs : 0 < s := lt_of_lt_of_le hq hqs
  by_cases hn : lpNorm q v = 0
  · have hv : v = 0 := by
      ext i
      exact abs_nonpos_iff.mp (by simpa [hn] using abs_coordinate_le_lpNorm hq v i)
    simp [hv, lpNorm, lpPower, Real.zero_rpow hq.ne', Real.zero_rpow hs.ne', hq.ne', hs.ne']
  · have hnpos : 0 < lpNorm q v := lt_of_le_of_ne (lpNorm_nonneg q v) (Ne.symm hn)
    have hnormsum : (∑ i, (|v i| / lpNorm q v) ^ q) = 1 := by
      simp_rw [Real.div_rpow (abs_nonneg _) (lpNorm_nonneg q v)]
      rw [← Finset.sum_div, ← lpPower, ← lpNorm_rpow q hq]
      exact div_self (ne_of_gt (Real.rpow_pos_of_pos hnpos q))
    have hsum : (∑ i, (|v i| / lpNorm q v) ^ s) ≤ 1 := by
      rw [← hnormsum]
      apply Finset.sum_le_sum
      intro i _
      apply Real.rpow_le_rpow_of_exponent_ge' (div_nonneg (abs_nonneg _) hnpos.le) _ hq.le hqs
      exact (div_le_one hnpos).mpr (abs_coordinate_le_lpNorm hq v i)
    have hsum' : lpPower s v / lpNorm q v ^ s ≤ 1 := by
      simpa only [Real.div_rpow (abs_nonneg _) (lpNorm_nonneg q v), ← Finset.sum_div,
        lpPower] using hsum
    have hpowers : lpPower s v ≤ lpNorm q v ^ s :=
      (div_le_one (Real.rpow_pos_of_pos hnpos s)).mp hsum'
    apply (Real.rpow_le_rpow_iff (lpNorm_nonneg s v) (lpNorm_nonneg q v) hs).mp
    simpa only [lpNorm_rpow s hs] using hpowers

/-- The norm of a constant `d`-coordinate real vector. -/
theorem lpNorm_constant (d : ℕ) {p : ℝ} (hp : 0 < p) (a : ℝ) :
    lpNorm p (fun _ : Fin d ↦ a) = (d : ℝ) ^ (1 / p) * |a| := by
  simp only [lpNorm, lpPower, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg d) (Real.rpow_nonneg (abs_nonneg a) p),
    ← Real.rpow_mul (abs_nonneg a), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The flat vector used in the second assertion of Remark 5.1. -/
def normalizedFlatVector (d : ℕ) (q : ℝ) : Fin d → ℝ :=
  fun _ ↦ (d : ℝ) ^ (-(1 / q))

/-- Its ℓ_s norm contains exactly the dimension factor displayed in the paper.
The formula holds for all positive finite exponents. -/
theorem normalizedFlatVector_norm (d : ℕ) (hd : 0 < d) {q s : ℝ}
    (hs : 0 < s) :
    lpNorm s (normalizedFlatVector d q) = (d : ℝ) ^ (1 / s - 1 / q) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  unfold normalizedFlatVector
  rw [lpNorm_constant d hs,
    abs_of_pos (Real.rpow_pos_of_pos hdpos _), ← Real.rpow_add hdpos] <;> congr 1

/-- In particular the input vector has unit ℓ_q norm. -/
theorem normalizedFlatVector_unit_norm (d : ℕ) (hd : 0 < d) {q : ℝ}
    (hq : 0 < q) : lpNorm q (normalizedFlatVector d q) = 1 := by
  rw [normalizedFlatVector_norm d hd hq, sub_self, Real.rpow_zero]

/-- For the stronger target `s < q`, the dimension exponent is positive. -/
theorem stronger_target_dimension_exponent_pos {q s : ℝ}
    (hs : 0 < s) (hsq : s < q) : 0 < 1 / s - 1 / q := by
  have hq : 0 < q := lt_trans hs hsq
  exact sub_pos.mpr ((one_div_lt_one_div hq hs).mpr hsq)

/-- No constant independent of dimension converts the weaker ℓ_q norm to
an ℓ_s norm with `s < q`: unit ℓ_q flat vectors have arbitrarily large ℓ_s norm. -/
theorem stronger_target_no_dimension_free_conversion {q s : ℝ}
    (hs : 0 < s) (hsq : s < q) (C : ℝ) :
    ∃ d : ℕ, 0 < d ∧ lpNorm s (normalizedFlatVector d q) > C := by
  let γ : ℝ := 1 / s - 1 / q
  have hγ : 0 < γ := stronger_target_dimension_exponent_pos hs hsq
  obtain ⟨d, hd⟩ := exists_nat_gt (max 1 ((max C 0) ^ γ⁻¹))
  have hdreal : (0 : ℝ) < d := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hd)
  have hdpos : 0 < d := Nat.cast_pos.mp hdreal
  refine ⟨d, hdpos, ?_⟩
  rw [normalizedFlatVector_norm d hdpos hs]
  have hbase : (max C 0) ^ γ⁻¹ < (d : ℝ) := (le_max_right _ _).trans_lt hd
  have hgrowth : max C 0 < (d : ℝ) ^ γ := by
    calc
      max C 0 = ((max C 0) ^ γ⁻¹) ^ γ :=
        (Real.rpow_inv_rpow (le_max_right C 0) hγ.ne').symm
      _ < (d : ℝ) ^ γ := Real.rpow_lt_rpow
        (Real.rpow_nonneg (le_max_right C 0) _) hbase hγ
  exact (le_max_left C 0).trans_lt hgrowth

end P31
