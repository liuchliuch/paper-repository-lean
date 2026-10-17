import ELV.AdmissibleOperational
import ELV.Fock

/-! Reciprocal answer-block rescaling (4.4)--(4.6), on the true generated
states of all promised oracles, with arbitrary complex coordinates. -/
noncomputable section
namespace ELV.Rescale
open ELV.Model ELV.Costs

lemma kappa_pos (gap : Gap) : 0 < gap.kappa :=
  Real.rpow_pos_of_pos (div_pos gap.ell_pos gap.high_pos) _

lemma kappa_fourth (gap : Gap) : gap.kappa ^ 4 = gap.ell / gap.high := by
  rw [Gap.kappa, ← Real.rpow_mul_natCast (div_nonneg gap.ell_nonneg gap.high_nonneg)]
  norm_num

lemma kappa_order (gap : Gap) : gap.kappa ^ 2 ≤ gap.kappa⁻¹ ^ 2 := by
  have hk := kappa_pos gap
  have h4 : gap.kappa ^ 4 < 1 := by
    rw [kappa_fourth]
    exact (div_lt_one gap.high_pos).2 gap.ell_lt_high
  have hid : gap.kappa ^ 2 * gap.kappa⁻¹ ^ 2 = 1 := by
    field_simp
  have hh : gap.kappa ^ 2 * gap.kappa ^ 2 ≤ gap.kappa ^ 2 * gap.kappa⁻¹ ^ 2 := by
    nlinarith
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hk)).mp (by nlinarith [hh])

lemma kappa_boundary (gap : Gap) :
    gap.kappa ^ 2 * gap.high + gap.kappa⁻¹ ^ 2 * gap.ell = gap.mu := by
  have hk := (kappa_pos gap).ne'
  have hfirst : gap.kappa ^ 2 * gap.high = Real.sqrt (gap.ell * gap.high) := by
    apply (sq_eq_sq₀ (mul_nonneg (sq_nonneg _) gap.high_nonneg) (Real.sqrt_nonneg _)).mp
    calc
      (gap.kappa ^ 2 * gap.high) ^ 2 = gap.kappa ^ 4 * gap.high ^ 2 := by ring
      _ = gap.ell / gap.high * gap.high ^ 2 := by rw [kappa_fourth]
      _ = gap.ell * gap.high := by field_simp
      _ = Real.sqrt (gap.ell * gap.high) ^ 2 := (Real.sq_sqrt gap.ell_mul_high_pos.le).symm
  have hquart : gap.kappa ^ 4 * gap.high = gap.ell := by
    rw [kappa_fourth]
    exact div_mul_cancel₀ _ gap.high_pos.ne'
  have hsecond : gap.kappa⁻¹ ^ 2 * gap.ell = gap.kappa ^ 2 * gap.high := by
    rw [← hquart]
    field_simp
    <;> ring
  rw [hsecond, hfirst, gap.mu_eq_two_sqrt]
  ring

variable {n : ℕ}

/-- Squared norm in the answer-1 block. -/
def mass (v : Mspace n) : ℝ := ∑ i : Fin (2*n), if n ≤ i.val then ‖v i‖ ^ 2 else 0

/-- Real rescaling of the two orthogonal answer blocks. -/
def scaleBlocks (a b : ℝ) (v : Mspace n) : Mspace n :=
  WithLp.toLp 2 (fun i => ((if n ≤ i.val then b else a : ℝ) : ℂ) * v i)

theorem scaleBlocks_norm_sq (a b : ℝ) (v : Mspace n) :
    ‖scaleBlocks a b v‖ ^ 2 = a ^ 2 * (‖v‖ ^ 2 - mass v) + b ^ 2 * mass v := by
  rw [PiLp.norm_sq_eq_of_L2]
  have hterm : ∀ i : Fin (2*n), ‖scaleBlocks a b v i‖ ^ 2 =
      a ^ 2 * ‖v i‖ ^ 2 + (b ^ 2 - a ^ 2) * (if n ≤ i.val then ‖v i‖ ^ 2 else 0) := by
    intro i
    by_cases hi : n ≤ i.val
    · simp [scaleBlocks, hi, norm_mul, mul_pow, Complex.norm_real]
      ring
    · simp [scaleBlocks, hi, norm_mul, mul_pow, Complex.norm_real]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [← PiLp.norm_sq_eq_of_L2]
  change a ^ 2 * ‖v‖ ^ 2 + (b ^ 2 - a ^ 2) * mass v = _
  ring

/-- Opposite-label block scalings cancel in the entire complex inner product. -/
theorem scaleBlocks_cross (a : ℝ) (ha : a ≠ 0) (v w : Mspace n) :
    inner ℂ (scaleBlocks a a⁻¹ v) (scaleBlocks a⁻¹ a w) = inner ℂ v w := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℂ (((if n ≤ i.val then a⁻¹ else a : ℝ) : ℂ) * v i)
    (((if n ≤ i.val then a else a⁻¹ : ℝ) : ℂ) * w i) = inner ℂ (v i) (w i)
  by_cases hi : n ≤ i.val <;>
    simp [hi, RCLike.inner_apply, map_mul, map_inv₀, mul_assoc, mul_left_comm, mul_comm, ha]

variable [NeZero n]

/-- Equation (4.4), using the actual label and generated state of the oracle. -/
def contracted (gap : Gap) (O : promisedFamily n gap.δ) : Mspace n :=
  if label gap.δ O = 0 then scaleBlocks gap.kappa gap.kappa⁻¹ O.val.phi
  else scaleBlocks gap.kappa⁻¹ gap.kappa O.val.phi

lemma low_of_label_zero (gap : Gap) (O : promisedFamily n gap.δ)
    (hr : label gap.δ O = 0) : O.val.p ≤ gap.ell := by
  have hp : O.val.p ≤ 1 / 2 := by
    by_contra hc
    change (if O.val.p ≤ (1 / 2 : ℝ) then (0 : Fin 2) else 1) = 0 at hr
    rw [if_neg hc] at hr
    exact Fin.zero_ne_one hr.symm
  rcases O.property with hl | hh
  · exact hl
  · exfalso
    linarith [gap.δ_pos]

lemma high_of_label_nonzero (gap : Gap) (O : promisedFamily n gap.δ)
    (hr : label gap.δ O ≠ 0) : gap.high ≤ O.val.p := by
  have hp : ¬ O.val.p ≤ 1 / 2 := by
    intro hc
    apply hr
    change (if O.val.p ≤ (1 / 2 : ℝ) then (0 : Fin 2) else 1) = 0
    exact if_pos hc
  rcases O.property with hl | hh
  · exfalso
    have h := gap.δ_pos
    have he : O.val.p ≤ 1/2-gap.δ := hl
    linarith
  · exact hh

/-- Equation (4.6), including the endpoints p=0 and p=1. -/
theorem contracted_norm_sq_le (gap : Gap) (O : promisedFamily n gap.δ) :
    ‖contracted gap O‖ ^ 2 ≤ gap.mu := by
  have horder := kappa_order gap
  have hb := kappa_boundary gap
  have hn := O.val.phi_norm
  have hm : mass O.val.phi = O.val.p := rfl
  by_cases hr : label gap.δ O = 0
  · rw [contracted, if_pos hr, scaleBlocks_norm_sq, hn, hm]
    have hp := low_of_label_zero gap O hr
    have hmul := mul_nonneg (sub_nonneg.mpr horder) (sub_nonneg.mpr hp)
    have he := gap.ell_add_high
    nlinarith
  · rw [contracted, if_neg hr, scaleBlocks_norm_sq, hn, hm]
    have hp := high_of_label_nonzero gap O hr
    have hmul := mul_nonneg (sub_nonneg.mpr horder) (sub_nonneg.mpr hp)
    have he := gap.ell_add_high
    nlinarith

theorem contracted_inner_cross (gap : Gap) (O O' : promisedFamily n gap.δ)
    (hr : label gap.δ O ≠ label gap.δ O') :
    inner ℂ (contracted gap O) (contracted gap O') = inner ℂ O.val.phi O'.val.phi := by
  have hk := (kappa_pos gap).ne'
  by_cases h0 : label gap.δ O = 0
  · have h1 : label gap.δ O' ≠ 0 := by intro h; exact hr (h0.trans h.symm)
    simp only [contracted, if_pos h0, if_neg h1]
    exact scaleBlocks_cross _ hk _ _
  · have h1 : label gap.δ O' = 0 := by
      have ha : label gap.δ O = 1 := by omega
      have hc : label gap.δ O' ≠ 1 := by simpa [ha] using hr.symm
      omega
    simp only [contracted, if_neg h0, if_pos h1]
    simpa using scaleBlocks_cross gap.kappa⁻¹ (inv_ne_zero hk) O.val.phi O'.val.phi

end ELV.Rescale
