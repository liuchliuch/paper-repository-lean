import Paper22.Programs
import Paper22.Divergences

open scoped MatrixOrder ComplexOrder
open Matrix
noncomputable section
namespace Paper22
variable {n d : ℕ}

lemma spectral_scalar_lower_bound {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) {lam : ℝ} (hlam : ∀ i, lam ≤ hA.eigenvalues i) :
    lam • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ A := by
  rw [← Algebra.algebraMap_eq_smul_one]
  conv_rhs => rw [← cfc_id ℝ A]
  apply algebraMap_le_cfc
  · intro x hx
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hlam i
  · exact continuous_id.continuousOn
  · exact hA.isSelfAdjoint

/-- A common positive lower eigenvalue bounds the MC error away from zero. -/
theorem epsMC_lower_bound_of_spectral [NeZero n] (V : CQChannel n d)
    {lam : ℝ} (hlam : ∀ x i, lam ≤ (V.density x).isHermitian.eigenvalues i)
    (hlam0 : 0 ≤ lam) {L : ℝ} (hL : 0 < L) :
    lam * (d : ℝ) * (1 - 1 / L) ≤ epsMC V L := by
  obtain ⟨q₀, T₀, h₀⟩ := mc_feasible_nonempty (d := d) (Nat.pos_of_ne_zero (NeZero.ne n)) hL.le
  apply le_csInf (show ({e | ∃ q T, MCFEasable L q T ∧
      e = programObjective V.states q T} : Set ℝ).Nonempty from
    ⟨_, q₀, T₀, h₀, rfl⟩)
  rintro e ⟨q, T, h, rfl⟩
  have hsum : ∑ x, q x * (1 - T x).trace.re =
      (d : ℝ) - (∑ x, q x • T x).trace.re := by
    simp only [trace_sub, trace_one, Fintype.card_fin, Complex.sub_re, Complex.natCast_re,
      mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h.2.1, one_mul,
      trace_sum, trace_smul, Complex.re_sum, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have htrace : (∑ x, q x • T x).trace.re ≤ (1 / L) * d := by
    have ht := (le_iff.mp h.2.2.2).trace_nonneg
    simpa only [trace_sub, trace_smul, trace_one, Fintype.card_fin, Complex.sub_re,
      Complex.real_smul, Complex.natCast_re, sub_nonneg, Complex.zero_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_im,
      zero_mul, sub_zero] using ht.1
  calc
    lam * (d : ℝ) * (1 - 1 / L) ≤ lam * ((d : ℝ) - (∑ x, q x • T x).trace.re) := by
      nlinarith
    _ = ∑ x, q x * ((lam • (1 : Matrix (Fin d) (Fin d) ℂ)) * (1 - T x)).trace.re := by
      simp only [smul_mul_assoc, one_mul, trace_smul, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [← hsum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ programObjective V.states q T := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (h.1 x)
      rw [Matrix.trace_mul_comm, Matrix.trace_mul_comm (V.states x)]
      exact trace_mul_mono_re (h.2.2.1 x).one_sub_posSemidef
        (spectral_scalar_lower_bound (V.density x).isHermitian (hlam x))

theorem epsMC_pos_fullRank [NeZero n] [NeZero d] (V : CQChannel n d)
    (hV : V.FullRank) {L : ℝ} (hL : 1 < L) : 0 < epsMC V L := by
  obtain ⟨lam, hlam0, hlam⟩ := V.exists_uniform_spectral_lower_bound hV
  apply lt_of_lt_of_le _ (epsMC_lower_bound_of_spectral V hlam hlam0.le (by linarith))
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hdiv : 1 / L < 1 := (div_lt_one (by linarith : 0 < L)).mpr hL
  exact mul_pos (mul_pos hlam0 hd) (sub_pos.mpr hdiv)

end Paper22
end
