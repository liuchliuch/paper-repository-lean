import Paper18.Category.ENOPseudounitaryBounds
import Paper18.Fusion.Grading

noncomputable section
open Classical
open scoped BigOperators ComplexConjugate
universe u

namespace Paper18

private lemma real_sign_mem (r f : ℝ) (hf : 0 < f) (hr : |r| = f) :
    r / f = 1 ∨ r / f = -1 := by
  apply (abs_eq (zero_le_one : (0 : ℝ) ≤ 1)).mp
  rw [abs_div, hr, abs_of_pos hf, div_self (ne_of_gt hf)]

/-- Equality in the FP triangle bound forces the signs on every actual
fusion constituent to multiply. -/
lemma real_dimension_constituent_sign {ι : Type u} [Fintype ι] (B : FusionBasis ι)
    (r : ι → ℝ) (hr : ∀ i, |r i| = B.fpdim i)
    (hm : ∀ i j, ∑ k, (B.N i j k : ℝ) * r k = r i * r j)
    (i j k : ι) (hk : 0 < B.N i j k) :
    r k / B.fpdim k = (r i / B.fpdim i) * (r j / B.fpdim j) := by
  let s := (r i / B.fpdim i) * (r j / B.fpdim j)
  have hsi := real_sign_mem (r i) (B.fpdim i) (B.fpdim_pos i) (hr i)
  have hsj := real_sign_mem (r j) (B.fpdim j) (B.fpdim_pos j) (hr j)
  have hs : s = 1 ∨ s = -1 := by
    rcases hsi with hi | hi <;> rcases hsj with hj | hj <;> simp [s, hi, hj]
  have hs_sq : s ^ 2 = 1 := by rcases hs with hs | hs <;> simp [hs]
  have hs_mul : s * (B.fpdim i * B.fpdim j) = r i * r j := by
    dsimp [s]
    field_simp [ne_of_gt (B.fpdim_pos i), ne_of_gt (B.fpdim_pos j)]
  have hs_prod : s * (r i * r j) = B.fpdim i * B.fpdim j := by
    rw [← hs_mul, ← mul_assoc, ← pow_two, hs_sq, one_mul]
  have hgap (z : ι) : 0 ≤ B.fpdim z - s * r z := by
    have hz := abs_le.mp (hr z).le
    rcases hs with hs | hs <;> rw [hs] <;> linarith
  have hsum : ∑ z, (B.N i j z : ℝ) * (B.fpdim z - s * r z) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    have he : (∑ z, (B.N i j z : ℝ) * (s * r z)) = s * ∑ z, (B.N i j z : ℝ) * r z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    rw [B.fpdim_mul, he, hm, hs_prod, sub_self]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun z (_ : z ∈ Finset.univ) => mul_nonneg (Nat.cast_nonneg (B.N i j z)) (hgap z))).mp
      hsum k (Finset.mem_univ k)
  have hgap0 : B.fpdim k - s * r k = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (by exact_mod_cast ne_of_gt hk)
  apply (div_eq_iff (ne_of_gt (B.fpdim_pos k))).mpr
  change r k = s * B.fpdim k
  rcases hs with hs | hs <;> rw [hs] at hgap0 ⊢ <;> linarith

namespace PivotalData
variable {ι : Type u} [Fintype ι] {B : FusionBasis ι} (J : PivotalData B)

lemma real_jdim_tensor (hJ : J.Spherical) (i j : ι) :
    ∑ k, (B.N i j k : ℝ) * (J.jdim k).re = (J.jdim i).re * (J.jdim j).re := by
  have h := congrArg Complex.re (J.jdim_tensor i j)
  simpa [Complex.mul_re, J.jdim_im_eq_zero hJ] using h.symm

lemma abs_re_jdim_eq_fpdim (hJ : J.Spherical)
    (hD : J.globalDimension.re = B.totalFPdim) (i : ι) : |(J.jdim i).re| = B.fpdim i := by
  have hc : ((J.jdim i).re : ℂ) = J.jdim i :=
    Complex.conj_eq_iff_re.mp ((J.jdim_dual_eq_conj i).symm.trans (J.jdim_dual_of_spherical hJ i))
  calc
    _ = ‖((J.jdim i).re : ℂ)‖ := by simp
    _ = ‖J.jdim i‖ := congrArg norm hc
    _ = _ := J.norm_jdim_eq_fpdim_of_global_eq hD i

/-- The sign determined by actual categorical dimensions. This is merely
a function until the global-dimension equality is proved. -/
def normalizedSign (i : ι) : ℂ := ((J.jdim i).re / B.fpdim i : ℝ)

/-- Given equality of the two global dimensions, all sign-character laws
are derived from actual dimension and fusion equations. -/
def signCharacterOfGlobalEq (hJ : J.Spherical)
    (hD : J.globalDimension.re = B.totalFPdim) : SignCharacter B where
  val := J.normalizedSign
  val_mem i := by
    dsimp only [normalizedSign]
    rcases real_sign_mem (J.jdim i).re (B.fpdim i) (B.fpdim_pos i)
      (J.abs_re_jdim_eq_fpdim hJ hD i) with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  val_one := by simp [normalizedSign, J.jdim_one]
  val_dual i := by
    have hi := real_sign_mem (J.jdim i).re (B.fpdim i) (B.fpdim_pos i)
      (J.abs_re_jdim_eq_fpdim hJ hD i)
    simp only [normalizedSign, J.jdim_dual_of_spherical hJ, B.fpdim_dual]
    rcases hi with hi | hi <;> rw [hi] <;> norm_num
  val_tensor i j k hk := by
    have h := real_dimension_constituent_sign B (fun i => (J.jdim i).re)
      (J.abs_re_jdim_eq_fpdim hJ hD) (J.real_jdim_tensor hJ) i j k hk
    change (((J.jdim k).re / B.fpdim k : ℝ) : ℂ) =
      (((J.jdim i).re / B.fpdim i : ℝ) : ℂ) * (((J.jdim j).re / B.fpdim j : ℝ) : ℂ)
    exact_mod_cast h

theorem sign_mul_jdim_of_global_eq (hJ : J.Spherical)
    (hD : J.globalDimension.re = B.totalFPdim) (i : ι) :
    (J.signCharacterOfGlobalEq hJ hD).val i * J.jdim i = (B.fpdim i : ℂ) := by
  have hc : ((J.jdim i).re : ℂ) = J.jdim i :=
    Complex.conj_eq_iff_re.mp ((J.jdim_dual_eq_conj i).symm.trans (J.jdim_dual_of_spherical hJ i))
  have hr := J.abs_re_jdim_eq_fpdim hJ hD i
  have he : ((J.jdim i).re / B.fpdim i) * (J.jdim i).re = B.fpdim i := by
    have hs : (J.jdim i).re ^ 2 = B.fpdim i ^ 2 := by rw [← sq_abs, hr]
    field_simp [ne_of_gt (B.fpdim_pos i)]
    nlinarith
  change (((J.jdim i).re / B.fpdim i : ℝ) : ℂ) * J.jdim i = (B.fpdim i : ℂ)
  rw [← hc, ← Complex.ofReal_mul]
  exact congrArg Complex.ofReal he

end PivotalData
end Paper18
