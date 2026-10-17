import Paper34.Kernel
import Mathlib.Algebra.Field.GeomSum

/-!
# The sine-quotient definition of the source Fejér kernel

This is an identity for the actual continuous kernel from `Kernel`, obtained
from the finite geometric sum. No Fourier or kernel identity is assumed.
-/

noncomputable section
open scoped BigOperators

namespace Paper34.Kernel

lemma fourier_nat_eq_exp (j : ℕ) (t : ℝ) :
    fourier (j : ℤ) (t : Torus) = Complex.exp ((j : ℂ) * (t : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

lemma exponentialSum_eq_geom (N : ℕ) (t : ℝ) :
    exponentialSum N (t : Torus) =
      ∑ j ∈ Finset.range N, Complex.exp ((t : ℂ) * Complex.I) ^ j := by
  simp only [exponentialSum, ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fourier_nat_eq_exp, ← Complex.exp_nat_mul]
  congr 1
  ring

lemma normSq_exp_sub_one (t : ℝ) :
    Complex.normSq (Complex.exp ((t : ℂ) * Complex.I) - 1) =
      4 * Real.sin (t / 2) ^ 2 := by
  rw [Complex.exp_mul_I]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re,
    Complex.cos_ofReal_re, Complex.mul_re, Complex.sin_ofReal_re,
    Complex.I_re, Complex.sin_ofReal_im, Complex.I_im, mul_zero,
    sub_zero, add_zero, Complex.one_re, Complex.sub_im, Complex.add_im,
    Complex.cos_ofReal_im, Complex.mul_im, mul_one, zero_add, Complex.one_im]
  have ht : Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
    have hdouble : 2 * (t / 2) = t := by ring
    simpa only [hdouble] using Real.cos_two_mul (t / 2)
  nlinarith [Real.sin_sq_add_cos_sq t, Real.sin_sq_add_cos_sq (t / 2)]

lemma exponentialSum_normSq_sine (N : ℕ) (t : ℝ)
    (ht : Real.sin (t / 2) ≠ 0) :
    Complex.normSq (exponentialSum N (t : Torus)) =
      (Real.sin ((N : ℝ) * t / 2) / Real.sin (t / 2)) ^ 2 := by
  have hgeom := congrArg Complex.normSq
    (geom_sum_mul (Complex.exp ((t : ℂ) * Complex.I)) N)
  have hpow : Complex.exp ((t : ℂ) * Complex.I) ^ N =
      Complex.exp ((((N : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← exponentialSum_eq_geom, map_mul, hpow,
    normSq_exp_sub_one t, normSq_exp_sub_one ((N : ℝ) * t)] at hgeom
  rw [div_pow]
  apply (eq_div_iff (pow_ne_zero 2 ht)).2
  nlinarith [hgeom]

/-- The precise sine quotient in source (3.1), away from its removable poles. -/
theorem fejer_sine_quotient (N : ℕ) (t : ℝ) (ht : Real.sin (t / 2) ≠ 0) :
    fejer N (t : Torus) =
      ((((N : ℝ)⁻¹) *
        (Real.sin ((N : ℝ) * t / 2) / Real.sin (t / 2)) ^ 2 : ℝ) : ℂ) := by
  rw [fejer_eq_normSq, exponentialSum_normSq_sine N t ht]

/-- The quotient's continuous extension is the existing actual Fejér kernel.
The equality on the punctured domain and continuity are both supplied. -/
theorem fejer_sine_continuous_extension (N : ℕ) :
    Continuous (fun t : ℝ => fejer N (t : Torus)) ∧
    (∀ t : ℝ, Real.sin (t / 2) ≠ 0 →
      fejer N (t : Torus) =
        ((((N : ℝ)⁻¹) *
          (Real.sin ((N : ℝ) * t / 2) / Real.sin (t / 2)) ^ 2 : ℝ) : ℂ)) ∧
    fejer N (0 : Torus) = N := by
  exact ⟨(fejer N).continuous.comp continuous_quotient_mk',
    fun t ht => fejer_sine_quotient N t ht, fejer_zero N⟩

/-- Source sine quotient, with the specified value at every removable pole. -/
def sourceFejerSine (N : ℕ) (t : ℝ) : ℝ :=
  if Real.sin (t / 2) = 0 then N
  else (N : ℝ)⁻¹ * (Real.sin ((N : ℝ) * t / 2) / Real.sin (t / 2)) ^ 2

/-- Equality on the full real line, including the continuous-extension values. -/
theorem fejer_eq_sourceFejerSine (N : ℕ) (t : ℝ) :
    fejer N (t : Torus) = (sourceFejerSine N t : ℂ) := by
  by_cases ht : Real.sin (t / 2) = 0
  · rcases Real.sin_eq_zero_iff.mp ht with ⟨ell, hell⟩
    have hzero : (t : Torus) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      refine ⟨ell, ?_⟩
      rw [zsmul_eq_mul]
      nlinarith [hell]
    simp [sourceFejerSine, ht, hzero, fejer_zero]
  · simpa [sourceFejerSine, ht] using fejer_sine_quotient N t ht

/-- The source's patched sine quotient really is continuous, proved through
its equality with the actual continuous finite-sum kernel. -/
theorem continuous_sourceFejerSine (N : ℕ) : Continuous (sourceFejerSine N) := by
  have heq : sourceFejerSine N = fun t : ℝ => (fejer N (t : Torus)).re := by
    funext t
    rw [fejer_eq_sourceFejerSine]
    simp
  rw [heq]
  exact Complex.continuous_re.comp
    ((fejer N).continuous.comp continuous_quotient_mk')

theorem sourceFejerSine_two_pi_int (N : ℕ) (ell : ℤ) :
    sourceFejerSine N (2 * Real.pi * ell) = N := by
  have hzero : ((2 * Real.pi * ell : ℝ) : Torus) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨ell, ?_⟩
    rw [zsmul_eq_mul]
    ring
  have h := congrArg Complex.re (fejer_eq_sourceFejerSine N (2 * Real.pi * ell))
  simpa [hzero, fejer_zero] using h.symm

/-- Both displayed definitions of `F_N` in the source now denote the same
function, rather than merely having assigned equal formal coefficients. -/
theorem sourceFejerSine_fourier_expansion (N : ℕ) (hN : 1 ≤ N) (t : ℝ) :
    (sourceFejerSine N t : ℂ) =
      ∑ k ∈ Finset.Ioo (-(N : ℤ)) (N : ℤ),
        ((1 : ℂ) - (k.natAbs : ℂ) / N) * fourier k (t : Torus) := by
  rw [← fejer_eq_sourceFejerSine]
  exact fejer_fourier_expansion N hN (t : Torus)

theorem valleePoussin_eq_sourceFejerSine (d : ℕ) (t : ℝ) :
    valleePoussin d (t : Torus) =
      ((2 * sourceFejerSine (2 * d) t - sourceFejerSine d t : ℝ) : ℂ) := by
  simp only [valleePoussin, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    smul_eq_mul, fejer_eq_sourceFejerSine, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_ofNat]

end Paper34.Kernel
