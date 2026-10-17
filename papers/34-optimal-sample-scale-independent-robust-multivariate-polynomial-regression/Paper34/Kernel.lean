import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The one-dimensional kernels in Lemma 3.1

We use the actual additive circle and its probability Haar measure.  The Fejér
kernel is the squared modulus of a finite sum of exponential monomials, divided
by its length.  In particular, Fourier coefficients below are Bochner integrals,
not a separately stipulated coefficient sequence.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Paper34.Kernel

instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev Torus := AddCircle (2 * Real.pi)
abbrev haar : Measure Torus := AddCircle.haarAddCircle

/-- The finite exponential sum whose squared modulus gives the Fejér kernel. -/
def exponentialSum (N : ℕ) : C(Torus, ℂ) :=
  ∑ j ∈ Finset.range N, fourier (j : ℤ)

/-- The Fejér kernel, including its continuously extended values at multiples of `2π`. -/
def fejer (N : ℕ) : C(Torus, ℂ) :=
  ((N : ℂ)⁻¹) • (exponentialSum N * star (exponentialSum N))

/-- The de la Vallée Poussin kernel of degree parameter `d`. -/
def valleePoussin (d : ℕ) : C(Torus, ℂ) :=
  (2 : ℂ) • fejer (2 * d) - fejer d

lemma fejer_eq_normSq (N : ℕ) (x : Torus) :
    fejer N x = (((N : ℝ)⁻¹ * Complex.normSq (exponentialSum N x) : ℝ) : ℂ) := by
  simp only [fejer, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
    ContinuousMap.star_apply, smul_eq_mul, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]

lemma fejer_re_nonneg (N : ℕ) (x : Torus) : 0 ≤ (fejer N x).re := by
  rw [fejer_eq_normSq]
  simp only [Complex.ofReal_re]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) (Complex.normSq_nonneg _)

lemma norm_fejer (N : ℕ) (x : Torus) : ‖fejer N x‖ = (fejer N x).re := by
  rw [fejer_eq_normSq, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs,
    abs_of_nonneg]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) (Complex.normSq_nonneg _)

lemma fejer_double_sum (N : ℕ) (x : Torus) :
    fejer N x = (N : ℂ)⁻¹ *
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, fourier ((i : ℤ) - j) x := by
  simp only [fejer, exponentialSum, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
    ContinuousMap.star_apply, ContinuousMap.sum_apply, smul_eq_mul, star_sum,
    Complex.star_def]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [sub_eq_add_neg, fourier_add, fourier_neg]

lemma exponentialSum_zero (N : ℕ) : exponentialSum N (0 : Torus) = N := by
  simp [exponentialSum]

/-- This is the continuously extended value at the origin of the circle. -/
lemma fejer_zero (N : ℕ) : fejer N (0 : Torus) = N := by
  by_cases hN : N = 0
  · simp [hN, fejer, exponentialSum]
  · have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    change (N : ℂ)⁻¹ * (exponentialSum N 0 * star (exponentialSum N 0)) = N
    rw [exponentialSum_zero]
    simp only [Complex.star_def, map_natCast]
    field_simp [hN0]

lemma integral_fourier (k : ℤ) :
    (∫ x : Torus, fourier k x ∂haar) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · simp [hk, measureReal_univ_eq_one]
  · exact integral_eq_zero_of_add_right_eq_neg (μ := haar)
      (fourier_add_half_inv_index hk (by positivity))

lemma fourierCoeff_fourier (j k : ℤ) :
    fourierCoeff (fourier j : Torus → ℂ) k = if j = k then 1 else 0 := by
  simp only [fourierCoeff, smul_eq_mul, ← fourier_add]
  rw [integral_fourier]
  have heq : (-k + j = 0) ↔ j = k := by omega
  simp only [heq]

lemma integrable_continuous (f : C(Torus, ℂ)) : Integrable f haar :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma fourierCoeff_sum {ι : Type*} (s : Finset ι) (f : ι → C(Torus, ℂ)) (k : ℤ) :
    fourierCoeff (∑ i ∈ s, f i : C(Torus, ℂ)) k = ∑ i ∈ s, fourierCoeff (f i) k := by
  simp only [fourierCoeff, ContinuousMap.sum_apply, smul_eq_mul, Finset.mul_sum]
  apply integral_finset_sum
  intro i hi
  exact ((fourier (-k)).continuous.mul (f i).continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma fourierCoeff_smul (c : ℂ) (f : C(Torus, ℂ)) (k : ℤ) :
    fourierCoeff (c • f : C(Torus, ℂ)) k = c * fourierCoeff f k :=
  fourierCoeff.const_smul f c k

lemma fejer_coeff_double_sum (N : ℕ) (k : ℤ) :
    fourierCoeff (fejer N) k = (N : ℂ)⁻¹ *
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        if (i : ℤ) - j = k then (1 : ℂ) else 0 := by
  have h : fejer N = (N : ℂ)⁻¹ •
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (fourier ((i : ℤ) - j) : C(Torus, ℂ)) := by
    ext x
    simpa using fejer_double_sum N x
  rw [h, fourierCoeff_smul, fourierCoeff_sum]
  simp_rw [fourierCoeff_sum, fourierCoeff_fourier]

lemma fejer_coeff_neg (N : ℕ) (k : ℤ) :
    fourierCoeff (fejer N) (-k) = fourierCoeff (fejer N) k := by
  rw [fejer_coeff_double_sum, fejer_coeff_double_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have heq : ((j : ℤ) - i = -k) ↔ (i : ℤ) - j = k := by omega
  simp only [heq]

lemma pair_count_nat (N k : ℕ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      if (i : ℤ) - j = k then (1 : ℂ) else 0) = (N - k : ℕ) := by
  rw [Finset.sum_comm]
  have hinner (j : ℕ) :
      (∑ i ∈ Finset.range N, if (i : ℤ) - j = k then (1 : ℂ) else 0) =
        if j + k < N then 1 else 0 := by
    by_cases h : j + k < N
    · rw [if_pos h, Finset.sum_eq_single (j + k)]
      · simp
      · intro i hi hij
        rw [if_neg]
        omega
      · intro hnot
        exact (hnot (Finset.mem_range.mpr h)).elim
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_neg]
      have hi' := Finset.mem_range.mp hi
      omega
  simp_rw [hinner]
  have hset : (Finset.range N).filter (fun j => j + k < N) = Finset.range (N - k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter]
  rw [hset]
  simp

/-- The actual Fourier coefficient of the Fejér kernel at a nonnegative frequency. -/
lemma fejer_coeff_nat (N k : ℕ) :
    fourierCoeff (fejer N) (k : ℤ) = (N : ℂ)⁻¹ * (N - k : ℕ) := by
  rw [fejer_coeff_double_sum, pair_count_nat]

/-- The actual triangular Fourier multiplier, for every integer frequency. -/
lemma fejer_coeff (N : ℕ) (k : ℤ) :
    fourierCoeff (fejer N) k = (N : ℂ)⁻¹ * (N - k.natAbs : ℕ) := by
  cases k with
  | ofNat k => simpa using fejer_coeff_nat N k
  | negSucc k =>
    change fourierCoeff (fejer N) (-(↑(k + 1) : ℤ)) = _
    rw [fejer_coeff_neg, fejer_coeff_nat]
    rfl

/-- The displayed finite Fourier expansion in the paper, proved from the
squared-exponential-sum construction rather than assigned as formal data. -/
theorem fejer_fourier_expansion (N : ℕ) (hN : 1 ≤ N) (x : Torus) :
    fejer N x = ∑ k ∈ Finset.Ioo (-(N : ℤ)) (N : ℤ),
      ((1 : ℂ) - (k.natAbs : ℂ) / N) * fourier k x := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hcount (k : ℤ) :
      (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        if (i : ℤ) - j = k then (1 : ℂ) else 0) = (N - k.natAbs : ℕ) := by
    have h := fejer_coeff_double_sum N k
    rw [fejer_coeff] at h
    exact (mul_left_cancel₀ (inv_ne_zero hN0) h).symm
  have hsum :
      (∑ k ∈ Finset.Ioo (-(N : ℤ)) (N : ℤ), (N - k.natAbs : ℕ) * fourier k x) =
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, fourier ((i : ℤ) - j) x := by
    calc
      _ = ∑ k ∈ Finset.Ioo (-(N : ℤ)) (N : ℤ),
          (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            if (i : ℤ) - j = k then (1 : ℂ) else 0) * fourier k x := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hcount]
      _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          ∑ k ∈ Finset.Ioo (-(N : ℤ)) (N : ℤ),
            if (i : ℤ) - j = k then fourier k x else 0 := by
        simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        have hij : (i : ℤ) - j ∈ Finset.Ioo (-(N : ℤ)) (N : ℤ) := by
          have hi' := Finset.mem_range.mp hi
          have hj' := Finset.mem_range.mp hj
          simp only [Finset.mem_Ioo]
          omega
        rw [Finset.sum_eq_single ((i : ℤ) - j)]
        · simp
        · intro k hk hne
          rw [if_neg (Ne.symm hne)]
        · intro hnot
          exact (hnot hij).elim
  rw [fejer_double_sum, ← hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k.natAbs ≤ N := by
    have hk' := Finset.mem_Ioo.mp hk
    omega
  rw [Nat.cast_sub hkN, ← mul_assoc]
  congr 1
  field_simp [hN0] <;> ring

lemma fourierCoeff_sub (f g : C(Torus, ℂ)) (k : ℤ) :
    fourierCoeff (f - g : C(Torus, ℂ)) k = fourierCoeff f k - fourierCoeff g k := by
  simp only [fourierCoeff, ContinuousMap.sub_apply, smul_eq_mul, mul_sub]
  apply integral_sub
  · exact ((fourier (-k)).continuous.mul f.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact ((fourier (-k)).continuous.mul g.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Reproduction includes the endpoints `|k| = d`. -/
theorem valleePoussin_coeff (d : ℕ) (hd : 1 ≤ d) (k : ℤ) (hk : k.natAbs ≤ d) :
    fourierCoeff (valleePoussin d) k = 1 := by
  rw [valleePoussin, fourierCoeff_sub, fourierCoeff_smul, fejer_coeff, fejer_coeff]
  have hk2 : k.natAbs ≤ 2 * d := by omega
  rw [Nat.cast_sub hk2, Nat.cast_sub hk]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  push_cast
  field_simp <;> ring

lemma fejer_integral (N : ℕ) (hN : 1 ≤ N) :
    (∫ x : Torus, fejer N x ∂haar) = 1 := by
  have h := fejer_coeff_nat N 0
  simp only [fourierCoeff, Nat.cast_zero, neg_zero, fourier_zero, one_smul, Nat.sub_zero] at h
  rw [h]
  exact inv_mul_cancel₀ (by exact_mod_cast (show N ≠ 0 by omega))

/-- Positivity gives exact unit mass in normalized `L¹`. -/
theorem fejer_L1 (N : ℕ) (hN : 1 ≤ N) :
    (∫ x : Torus, ‖fejer N x‖ ∂haar) = 1 := by
  simp_rw [norm_fejer]
  change (∫ x : Torus, RCLike.re (fejer N x) ∂haar) = 1
  rw [integral_re (integrable_continuous (fejer N)), fejer_integral N hN]
  rfl

/-- The `L¹` part of Lemma 3.1, with the paper's constant `3`. -/
theorem valleePoussin_L1 (d : ℕ) (hd : 1 ≤ d) :
    (∫ x : Torus, ‖valleePoussin d x‖ ∂haar) ≤ 3 := by
  have pointwise (x : Torus) :
      ‖valleePoussin d x‖ ≤ 2 * ‖fejer (2 * d) x‖ + ‖fejer d x‖ := by
    calc
      ‖valleePoussin d x‖ ≤ ‖(2 : ℂ) * fejer (2 * d) x‖ + ‖fejer d x‖ :=
        norm_sub_le _ _
      _ = _ := by rw [norm_mul]; norm_num
  have h := integral_mono (integrable_continuous (valleePoussin d)).norm
    (((integrable_continuous (fejer (2 * d))).norm.const_mul 2).add
      (integrable_continuous (fejer d)).norm) pointwise
  simp only [Pi.add_apply] at h
  rw [integral_add ((integrable_continuous (fejer (2 * d))).norm.const_mul 2)
    (integrable_continuous (fejer d)).norm, integral_const_mul,
    fejer_L1 (2 * d) (by omega), fejer_L1 d hd] at h
  norm_num at h ⊢
  exact h

/-- A finite trigonometric polynomial on the same (genuine) torus. -/
def weightedSum (N : ℕ) (c : ℕ → ℂ) : C(Torus, ℂ) :=
  ∑ j ∈ Finset.range N, c j • fourier (j : ℤ)

/-- Finite Parseval, obtained from orthogonality for normalized Haar measure. -/
lemma weightedSum_integral_norm_sq (N : ℕ) (c : ℕ → ℂ) :
    (∫ x : Torus, ‖weightedSum N c x‖ ^ 2 ∂haar) =
      ∑ j ∈ Finset.range N, ‖c j‖ ^ 2 := by
  have horth : Orthonormal ℂ (fun j : ℕ => (fourierLp (T := 2 * Real.pi) 2 (j : ℤ))) :=
    (orthonormal_fourier (T := 2 * Real.pi)).comp (fun j : ℕ => (j : ℤ))
      (by intro a b h; exact Int.ofNat.inj h)
  have h := horth.inner_sum c c (Finset.range N)
  have hLp : (∑ j ∈ Finset.range N, c j • fourierLp (T := 2 * Real.pi) 2 (j : ℤ)) =
      ContinuousMap.toLp 2 haar ℂ (weightedSum N c) := by
    simp only [weightedSum, map_sum, map_smul, fourierLp]
  rw [hLp, ContinuousMap.inner_toLp] at h
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    (∫ x : Torus, ((‖weightedSum N c x‖ ^ 2 : ℝ) : ℂ) ∂haar) =
        ∫ x : Torus, weightedSum N c x * conj (weightedSum N c x) ∂haar := by
      congr 1
      ext x
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    _ = ∑ j ∈ Finset.range N, conj (c j) * c j := h
    _ = ((∑ j ∈ Finset.range N, ‖c j‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

lemma exponentialSum_integral_norm_sq (N : ℕ) :
    (∫ x : Torus, ‖exponentialSum N x‖ ^ 2 ∂haar) = N := by
  simpa [weightedSum, exponentialSum] using weightedSum_integral_norm_sq N (fun _ => 1)

/-- The angular derivative of the finite exponential sum. -/
def exponentialSumDerivative (N : ℕ) : C(Torus, ℂ) :=
  weightedSum N (fun j => (j : ℂ) * Complex.I)

lemma exponentialSumDerivative_integral_norm_sq (N : ℕ) :
    (∫ x : Torus, ‖exponentialSumDerivative N x‖ ^ 2 ∂haar) ≤ (N : ℝ) ^ 3 := by
  rw [exponentialSumDerivative, weightedSum_integral_norm_sq]
  calc
    (∑ j ∈ Finset.range N, ‖(j : ℂ) * Complex.I‖ ^ 2) ≤
        ∑ j ∈ Finset.range N, (N : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [norm_mul, Complex.norm_natCast, Complex.norm_I, mul_one]
      have hj' : (j : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hj).le
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hj' 2
    _ = (N : ℝ) ^ 3 := by simp; ring

lemma hasDerivAt_exponentialSum (N : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => exponentialSum N (y : Torus))
      (exponentialSumDerivative N (x : Torus)) x := by
  simp only [exponentialSum, exponentialSumDerivative, weightedSum,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  apply HasDerivAt.fun_sum
  intro j hj
  convert hasDerivAt_fourier (2 * Real.pi) (j : ℤ) x using 1
  congr 1
  push_cast
  field_simp <;> ring

/-- The derivative is represented on the torus and proved to be the actual real angular derivative. -/
def fejerDerivative (N : ℕ) : C(Torus, ℂ) :=
  (N : ℂ)⁻¹ •
    (exponentialSumDerivative N * star (exponentialSum N) +
      exponentialSum N * star (exponentialSumDerivative N))

lemma hasDerivAt_fejer (N : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => fejer N (y : Torus)) (fejerDerivative N (x : Torus)) x := by
  have h := hasDerivAt_exponentialSum N x
  exact (h.mul h.star).const_mul (N : ℂ)⁻¹

lemma fejerDerivative_norm_le (N : ℕ) (x : Torus) :
    ‖fejerDerivative N x‖ ≤
      ((N : ℝ)⁻¹) ^ 2 * ‖exponentialSumDerivative N x‖ ^ 2 +
        ‖exponentialSum N x‖ ^ 2 := by
  have hnorm : ‖fejerDerivative N x‖ ≤
      (N : ℝ)⁻¹ * (2 * ‖exponentialSumDerivative N x‖ * ‖exponentialSum N x‖) := by
    simp only [fejerDerivative, ContinuousMap.smul_apply, ContinuousMap.add_apply,
      ContinuousMap.mul_apply, ContinuousMap.star_apply, smul_eq_mul, norm_mul,
      norm_inv, Complex.norm_natCast]
    calc
      (N : ℝ)⁻¹ * ‖exponentialSumDerivative N x * star (exponentialSum N x) +
          exponentialSum N x * star (exponentialSumDerivative N x)‖ ≤
          (N : ℝ)⁻¹ * (‖exponentialSumDerivative N x * star (exponentialSum N x)‖ +
            ‖exponentialSum N x * star (exponentialSumDerivative N x)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ = _ := by simp only [norm_mul, norm_star]; ring
  refine hnorm.trans ?_
  nlinarith [sq_nonneg ((N : ℝ)⁻¹ * ‖exponentialSumDerivative N x‖ -
    ‖exponentialSum N x‖)]

lemma integrable_norm_sq (f : C(Torus, ℂ)) :
    Integrable (fun x => ‖f x‖ ^ 2) haar :=
  (f.continuous.norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- A direct finite-Parseval proof of the endpoint derivative estimate. -/
theorem fejerDerivative_L1 (N : ℕ) (hN : 1 ≤ N) :
    (∫ x : Torus, ‖fejerDerivative N x‖ ∂haar) ≤ 2 * N := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hupper := integral_mono (integrable_continuous (fejerDerivative N)).norm
    (((integrable_norm_sq (exponentialSumDerivative N)).const_mul ((N : ℝ)⁻¹ ^ 2)).add
      (integrable_norm_sq (exponentialSum N))) (fejerDerivative_norm_le N)
  simp only [Pi.add_apply] at hupper
  rw [integral_add ((integrable_norm_sq (exponentialSumDerivative N)).const_mul _)
    (integrable_norm_sq (exponentialSum N)), integral_const_mul,
    exponentialSum_integral_norm_sq] at hupper
  calc
    (∫ x : Torus, ‖fejerDerivative N x‖ ∂haar) ≤
        ((N : ℝ)⁻¹) ^ 2 *
          (∫ x : Torus, ‖exponentialSumDerivative N x‖ ^ 2 ∂haar) + N := hupper
    _ ≤ ((N : ℝ)⁻¹) ^ 2 * (N : ℝ) ^ 3 + N := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left
        (exponentialSumDerivative_integral_norm_sq N) (sq_nonneg _)) _
    _ = 2 * N := by field_simp [hN0] <;> ring

/-- The actual angular derivative of the de la Vallée Poussin kernel. -/
def valleePoussinDerivative (d : ℕ) : C(Torus, ℂ) :=
  (2 : ℂ) • fejerDerivative (2 * d) - fejerDerivative d

lemma hasDerivAt_valleePoussin (d : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => valleePoussin d (y : Torus))
      (valleePoussinDerivative d (x : Torus)) x :=
  ((hasDerivAt_fejer (2 * d) x).const_mul 2).sub (hasDerivAt_fejer d x)

/-- The derivative part of Lemma 3.1 with the explicit absolute constant `C = 10`. -/
theorem valleePoussinDerivative_L1 (d : ℕ) (hd : 1 ≤ d) :
    (∫ x : Torus, ‖valleePoussinDerivative d x‖ ∂haar) ≤ 10 * d := by
  have pointwise (x : Torus) :
      ‖valleePoussinDerivative d x‖ ≤
        2 * ‖fejerDerivative (2 * d) x‖ + ‖fejerDerivative d x‖ := by
    calc
      ‖valleePoussinDerivative d x‖ ≤
          ‖(2 : ℂ) * fejerDerivative (2 * d) x‖ + ‖fejerDerivative d x‖ :=
        norm_sub_le _ _
      _ = _ := by rw [norm_mul]; norm_num
  have h := integral_mono (integrable_continuous (valleePoussinDerivative d)).norm
    (((integrable_continuous (fejerDerivative (2 * d))).norm.const_mul 2).add
      (integrable_continuous (fejerDerivative d)).norm) pointwise
  simp only [Pi.add_apply] at h
  rw [integral_add ((integrable_continuous (fejerDerivative (2 * d))).norm.const_mul 2)
    (integrable_continuous (fejerDerivative d)).norm, integral_const_mul] at h
  have h1 := fejerDerivative_L1 (2 * d) (by omega)
  have h2 := fejerDerivative_L1 d hd
  push_cast at h1
  linarith

/-- The three conclusions of Lemma 3.1, with a genuine angular derivative
and the explicit absolute derivative constant `10`. -/
theorem one_dimensional_kernel_bounds (d : ℕ) (hd : 1 ≤ d) :
    (∀ k : ℤ, k.natAbs ≤ d → fourierCoeff (valleePoussin d) k = 1) ∧
    (∫ x : Torus, ‖valleePoussin d x‖ ∂haar) ≤ 3 ∧
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => valleePoussin d (s : Torus))
      (valleePoussinDerivative d (t : Torus)) t) ∧
    (∫ x : Torus, ‖valleePoussinDerivative d x‖ ∂haar) ≤ 10 * d :=
  ⟨valleePoussin_coeff d hd, valleePoussin_L1 d hd,
    hasDerivAt_valleePoussin d, valleePoussinDerivative_L1 d hd⟩

end Paper34.Kernel
