import Paper02.Bounds
import Paper02.MeasureDual
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.ZMod.ValMinAbs

/-!
# The finite Fourier–Hahn construction (Proposition 3.3)

Normalized discrete Fourier coefficients of a real even table are real. Fourier
inversion and Parseval give an exact difference of finite positive atomic Lévy
exponents with square-root cancellation cost.
-/

noncomputable section

namespace Paper02.Fourier

open Paper02 Finset
open scoped ComplexConjugate

variable {p : ℕ} [NeZero p]

lemma conj_stdAddChar (x : ZMod p) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj,
    ← AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]

lemma conj_dft_real (F : ZMod p → ℝ) (j : ZMod p) :
    conj (ZMod.dft (fun x => (F x : ℂ)) j) =
      ZMod.dft (fun x => (F x : ℂ)) (-j) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul, conj_stdAddChar,
    Complex.conj_ofReal, mul_neg, neg_neg]

lemma dft_real (F : ZMod p → ℝ) (hF : Function.Even F) (j : ZMod p) :
    ((ZMod.dft (fun x => (F x : ℂ)) j).re : ℂ) =
      ZMod.dft (fun x => (F x : ℂ)) j := by
  have he : Function.Even (fun x => (F x : ℂ)) := fun x => congrArg (fun t : ℝ => (t : ℂ)) (hF x)
  have hc := conj_dft_real F j
  rw [ZMod.dft_even_iff.mpr he j] at hc
  apply Complex.ext
  · simp
  · have hi := congrArg Complex.im hc
    simp only [Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

/-- The normalized, real discrete Fourier coefficients. -/
def coeff (F : ZMod p → ℝ) (j : ZMod p) : ℝ :=
  (ZMod.dft (fun x => (F x : ℂ)) j).re / p

lemma coeff_complex (F : ZMod p → ℝ) (hF : Function.Even F) (j : ZMod p) :
    (coeff F j : ℂ) = (p : ℂ)⁻¹ * ZMod.dft (fun x => (F x : ℂ)) j := by
  simp only [coeff, Complex.ofReal_div, Complex.ofReal_natCast, dft_real F hF]
  ring

lemma sum_dft_mul (A B : ZMod p → ℂ) :
    (∑ j, ZMod.dft A j * B j) = ∑ j, A j * ZMod.dft B j := by
  simp only [ZMod.dft_apply, smul_eq_mul, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [mul_comm k j]
  ring

lemma coeff_inversion_complex (F : ZMod p → ℝ) (hF : Function.Even F)
    (k : ZMod p) :
    (F k : ℂ) = ∑ j, ZMod.stdAddChar (j * k) * (coeff F j : ℂ) := by
  have hi := congrFun (ZMod.dft.symm_apply_apply (fun x => (F x : ℂ))) k
  rw [ZMod.invDFT_apply] at hi
  simp only [smul_eq_mul, mul_sum] at hi
  rw [← hi]
  refine sum_congr rfl fun j _ => ?_
  rw [coeff_complex F hF]
  ring

lemma coeff_parseval (F : ZMod p → ℝ) (hF : Function.Even F) :
    (∑ j, coeff F j ^ 2) = (∑ x, F x ^ 2) / p := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have he : Function.Even (fun x => (F x : ℂ)) := fun x => congrArg (fun t : ℝ => (t : ℂ)) (hF x)
  have h := sum_dft_mul (fun x => (F x : ℂ))
    (ZMod.dft (fun x => (F x : ℂ)))
  simp only [ZMod.dft_dft, smul_eq_mul] at h
  have hFe (x : ZMod p) : F (-x) = F x := hF x
  simp only [hFe] at h
  have hc : (∑ j, (coeff F j : ℂ) ^ 2) = (∑ x, (F x : ℂ) ^ 2) / p := by
    simp_rw [coeff_complex F hF, mul_pow]
    rw [← mul_sum]
    have hs : (∑ j, ZMod.dft (fun x => (F x : ℂ)) j ^ 2) =
        (p : ℂ) * ∑ x, (F x : ℂ) ^ 2 := by
      calc
        _ = ∑ j, ZMod.dft (fun x => (F x : ℂ)) j *
            ZMod.dft (fun x => (F x : ℂ)) j := by simp only [pow_two]
        _ = ∑ x, (F x : ℂ) * ((p : ℂ) * (F x : ℂ)) := h
        _ = ∑ x, (p : ℂ) * (F x : ℂ) ^ 2 := by
          apply sum_congr rfl
          intro x _
          ring
        _ = _ := (mul_sum _ _ _).symm
    rw [hs]
    field_simp
  exact_mod_cast hc

/-- The positive real frequency associated to a Fourier index (zero at `j=0`). -/
def frequency (j : ZMod p) : ℝ := 2 * Real.pi * j.val / p

omit [NeZero p] in
lemma frequency_nonneg (j : ZMod p) : 0 ≤ frequency j := by
  unfold frequency
  positivity

lemma stdAddChar_mul_int_re (j : ZMod p) (k : ℤ) :
    (ZMod.stdAddChar (j * (k : ZMod p))).re =
      Real.cos ((k : ℝ) * frequency j) := by
  have hj : (((j.val : ℤ) * k : ℤ) : ZMod p) = j * (k : ZMod p) := by
    simp
  rw [← hj, ZMod.stdAddChar_coe]
  have he : 2 * (Real.pi : ℂ) * Complex.I * (((j.val : ℤ) * k : ℤ) : ℂ) / p =
      (((k : ℝ) * frequency j : ℝ) : ℂ) * Complex.I := by
    simp only [frequency]
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I_re]

lemma coeff_inversion (F : ZMod p → ℝ) (hF : Function.Even F) (k : ℤ) :
    F (k : ZMod p) = ∑ j, coeff F j * Real.cos ((k : ℝ) * frequency j) := by
  have h := congrArg Complex.re (coeff_inversion_complex F hF (k : ZMod p))
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, stdAddChar_mul_int_re] at h
  simpa only [mul_comm] using h

lemma coeff_sum_zero (F : ZMod p → ℝ) (hF : Function.Even F) (h0 : F 0 = 0) :
    ∑ j, coeff F j = 0 := by
  have h := coeff_inversion F hF 0
  simpa [h0] using h.symm

lemma coeff_mass_bound (F : ZMod p → ℝ) (hF : Function.Even F)
    (hbound : ∀ x, |F x| ≤ 3) :
    ∑ j, |coeff F j| ≤ 3 * Real.sqrt (p : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hsq : (∑ j, |coeff F j| ^ 2) ≤ 9 := by
    simp only [sq_abs]
    rw [coeff_parseval F hF]
    apply (div_le_iff₀ hp).mpr
    calc
      ∑ x, F x ^ 2 ≤ ∑ x : ZMod p, (9 : ℝ) := by
        apply sum_le_sum
        intro x _
        have hx := hbound x
        nlinarith [sq_abs (F x), abs_nonneg (F x)]
      _ = 9 * p := by simp [mul_comm]
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset (ZMod p))
    (fun _ => (1 : ℝ)) (fun j => |coeff F j|)
  simp only [one_mul, one_pow, sum_const, card_univ, ZMod.card,
    nsmul_eq_mul, mul_one] at hcs
  have hnonneg : 0 ≤ ∑ j, |coeff F j| := sum_nonneg fun _ _ => abs_nonneg _
  have hsqrt := Real.sq_sqrt (le_of_lt hp)
  have hsqrtnonneg := Real.sqrt_nonneg (p : ℝ)
  nlinarith [mul_le_mul_of_nonneg_left hsq (le_of_lt hp)]

/-- The periodic table agrees with the paper's target on the centered interval. -/
def table (n : ℕ) (x : ZMod (2 * n + 1)) : ℝ := f x.valMinAbs

lemma table_even (n : ℕ) : Function.Even (table n) := by
  intro x
  have hi : 2 * x.val ≠ 2 * n + 1 := by omega
  simp only [table, ZMod.valMinAbs_neg_of_ne_half hi, f_even]

lemma table_zero (n : ℕ) : table n 0 = 0 := by simp [table, f_zero]

lemma table_bound (n : ℕ) (x : ZMod (2 * n + 1)) : |table n x| ≤ 3 := by
  unfold table
  rw [abs_of_nonneg (f_nonneg _)]
  exact f_le_three _

lemma table_int (n : ℕ) (k : ℤ) (hk : |k| ≤ n) :
    table n (k : ZMod (2 * n + 1)) = f k := by
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  unfold table
  congr 1
  apply (ZMod.valMinAbs_spec _ _).mpr
  refine ⟨rfl, ?_⟩
  have hb := abs_le.mp hk
  constructor <;> push_cast <;> omega

/-- Positive Fourier–Hahn coefficients. -/
def splitPos (F : ZMod p → ℝ) (x : ℝ) : ℝ :=
  ∑ j, max (-coeff F j) 0 * (1 - Real.cos (x * frequency j))

/-- Negative Fourier–Hahn coefficients. -/
def splitNeg (F : ZMod p → ℝ) (x : ℝ) : ℝ :=
  ∑ j, max (coeff F j) 0 * (1 - Real.cos (x * frequency j))

lemma positiveParts_sub (c : ℝ) : max (-c) 0 - max c 0 = -c := by
  by_cases h : 0 ≤ c
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · have hc := le_of_not_ge h
    rw [max_eq_right hc, max_eq_left (neg_nonneg.mpr hc)]
    ring

lemma positiveParts_add (c : ℝ) : max (-c) 0 + max c 0 = |c| := by
  by_cases h : 0 ≤ c
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]
    ring
  · have hc := le_of_not_ge h
    rw [max_eq_right hc, max_eq_left (neg_nonneg.mpr hc), abs_of_nonpos hc]
    ring

lemma split_exact (F : ZMod p → ℝ) (hF : Function.Even F) (h0 : F 0 = 0)
    (k : ℤ) : splitPos F k - splitNeg F k = F (k : ZMod p) := by
  unfold splitPos splitNeg
  rw [← sum_sub_distrib]
  simp_rw [← sub_mul, positiveParts_sub]
  have hsum := coeff_sum_zero F hF h0
  have hinv := coeff_inversion F hF k
  calc
    (∑ j, -coeff F j * (1 - Real.cos ((k : ℝ) * frequency j))) =
        (∑ j, coeff F j * Real.cos ((k : ℝ) * frequency j)) - ∑ j, coeff F j := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro j _
      ring
    _ = F (k : ZMod p) := by rw [hsum, sub_zero, ← hinv]

lemma split_envelope (F : ZMod p → ℝ) (hF : Function.Even F)
    (hbound : ∀ x, |F x| ≤ 3) (x : ℝ) :
    splitPos F x + splitNeg F x ≤ 6 * Real.sqrt (p : ℝ) := by
  unfold splitPos splitNeg
  rw [← sum_add_distrib]
  simp_rw [← add_mul, positiveParts_add]
  calc
    _ ≤ ∑ j, 2 * |coeff F j| := by
      apply sum_le_sum
      intro j _
      have hcos := Real.neg_one_le_cos (x * frequency j)
      nlinarith [abs_nonneg (coeff F j)]
    _ = 2 * ∑ j, |coeff F j| := (mul_sum _ _ _).symm
    _ ≤ 6 * Real.sqrt (p : ℝ) := by
      have h := coeff_mass_bound F hF hbound
      linarith

lemma splitPos_zero (F : ZMod p → ℝ) : splitPos F 0 = 0 := by simp [splitPos]

lemma splitNeg_zero (F : ZMod p → ℝ) : splitNeg F 0 = 0 := by simp [splitNeg]

/-- The explicit Fourier–Hahn pair has the paper's exact cancellation envelope. -/
theorem split_admissible (n : ℕ) :
    AdmissibleSplit (RestrictInt (splitPos (table n)))
      (RestrictInt (splitNeg (table n))) f n 0
      (6 * Real.sqrt (2 * (n : ℝ) + 1)) := by
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  constructor
  · intro k hk
    change |splitPos (table n) k - splitNeg (table n) k - f k| ≤ 0 * f k
    rw [split_exact (table n) (table_even n) (table_zero n), table_int n k hk]
    simp
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp [RestrictInt, splitPos_zero, splitNeg_zero, f_zero]
    · have henv := split_envelope (table n) (table_even n) (table_bound n) (k : ℝ)
      have hc : 0 ≤ 6 * Real.sqrt (2 * (n : ℝ) + 1) := by positivity
      have hf := mul_le_mul_of_nonneg_left (f_ge_one_of_ne_zero hk0) hc
      have he : splitPos (table n) k + splitNeg (table n) k ≤
          6 * Real.sqrt (2 * (n : ℝ) + 1) := by simpa using henv
      exact he.trans (by simpa using hf)

lemma isLSym_splitPos (F : ZMod p → ℝ) : IsLSym (splitPos F) := by
  exact Paper02.LSym.isLSym_atomic_sum frequency (fun j => max (-coeff F j) 0)
    frequency_nonneg (fun _ => le_max_right _ _)

lemma isLSym_splitNeg (F : ZMod p → ℝ) : IsLSym (splitNeg F) := by
  exact Paper02.LSym.isLSym_atomic_sum frequency (fun j => max (coeff F j) 0)
    frequency_nonneg (fun _ => le_max_right _ _)

/-- **Proposition 3.3.** For every cutoff `n ≥ 1`, finite positive atomic
Lévy exponents give an exact split with envelope `6√(2n+1) f`. -/
theorem prop_3_3 (n : ℕ) (hn : 1 ≤ n) :
    ∃ gpos gneg : ℝ → ℝ,
      AdmissibleLSymPair gpos gneg f n 0 (6 * Real.sqrt (2 * (n : ℝ) + 1)) := by
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  exact ⟨splitPos (table n), splitNeg (table n),
    isLSym_splitPos (table n), isLSym_splitNeg (table n), split_admissible n⟩

end Paper02.Fourier
