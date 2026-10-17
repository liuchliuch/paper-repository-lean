import Paper26.PositiveLossBridge
import Paper26.ShellAccounting
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Binomial

/-!
# Mass rescaling for the collective submatrix routine (Proposition 5.5)

All deterministic errors below are entrywise Frobenius squares of actual
complex matrices. The finite-mixture layer keeps the retained-copy count and
conditional estimator laws explicit; it does not assume a final submatrix
risk or confidence theorem.

`BinomialMomentsInput` records only the native binomial count's standard first
and centered second moments. The finite conditional-estimator bound is the raw
Equation (48), not a final risk bound. This module proves the finite-mixture
routine and its actual integral/Markov bounds. Realizing these laws as the
continuous-outcome O'Donnell--Wright collective POVM after a block-projection
instrument, and independent-batch amplification, are separate obligations.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
namespace Paper26.CollectiveSubmatrix
open MeasureTheory
open QuantumModel ShellAccounting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frobeniusSq_diagonal (a : ι → ℝ) :
    frobeniusSq (Normalization.diagonalMatrix a) = ∑ i, a i ^ 2 := by
  rw [frobeniusSq_eq_trace, Normalization.diagonalMatrix_conjTranspose]
  unfold Normalization.diagonalMatrix
  rw [Matrix.diagonal_mul_diagonal]
  simp [Matrix.trace_diagonal, Complex.mul_re, pow_two]


/-- A PSD block's true Frobenius square is at most its squared mass. -/
theorem psd_frobeniusSq_le_mass_sq (R : Matrix ι ι ℂ) (hR : R.PosSemidef) :
    frobeniusSq R ≤ (Matrix.trace R).re ^ 2 := by
  let U := hR.1.eigenvectorUnitary
  let a := hR.1.eigenvalues
  have he : R = Normalization.conjugate (U : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix a) := by
    simpa only [U, a, Normalization.conjugate, Normalization.diagonalMatrix,
      Function.comp_def, Matrix.star_eq_conjTranspose] using hR.1.spectral_theorem
  have hf : frobeniusSq R = ∑ i, a i ^ 2 := by
    rw [he]
    unfold Normalization.conjugate
    have hus : (U : Matrix ι ι ℂ)ᴴ * ((U : Matrix ι ι ℂ)ᴴ)ᴴ = 1 := by
      simpa only [Matrix.conjTranspose_conjTranspose] using (PositiveLossBridge.unitary_left U)
    rw [frobeniusSq_mul_unitary _ _ hus,
      frobeniusSq_unitary_mul _ _ (PositiveLossBridge.unitary_left U), frobeniusSq_diagonal]
  have ht : (Matrix.trace R).re = ∑ i, a i := by
    have h := congrArg Complex.re hR.1.trace_eq_sum_eigenvalues
    simpa only [a, Complex.re_sum, RCLike.ofReal_re] using h
  rw [hf, ht]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hR.eigenvalues_nonneg i)

lemma density_frobeniusSq_le_one (τ : Density ι) : frobeniusSq τ.matrix ≤ 1 := by
  have h := psd_frobeniusSq_le_mass_sq τ.matrix τ.positive
  simpa only [τ.trace_one, Complex.one_re, one_pow] using h

/-- The zero-copy branch applies to every actual PSD block, including mass 0. -/
theorem zero_estimate_suffices (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (w W η : ℝ) (hmass : (Matrix.trace R).re = w)
    (hw : 0 ≤ w) (hwW : w ≤ W) (hW : W ^ 2 ≤ η) :
    (0 : Matrix ι ι ℂ).PosSemidef ∧ frobeniusSq (0 - R) ≤ η := by
  refine ⟨Matrix.PosSemidef.zero, ?_⟩
  have hf := psd_frobeniusSq_le_mass_sq R hR
  rw [hmass] at hf
  have hz : frobeniusSq (0 - R) = frobeniusSq R := by simp [frobeniusSq]
  rw [hz]
  have hW0 : 0 ≤ W := hw.trans hwW
  nlinarith

omit [DecidableEq ι] in
lemma frobeniusSq_real_smul (a : ℝ) (A : Matrix ι ι ℂ) :
    frobeniusSq ((a : ℂ) • A) = a ^ 2 * frobeniusSq A := by
  simp only [frobeniusSq, Matrix.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [Finset.mul_sum]

omit [DecidableEq ι] in
lemma frobeniusSq_add_le (A B : Matrix ι ι ℂ) :
    frobeniusSq (A + B) ≤ 2 * frobeniusSq A + 2 * frobeniusSq B := by
  unfold frobeniusSq
  simp only [Matrix.add_apply, ← Complex.normSq_eq_norm_sq]
  calc
    _ ≤ ∑ i, ∑ j, (2 * Complex.normSq (A i j) + 2 * Complex.normSq (B i j)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact SpectralLoss.normSq_add_le _ _
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

omit [DecidableEq ι] in
/-- The mass error and normalized-state error are separated in actual matrices. -/
theorem rescaling_error (τhat τ : Density ι) (a w : ℝ) :
    frobeniusSq ((a : ℂ) • τhat.matrix - (w : ℂ) • τ.matrix) ≤
      2 * a ^ 2 * frobeniusSq (τhat.matrix - τ.matrix) +
        2 * (a - w) ^ 2 * frobeniusSq τ.matrix := by
  have he : (a : ℂ) • τhat.matrix - (w : ℂ) • τ.matrix =
      (a : ℂ) • (τhat.matrix - τ.matrix) + ((a - w : ℝ) : ℂ) • τ.matrix := by
    push_cast
    simp only [smul_sub, sub_smul]
    abel
  rw [he]
  have hl := frobeniusSq_add_le ((a : ℂ) • (τhat.matrix - τ.matrix))
    (((a - w : ℝ) : ℂ) • τ.matrix)
  rw [frobeniusSq_real_smul, frobeniusSq_real_smul] at hl
  simpa only [mul_assoc] using hl

omit [DecidableEq ι] in
/-- Rescaled density outputs are always PSD, including a zero retained count. -/
theorem rescaled_posSemidef (τhat : Density ι) (a : ℝ) (ha : 0 ≤ a) :
    ((a : ℂ) • τhat.matrix).PosSemidef :=
  τhat.positive.smul (RCLike.ofReal_nonneg.mpr ha)

/-- A finite probability law, with its normalization kept explicit. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ y, 0 ≤ weight y
  sum_one : ∑ y, weight y = 1

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

def expectation (p : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ y, p.weight y * f y

lemma expectation_mono (p : FiniteLaw Ω) {f g : Ω → ℝ} (h : ∀ y, f y ≤ g y) :
    p.expectation f ≤ p.expectation g :=
  Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (h y) (p.nonneg y))

lemma expectation_add (p : FiniteLaw Ω) (f g : Ω → ℝ) :
    p.expectation (fun y => f y + g y) = p.expectation f + p.expectation g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

lemma expectation_const_mul (p : FiniteLaw Ω) (a : ℝ) (f : Ω → ℝ) :
    p.expectation (fun y => a * f y) = a * p.expectation f := by
  simp only [expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma expectation_const (p : FiniteLaw Ω) (a : ℝ) : p.expectation (fun _ => a) = a := by
  rw [expectation, ← Finset.sum_mul, p.sum_one, one_mul]


/-- The finite law is an actual probability mass function. -/
def toPMF (p : FiniteLaw Ω) : PMF Ω :=
  PMF.ofFintype (fun y => ENNReal.ofReal (p.weight y)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => p.nonneg y), p.sum_one]
    norm_num)

@[simp] lemma toPMF_apply (p : FiniteLaw Ω) (y : Ω) :
    p.toPMF y = ENNReal.ofReal (p.weight y) := rfl

/-- Finite expectations used here are genuine integrals under the actual
probability measure, not formal symbols for an unconstructed law. -/
theorem expectation_eq_integral [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) :
    p.expectation f = ∫ y, f y ∂p.toPMF.toMeasure := by
  rw [PMF.integral_eq_sum]
  simp only [expectation, toPMF_apply, ENNReal.toReal_ofReal (p.nonneg _), smul_eq_mul]


/-- The actual finite joint law obtained by first drawing the retained count
and then drawing the estimator output conditional on that count. -/
def mixture {M : Type*} [Fintype M] {Y : M → Type*} [∀ m, Fintype (Y m)]
    (p : FiniteLaw M) (q : ∀ m, FiniteLaw (Y m)) : FiniteLaw (Σ m, Y m) where
  weight z := p.weight z.1 * (q z.1).weight z.2
  nonneg z := mul_nonneg (p.nonneg z.1) ((q z.1).nonneg z.2)
  sum_one := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum, (q _).sum_one, mul_one]
    exact p.sum_one

lemma mixture_expectation {M : Type*} [Fintype M] {Y : M → Type*} [∀ m, Fintype (Y m)]
    (p : FiniteLaw M) (q : ∀ m, FiniteLaw (Y m)) (f : (Σ m, Y m) → ℝ) :
    (mixture p q).expectation f = p.expectation (fun m => (q m).expectation (fun y => f ⟨m, y⟩)) := by
  simp only [expectation, mixture, Fintype.sum_sigma, Finset.mul_sum, mul_assoc]


/-- Read a genuine finite PMF as the real weights used by matrix expectations. -/
def ofPMF (p : PMF Ω) : FiniteLaw Ω where
  weight y := (p y).toReal
  nonneg y := ENNReal.toReal_nonneg
  sum_one := by
    have hs : (∑ y, p y) = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    calc
      _ = (∑ y, p y).toReal := (ENNReal.toReal_sum (fun y _ => p.apply_ne_top y)).symm
      _ = 1 := by rw [hs]; norm_num

@[simp] lemma ofPMF_toPMF (p : PMF Ω) : (ofPMF p).toPMF = p := by
  ext y
  simp only [toPMF_apply, ofPMF, ENNReal.ofReal_toReal (p.apply_ne_top y)]


/-- Real probability of a finite event under the actual finite law. -/
def probability (p : FiniteLaw Ω) (S : Set Ω) : ℝ := by
  classical
  exact ∑ y, if y ∈ S then p.weight y else 0

lemma probability_compl (p : FiniteLaw Ω) (S : Set Ω) :
    p.probability S + p.probability Sᶜ = 1 := by
  classical
  rw [probability, probability, ← Finset.sum_add_distrib, ← p.sum_one]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y ∈ S <;> simp [hy]

lemma probability_eq_measure [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : FiniteLaw Ω) (S : Set Ω) :
    p.toPMF.toMeasure S = ENNReal.ofReal (p.probability S) := by
  classical
  rw [PMF.toMeasure_apply_fintype, probability,
    ENNReal.ofReal_sum_of_nonneg (by intro y _; split_ifs <;> [exact p.nonneg y; exact le_rfl])]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y ∈ S <;> simp [hy, Set.indicator, toPMF_apply]

/-- Elementary finite Markov inequality proved by summing each weighted term. -/
theorem markov (p : FiniteLaw Ω) (f : Ω → ℝ) (hf : ∀ y, 0 ≤ f y)
    (η : ℝ) (hη : 0 < η) : p.probability {y | η < f y} ≤ p.expectation f / η := by
  classical
  have ht : η * p.probability {y | η < f y} ≤ p.expectation f := by
    rw [probability, Finset.mul_sum, expectation]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : η < f y
    · simp only [Set.mem_setOf_eq, hy, if_true]
      nlinarith [mul_le_mul_of_nonneg_left hy.le (p.nonneg y)]
    · simp only [Set.mem_setOf_eq, hy, if_false, mul_zero]
      exact mul_nonneg (p.nonneg y) (hf y)
  exact (le_div_iff₀ hη).mpr (by simpa only [mul_comm] using ht)

theorem three_quarter_success (p : FiniteLaw Ω) (f : Ω → ℝ) (hf : ∀ y, 0 ≤ f y)
    (η : ℝ) (hη : 0 < η) (hE : p.expectation f ≤ η / 4) :
    3 / 4 ≤ p.probability {y | f y ≤ η} := by
  have hm := p.markov f hf η hη
  have hd : p.expectation f / η ≤ 1 / 4 := by
    apply (div_le_iff₀ hη).mpr
    linarith
  have hc := p.probability_compl {y | η < f y}
  have he : ({y | η < f y}ᶜ : Set Ω) = {y | f y ≤ η} := by
    ext y
    simp
  rw [he] at hc
  linarith

end FiniteLaw

/-- Actual conditional estimator error before averaging over the count. -/
theorem conditional_rescaling_bound {Ω : Type*} [Fintype Ω] (p : FiniteLaw Ω)
    (τ : Density ι) (τhat : Ω → Density ι) (a w : ℝ) :
    p.expectation (fun y => frobeniusSq ((a : ℂ) • (τhat y).matrix - (w : ℂ) • τ.matrix)) ≤
      2 * a ^ 2 * p.expectation (fun y => frobeniusSq ((τhat y).matrix - τ.matrix)) +
        2 * (a - w) ^ 2 := by
  have hl := p.expectation_mono (fun y => rescaling_error (τhat y) τ a w)
  rw [FiniteLaw.expectation_add, FiniteLaw.expectation_const_mul,
    FiniteLaw.expectation_const] at hl
  have ht := density_frobeniusSq_le_one τ
  have hc : 0 ≤ 2 * (a - w) ^ 2 := by positivity
  nlinarith


/-- Conditional use of the raw O'Donnell--Wright `4k/M` estimate. At `M=0`
the matrix output is exactly zero and no estimator bound is required. -/
theorem conditional_count_risk {Ω : Type*} [Fintype Ω]
    (N : ℕ) (hN : 0 < N) (m : Fin (N + 1)) (p : FiniteLaw Ω)
    (τ : Density ι) (τhat : Ω → Density ι) (w : ℝ)
    (hOW : 0 < m.val → p.expectation (fun y => frobeniusSq ((τhat y).matrix - τ.matrix)) ≤
      4 * Fintype.card ι / (m.val : ℝ)) :
    p.expectation (fun y => frobeniusSq
      ((((m.val : ℝ) / N : ℝ) : ℂ) • (τhat y).matrix - (w : ℂ) • τ.matrix)) ≤
      8 * Fintype.card ι * m.val / (N : ℝ) ^ 2 + 2 * ((m.val : ℝ) / N - w) ^ 2 := by
  have hl := conditional_rescaling_bound p τ τhat ((m.val : ℝ) / N) w
  by_cases hm : m.val = 0
  · simpa only [hm, Nat.cast_zero, zero_div, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_mul, zero_add] using hl
  · have hmpos : 0 < m.val := Nat.pos_of_ne_zero hm
    have hc : 0 ≤ 2 * ((m.val : ℝ) / N) ^ 2 := by positivity
    have how := mul_le_mul_of_nonneg_left (hOW hmpos) hc
    have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
    have hm0 : (m.val : ℝ) ≠ 0 := by exact_mod_cast hm
    have he : 2 * ((m.val : ℝ) / N) ^ 2 * (4 * Fintype.card ι / (m.val : ℝ)) =
        8 * Fintype.card ι * m.val / (N : ℝ) ^ 2 := by
      field_simp
      ring
    rw [he] at how
    exact hl.trans (add_le_add_right how _)

/-- Normalized count variance is derived from the raw centered count moment;
this step is part of the proof, not part of the binomial input. -/
lemma normalized_count_variance (N : ℕ) (hN : 0 < N)
    (p : FiniteLaw (Fin (N + 1))) (w : ℝ)
    (hvar : p.expectation (fun m => ((m.val : ℝ) - N * w) ^ 2) = N * w * (1 - w)) :
    p.expectation (fun m => ((m.val : ℝ) / N - w) ^ 2) = w * (1 - w) / N := by
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hp : (fun m : Fin (N + 1) => ((m.val : ℝ) / N - w) ^ 2) =
      fun m => (1 / (N : ℝ) ^ 2) * ((m.val : ℝ) - N * w) ^ 2 := by
    funext m
    field_simp
  rw [hp, FiniteLaw.expectation_const_mul, hvar]
  field_simp

/-- Finite-mixture expectation bound accounting for every rejected full copy.
The only estimator hypothesis is the raw trace-one `4k/M` conditional bound;
count inputs are only its first and centered second moments. -/
theorem finite_mixture_risk (N : ℕ) (hN : 0 < N)
    (p : FiniteLaw (Fin (N + 1))) (w : ℝ)
    (hmean : p.expectation (fun m => (m.val : ℝ)) = N * w)
    (hvar : p.expectation (fun m => ((m.val : ℝ) - N * w) ^ 2) = N * w * (1 - w))
    {Y : Fin (N + 1) → Type*} [∀ m, Fintype (Y m)]
    (q : ∀ m, FiniteLaw (Y m)) (τ : Density ι) (τhat : ∀ m, Y m → Density ι)
    (hOW : ∀ m, 0 < m.val →
      (q m).expectation (fun y => frobeniusSq ((τhat m y).matrix - τ.matrix)) ≤
        4 * Fintype.card ι / (m.val : ℝ)) :
    (FiniteLaw.mixture p q).expectation (fun z => frobeniusSq
      ((((z.1.val : ℝ) / N : ℝ) : ℂ) • (τhat z.1 z.2).matrix - (w : ℂ) • τ.matrix)) ≤
        2 * (4 * Fintype.card ι + 1) * w / N := by
  rw [FiniteLaw.mixture_expectation]
  have hl := p.expectation_mono (fun m => conditional_count_risk N hN m (q m) τ
    (τhat m) w (hOW m))
  have he : p.expectation (fun m =>
      8 * Fintype.card ι * m.val / (N : ℝ) ^ 2 + 2 * ((m.val : ℝ) / N - w) ^ 2) =
      8 * Fintype.card ι / (N : ℝ) ^ 2 * (N * w) + 2 * (w * (1 - w) / N) := by
    rw [FiniteLaw.expectation_add]
    have hm : (fun m : Fin (N + 1) => 8 * Fintype.card ι * m.val / (N : ℝ) ^ 2) =
        fun m => (8 * Fintype.card ι / (N : ℝ) ^ 2) * m.val := by
      funext m
      ring
    rw [hm, FiniteLaw.expectation_const_mul, hmean,
      FiniteLaw.expectation_const_mul, normalized_count_variance N hN p w hvar]
  rw [he] at hl
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hn0 : (N : ℝ) ≠ 0 := ne_of_gt hn
  have hsmall : 8 * Fintype.card ι / (N : ℝ) ^ 2 * (N * w) + 2 * (w * (1 - w) / N) ≤
      2 * (4 * Fintype.card ι + 1) * w / N := by
    apply (le_div_iff₀ hn).mpr
    field_simp
    nlinarith [sq_nonneg w]
  exact hl.trans hsmall


/-- The count law is the native binomial PMF, not an abstract loss distribution. -/
def binomialLaw (N : ℕ) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) : FiniteLaw (Fin (N + 1)) :=
  FiniteLaw.ofPMF (PMF.binomial ⟨w, hw⟩ (by exact_mod_cast hw1) N)

/-- Exact generic classical binomial moment input. Only the native count's
first moment and centered second moment are fields; normalization follows from
its actual PMF. No estimator, matrix, or submatrix-risk conclusion occurs. -/
structure BinomialMomentsInput : Prop where
  first : ∀ (N : ℕ) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1),
    (binomialLaw N w hw hw1).expectation (fun m => (m.val : ℝ)) = N * w
  centered_second : ∀ (N : ℕ) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1),
    (binomialLaw N w hw hw1).expectation (fun m => ((m.val : ℝ) - N * w) ^ 2) =
      N * w * (1 - w)

/-- Proposition 5.5's mass-rescaled risk under the actual finite binomial
mixture. The exact `M=0` branch is retained by the scaled matrix definition. -/
theorem binomial_mixture_risk (B : BinomialMomentsInput)
    (N : ℕ) (hN : 0 < N) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    {Y : Fin (N + 1) → Type*} [∀ m, Fintype (Y m)]
    (q : ∀ m, FiniteLaw (Y m)) (τ : Density ι) (τhat : ∀ m, Y m → Density ι)
    (hOW : ∀ m, 0 < m.val →
      (q m).expectation (fun y => frobeniusSq ((τhat m y).matrix - τ.matrix)) ≤
        4 * Fintype.card ι / (m.val : ℝ)) :
    (FiniteLaw.mixture (binomialLaw N w hw hw1) q).expectation (fun z => frobeniusSq
      ((((z.1.val : ℝ) / N : ℝ) : ℂ) • (τhat z.1 z.2).matrix - (w : ℂ) • τ.matrix)) ≤
        2 * (4 * Fintype.card ι + 1) * w / N :=
  finite_mixture_risk N hN _ w (B.first N w hw hw1) (B.centered_second N w hw hw1)
    q τ τhat hOW

/-- The finite-mixture calculation is the actual expected Frobenius error
under the joint count/conditional-output probability measure. -/
theorem binomial_mixture_integral (B : BinomialMomentsInput)
    (N : ℕ) (hN : 0 < N) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    {Y : Fin (N + 1) → Type*} [∀ m, Fintype (Y m)]
    [MeasurableSpace (Σ m, Y m)] [MeasurableSingletonClass (Σ m, Y m)]
    (q : ∀ m, FiniteLaw (Y m)) (τ : Density ι) (τhat : ∀ m, Y m → Density ι)
    (hOW : ∀ m, 0 < m.val →
      (q m).expectation (fun y => frobeniusSq ((τhat m y).matrix - τ.matrix)) ≤
        4 * Fintype.card ι / (m.val : ℝ)) :
    (∫ z, frobeniusSq
      ((((z.1.val : ℝ) / N : ℝ) : ℂ) • (τhat z.1 z.2).matrix - (w : ℂ) • τ.matrix)
      ∂(FiniteLaw.mixture (binomialLaw N w hw hw1) q).toPMF.toMeasure) ≤
        2 * (4 * Fintype.card ι + 1) * w / N := by
  rw [← FiniteLaw.expectation_eq_integral]
  exact binomial_mixture_risk B N hN w hw hw1 q τ τhat hOW

/-- Every actual PSD block of positive mass has an actual normalized density. -/
def normalizedBlock (R : Matrix ι ι ℂ) (hR : R.PosSemidef) (w : ℝ)
    (hmass : (Matrix.trace R).re = w) (hw : 0 < w) : Density ι where
  matrix := ((w⁻¹ : ℝ) : ℂ) • R
  positive := hR.smul (RCLike.ofReal_nonneg.mpr (inv_pos.mpr hw).le)
  trace_one := by
    rw [Matrix.trace_smul]
    have ht : Matrix.trace R = (w : ℂ) := by
      apply Complex.ext
      · simpa only [Complex.ofReal_re] using hmass
      · simpa only [Complex.ofReal_im, Complex.zero_im] using hR.trace_nonneg.2.symm
    rw [ht]
    change (((w⁻¹ : ℝ) : ℂ)) * (w : ℂ) = 1
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hw), Complex.ofReal_one]

omit [DecidableEq ι] in
lemma normalizedBlock_rescale (R : Matrix ι ι ℂ) (hR : R.PosSemidef) (w : ℝ)
    (hmass : (Matrix.trace R).re = w) (hw : 0 < w) :
    (w : ℂ) • (normalizedBlock R hR w hmass hw).matrix = R := by
  change (w : ℂ) • (((w⁻¹ : ℝ) : ℂ) • R) = R
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hw), Complex.ofReal_one, one_smul]

omit [DecidableEq ι] in
lemma psd_zero_mass (R : Matrix ι ι ℂ) (hR : R.PosSemidef) (hmass : (Matrix.trace R).re = 0) :
    R = 0 := by
  apply hR.trace_eq_zero_iff.mp
  apply Complex.ext hmass
  exact hR.trace_nonneg.2.symm


/-- The finite binomial routine expressed against an arbitrary actual PSD
block, normalized internally rather than assuming its normalized form. -/
theorem actual_block_integral (B : BinomialMomentsInput)
    (R : Matrix ι ι ℂ) (hR : R.PosSemidef) (w : ℝ) (hmass : (Matrix.trace R).re = w)
    (hw : 0 < w) (hw1 : w ≤ 1) (N : ℕ) (hN : 0 < N)
    {Y : Fin (N + 1) → Type*} [∀ m, Fintype (Y m)]
    [MeasurableSpace (Σ m, Y m)] [MeasurableSingletonClass (Σ m, Y m)]
    (q : ∀ m, FiniteLaw (Y m)) (τhat : ∀ m, Y m → Density ι)
    (hOW : ∀ m, 0 < m.val →
      (q m).expectation (fun y => frobeniusSq
        ((τhat m y).matrix - (normalizedBlock R hR w hmass hw).matrix)) ≤
          4 * Fintype.card ι / (m.val : ℝ)) :
    (∀ z : Σ m, Y m, ((((z.1.val : ℝ) / N : ℝ) : ℂ) • (τhat z.1 z.2).matrix).PosSemidef) ∧
      (∫ z, frobeniusSq
        ((((z.1.val : ℝ) / N : ℝ) : ℂ) • (τhat z.1 z.2).matrix - R)
        ∂(FiniteLaw.mixture (binomialLaw N w hw.le hw1) q).toPMF.toMeasure) ≤
          2 * (4 * Fintype.card ι + 1) * w / N := by
  constructor
  · intro z
    exact rescaled_posSemidef _ _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · have h := binomial_mixture_integral B N hN w hw.le hw1 q
      (normalizedBlock R hR w hmass hw) τhat hOW
    rwa [normalizedBlock_rescale] at h

/-- One actual finite-law batch has success at least `3/4` when its full-copy
count meets the explicit unrounded cost inequality. No amplification or
Chernoff theorem is included here. -/
theorem finite_batch_success (B : BinomialMomentsInput)
    (N : ℕ) (hN : 0 < N) (w W η : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hwW : w ≤ W) (hη : 0 < η)
    (hcost : 8 * (4 * Fintype.card ι + 1) * W ≤ η * N)
    {Y : Fin (N + 1) → Type*} [∀ m, Fintype (Y m)]
    (q : ∀ m, FiniteLaw (Y m)) (τ : Density ι) (τhat : ∀ m, Y m → Density ι)
    (hOW : ∀ m, 0 < m.val →
      (q m).expectation (fun y => frobeniusSq ((τhat m y).matrix - τ.matrix)) ≤
        4 * Fintype.card ι / (m.val : ℝ)) :
    3 / 4 ≤ (FiniteLaw.mixture (binomialLaw N w hw hw1) q).probability
      {z | frobeniusSq
        ((((z.1.val : ℝ) / N : ℝ) : ℂ) • (τhat z.1 z.2).matrix - (w : ℂ) • τ.matrix) ≤ η} := by
  have hr := binomial_mixture_risk B N hN w hw hw1 q τ τhat hOW
  apply FiniteLaw.three_quarter_success _ _ (fun z => frobeniusSq_nonneg _) η hη
  apply hr.trans
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  have hc : 0 ≤ 4 * (Fintype.card ι : ℝ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hwW hc]


/-- The actual matrix output of the finite routine, using the observed count
rather than the unknown block mass. -/
def rescaledOutput (N : ℕ) {Y : Fin (N + 1) → Type*}
    (τhat : ∀ m, Y m → Density ι) (z : Σ m, Y m) : Matrix ι ι ℂ :=
  ((((z.1.val : ℝ) / N : ℝ) : ℂ) • (τhat z.1 z.2).matrix)

omit [DecidableEq ι] in
lemma rescaledOutput_posSemidef (N : ℕ) {Y : Fin (N + 1) → Type*}
    (τhat : ∀ m, Y m → Density ι) (z : Σ m, Y m) :
    (rescaledOutput N τhat z).PosSemidef :=
  rescaled_posSemidef _ _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

omit [DecidableEq ι] in
lemma rescaledOutput_zero_count (N : ℕ) {Y : Fin (N + 1) → Type*}
    (τhat : ∀ m, Y m → Density ι) (z : Σ m, Y m) (hm : z.1.val = 0) :
    rescaledOutput N τhat z = 0 := by
  simp [rescaledOutput, hm]

/-- Zero-mass blocks are exact under the native binomial count law, without
any O'Donnell--Wright hypothesis at the impossible positive retained counts. -/
theorem zero_mass_mixture_error (N : ℕ)
    {Y : Fin (N + 1) → Type*} [∀ m, Fintype (Y m)]
    (q : ∀ m, FiniteLaw (Y m)) (τhat : ∀ m, Y m → Density ι) :
    (FiniteLaw.mixture (binomialLaw N 0 (by norm_num) (by norm_num)) q).expectation
      (fun z => frobeniusSq (rescaledOutput N τhat z)) = 0 := by
  unfold FiniteLaw.expectation
  apply Finset.sum_eq_zero
  intro z _
  by_cases hm : z.1.val = 0
  · change _ * frobeniusSq (rescaledOutput N τhat z) = 0
    rw [rescaledOutput_zero_count N τhat z hm]
    simp [frobeniusSq]
  · have hz : (binomialLaw N 0 (by norm_num) (by norm_num)).weight z.1 = 0 := by
      simp [binomialLaw, FiniteLaw.ofPMF, PMF.binomial_apply, hm]
    change (binomialLaw N 0 (by norm_num) (by norm_num)).weight z.1 *
      (q z.1).weight z.2 * _ = 0
    rw [hz, zero_mul, zero_mul]

/-- A concrete PSD-valued finite routine has single-batch Frobenius success
at least `3/4` as an actual probability-measure statement. Its assumptions
retain precisely the native count moments and raw conditional estimator risk. -/
theorem actual_block_success (B : BinomialMomentsInput)
    (R : Matrix ι ι ℂ) (hR : R.PosSemidef) (w W η : ℝ)
    (hmass : (Matrix.trace R).re = w) (hw : 0 < w) (hw1 : w ≤ 1) (hwW : w ≤ W)
    (N : ℕ) (hN : 0 < N) (hη : 0 < η)
    (hcost : 8 * (4 * Fintype.card ι + 1) * W ≤ η * N)
    {Y : Fin (N + 1) → Type*} [∀ m, Fintype (Y m)]
    [MeasurableSpace (Σ m, Y m)] [MeasurableSingletonClass (Σ m, Y m)]
    (q : ∀ m, FiniteLaw (Y m)) (τhat : ∀ m, Y m → Density ι)
    (hOW : ∀ m, 0 < m.val →
      (q m).expectation (fun y => frobeniusSq
        ((τhat m y).matrix - (normalizedBlock R hR w hmass hw).matrix)) ≤
          4 * Fintype.card ι / (m.val : ℝ)) :
    ENNReal.ofReal (3 / 4 : ℝ) ≤
      (FiniteLaw.mixture (binomialLaw N w hw.le hw1) q).toPMF.toMeasure
        {z | frobeniusSq (rescaledOutput N τhat z - R) ≤ η} := by
  rw [FiniteLaw.probability_eq_measure]
  apply ENNReal.ofReal_le_ofReal
  have h := finite_batch_success B N hN w W η hw.le hw1 hwW hη hcost q
    (normalizedBlock R hR w hmass hw) τhat hOW
  rwa [normalizedBlock_rescale] at h

end Paper26.CollectiveSubmatrix
