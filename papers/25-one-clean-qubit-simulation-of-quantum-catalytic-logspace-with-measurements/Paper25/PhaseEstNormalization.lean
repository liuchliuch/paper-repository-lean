import Paper25.PhaseEstTail
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Normalization of the actual phase-estimation amplitudes

The discrete Fourier orthogonality identity proves that the probabilities used
in Appendix B sum to one, for every eigenphase.
-/

noncomputable section
open scoped ComplexConjugate

namespace Paper25

set_option maxHeartbeats 400000

/-- Orthogonality of the exponentials on the finite phase grid. -/
lemma phase_grid_orthogonality (M : ℕ) (hM : 0 < M) (r s : Fin M) :
    (∑ j : Fin M, Complex.exp
      (2 * Real.pi * Complex.I * ((r : ℂ) - s) * ((j : ℂ) / M)))
      = if r = s then (M : ℂ) else 0 := by
  classical
  by_cases hrs : r = s
  · subst s
    simp
  · rw [if_neg hrs]
    let q : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) - s) / M)
    have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    have hqpow : q ^ M = 1 := by
      dsimp only [q]
      rw [← Complex.exp_nat_mul]
      have heq : (M : ℂ) * (2 * Real.pi * Complex.I * ((r : ℂ) - s) / M)
          = (((r.val : ℤ) - s.val : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        field_simp
      rw [heq]
      exact Complex.exp_int_mul_two_pi_mul_I ((r.val : ℤ) - s.val)
    have hqne : q ≠ 1 := by
      intro hq
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hq
      have heq : (((r.val : ℤ) - s.val : ℤ) : ℂ) = (M : ℂ) * k := by
        have hconst : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
          exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
            Complex.I_ne_zero
        apply mul_right_cancel₀ hconst
        have hk' := (div_eq_iff hMne).mp hk
        push_cast
        calc
          ((r : ℂ) - s) * (2 * Real.pi * Complex.I)
              = 2 * Real.pi * Complex.I * ((r : ℂ) - s) := by ring
          _ = (k * (2 * Real.pi * Complex.I)) * (M : ℂ) := hk'
          _ = ((M : ℂ) * k) * (2 * Real.pi * Complex.I) := by ring
      have heq' : (r.val : ℤ) - s.val = (M : ℤ) * k := by exact_mod_cast heq
      have hdvd : (M : ℤ) ∣ (r.val : ℤ) - s.val := ⟨k, heq'⟩
      have hzero : (r.val : ℤ) - s.val = 0 := by
        by_cases hle : s.val ≤ r.val
        · exact Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hdvd
        · have hneg : (M : ℤ) ∣ (s.val : ℤ) - r.val := by
            simpa only [neg_sub] using dvd_neg.mpr hdvd
          have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt
            (show (0 : ℤ) ≤ s.val - r.val by omega)
            (show (s.val : ℤ) - r.val < M by omega) hneg
          omega
      exact hrs (Fin.ext (by omega))
    have hsum : (∑ j : Fin M, Complex.exp
        (2 * Real.pi * Complex.I * ((r : ℂ) - s) * ((j : ℂ) / M)))
        = ∑ j ∈ Finset.range M, q ^ j := by
      rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => q ^ j) M]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [q]
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    rw [hsum, geom_sum_eq hqne M, hqpow, sub_self, zero_div]

/-- Multiplication of a Fourier kernel by its complex conjugate. -/
lemma phase_kernel_product (M : ℕ) (φ : ℝ) (r s j : Fin M) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * (φ - (j : ℂ) / M))) *
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (φ - (j : ℂ) / M))
      = Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) - s) * φ) *
        Complex.exp (2 * Real.pi * Complex.I * ((s : ℂ) - r) * ((j : ℂ) / M)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
    map_natCast, map_sub, map_div₀]
  push_cast
  ring

/-- Expansion of the squared norm of a finite complex sum. -/
lemma complex_sq_norm_fin_sum {M : ℕ} (v : Fin M → ℂ) :
    ((‖∑ r : Fin M, v r‖ ^ 2 : ℝ) : ℂ)
      = ∑ r : Fin M, ∑ s : Fin M, (starRingEnd ℂ) (v s) * v r := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, map_sum,
    Finset.sum_mul_sum, Finset.sum_comm]

/-- Normalization of Appendix B's explicit phase-estimation probabilities. -/
theorem phaseEstProb_sum (M : ℕ) (φ : ℝ) (hM : 0 < M) :
    ∑ j : Fin M, phaseEstProb M φ j = 1 := by
  classical
  have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hamp : ∀ j : Fin M, phaseEstAmplitude M φ j =
      (M : ℂ)⁻¹ * ∑ r : Fin M,
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (φ - (j : ℝ) / M)) := by
    intro j
    unfold phaseEstAmplitude
    exact congrArg (fun z : ℂ => (M : ℂ)⁻¹ * z)
      (Fin.sum_univ_eq_sum_range (fun r : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (φ - (j : ℝ) / M))) M).symm
  have hprob : ∀ j : Fin M, (phaseEstProb M φ j : ℂ)
      = (M : ℂ)⁻¹ ^ 2 * ∑ r : Fin M, ∑ s : Fin M,
        Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) - s) * φ) *
        Complex.exp (2 * Real.pi * Complex.I * ((s : ℂ) - r) * ((j : ℂ) / M)) := by
    intro j
    rw [phaseEstProb, hamp, norm_mul, mul_pow, norm_inv, RCLike.norm_natCast]
    push_cast
    rw [← Complex.ofReal_pow, complex_sq_norm_fin_sum]
    simp_rw [phase_kernel_product]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [hprob]
  rw [← Finset.mul_sum]
  have htriple : (∑ j : Fin M, ∑ r : Fin M, ∑ s : Fin M,
        Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) - s) * φ) *
        Complex.exp (2 * Real.pi * Complex.I * ((s : ℂ) - r) * ((j : ℂ) / M)))
      = (M : ℂ) ^ 2 := by
    rw [Finset.sum_comm]
    apply Eq.trans (Finset.sum_congr rfl (fun r _ => Finset.sum_comm))
    simp_rw [← Finset.mul_sum, phase_grid_orthogonality M hM]
    simp
    ring
  rw [htriple]
  field_simp

/-- Appendix B's complete uniform analytic error bound with no normalization
assumption: the probabilities are the explicit phase-estimation amplitudes. -/
theorem phaseEst_filter_average_error
    (M : ℕ) (δ ε φ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hMdef : 4096 / (δ * ε ^ 2) ≤ (M : ℝ)) :
    |(∑ j : Fin M, phaseEstProb M φ j * filterG δ (2 * Real.pi * ((j : ℝ) / M)))
      - filterG δ (2 * Real.pi * φ)| ≤ ε / 8 := by
  have hM : 0 < M := by
    have : 0 < (M : ℝ) := lt_of_lt_of_le (by positivity) hMdef
    exact_mod_cast this
  exact phaseEst_filter_average_error_of_normalized M δ ε φ hδ hδle hε hεle hMdef
    (phaseEstProb_sum M φ hM)

/-- The least sufficient power of two overshoots a threshold by less than
one factor of two. This is the finite resource estimate used in Appendix B. -/
lemma exists_power_two_in_range (K : ℝ) (hK : 1 ≤ K) :
    ∃ m : ℕ, K ≤ (2 : ℝ) ^ m ∧ (2 : ℝ) ^ m < 2 * K := by
  classical
  have hex : ∃ m : ℕ, K ≤ (2 : ℝ) ^ m := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt K (by norm_num : (1 : ℝ) < 2)
    exact ⟨m, hm.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  cases hm : Nat.find hex with
  | zero => simp only [pow_zero]; linarith
  | succ m =>
    have hprev := Nat.find_min hex (show m < Nat.find hex by rw [hm]; omega)
    have hp : (2 : ℝ) ^ m < K := lt_of_not_ge hprev
    rw [pow_succ]
    linarith

/-- Expanding the controlled powers uses exactly `2^m - 1` walk calls. -/
lemma phaseEst_walk_calls (m : ℕ) :
    (∑ k ∈ Finset.range m, (2 : ℕ) ^ k) = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have hp : 0 < (2 : ℕ) ^ m := by positivity
    omega

/-- A concrete phase-register size with a uniform error bound, a reciprocal
polynomial upper bound on walk calls, and a logarithmic upper bound on `m`. -/
theorem phaseEst_precision_exists (δ ε : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    ∃ m : ℕ,
      (4096 / (δ * ε ^ 2) ≤ ((2 ^ m : ℕ) : ℝ)) ∧
      (((2 ^ m : ℕ) : ℝ) < 8192 / (δ * ε ^ 2)) ∧
      ((m : ℝ) < 1 + Real.log (4096 / (δ * ε ^ 2)) / Real.log 2) ∧
      (∀ φ : ℝ,
        |(∑ j : Fin (2 ^ m), phaseEstProb (2 ^ m) φ j *
          filterG δ (2 * Real.pi * ((j : ℝ) / (2 ^ m : ℕ))))
          - filterG δ (2 * Real.pi * φ)| ≤ ε / 8) := by
  let K : ℝ := 4096 / (δ * ε ^ 2)
  have hden : 0 < δ * ε ^ 2 := by positivity
  have hdenle : δ * ε ^ 2 ≤ 1 := by
    have heps : ε ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hK : 1 ≤ K := by
    dsimp [K]
    apply (le_div_iff₀ hden).2
    linarith
  obtain ⟨m, hmlo, hmhi⟩ := exists_power_two_in_range K hK
  have hmlo' : 4096 / (δ * ε ^ 2) ≤ ((2 ^ m : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmlo
  have hmhi' : ((2 ^ m : ℕ) : ℝ) < 8192 / (δ * ε ^ 2) := by
    rw [show 8192 / (δ * ε ^ 2) = 2 * K by dsimp [K]; ring]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmhi
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.strictMonoOn_log (by change 0 < (2 : ℝ) ^ m; positivity)
    (by change 0 < 2 * K; positivity) hmhi
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hKpos.ne'] at hlog
  have hm_log : (m : ℝ) < 1 + Real.log K / Real.log 2 := by
    have h := (lt_div_iff₀ hlog2).2
      (show ((m : ℝ) - 1) * Real.log 2 < Real.log K by nlinarith)
    linarith
  refine ⟨m, hmlo', hmhi', hm_log, ?_⟩
  intro φ
  exact phaseEst_filter_average_error (2 ^ m) δ ε φ hδ hδle hε hεle hmlo'

end Paper25
