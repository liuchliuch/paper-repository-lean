import Paper26.SpectralLoss
import Paper26.Normalization
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Fintype.BigOperators

/-!
# Actual pure-state matrices and deterministic loss bounds

This file verifies Equations (38)--(39) for a genuine rank-one complex matrix.
`none` is the measured direction and `some k` is the direction of the residual
component. The ambient index type has cardinality `m + 1`.

It also proves the deterministic implications used after these equations.
The covariant POVM, its Haar law, and the probability of these events are not
asserted here.
-/

namespace Paper26.PureState

open scoped BigOperators ComplexOrder

noncomputable section

variable {m : ℕ}

abbrev Index (m : ℕ) := Option (Fin m)

/-- Squared amplitudes of the actual two-component pure vector. -/
def probability (k : Fin m) (t : ℝ) : Index m → ℝ
  | none => 1 - t
  | some j => if j = k then t else 0

/-- The vector `(sqrt(1-t), sqrt(t), 0, ...)`, embedded in complex space. -/
def vector (k : Fin m) (t : ℝ) (i : Index m) : ℂ :=
  (Real.sqrt (probability k t i) : ℂ)

/-- A genuine complex outer-product matrix `|ψ⟩⟨ψ|`. -/
def state (k : Fin m) (t : ℝ) : Matrix (Index m) (Index m) ℂ :=
  Matrix.vecMulVec (vector k t) (star (vector k t))

/-- The strictly positive spectrum of the regularized measured direction. -/
def outputSpectrum (a : ℝ) : Index m → ℝ
  | none => 1 - a
  | some _ => a / (m : ℝ)

def output (a : ℝ) : Matrix (Index m) (Index m) ℂ :=
  Matrix.diagonal (fun i => (outputSpectrum a i : ℂ))

theorem dimension : Fintype.card (Index m) = m + 1 := by simp [Index]

theorem tail_dimension_pos (k : Fin m) : 0 < m :=
  lt_of_le_of_lt (Nat.zero_le k.val) k.isLt

theorem probability_nonneg (k : Fin m) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (i : Index m) : 0 ≤ probability k t i := by
  cases i with
  | none => exact sub_nonneg.2 ht1
  | some i => simp only [probability]; split_ifs <;> positivity

theorem sum_probability_mul (k : Fin m) (t : ℝ) (f : Index m → ℝ) :
    (∑ i, f i * probability k t i) = f none * (1 - t) + f (some k) * t := by
  rw [Fintype.sum_option]
  simp [probability, mul_ite]

theorem probability_sum (k : Fin m) (t : ℝ) : ∑ i, probability k t i = 1 := by
  have h := sum_probability_mul k t (fun _ => 1)
  simpa using h

theorem vector_normSq (k : Fin m) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (i : Index m) : Complex.normSq (vector k t i) = probability k t i := by
  rw [vector, Complex.normSq_ofReal, Real.mul_self_sqrt (probability_nonneg k ht ht1 i)]

theorem vector_normalized (k : Fin m) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∑ i, Complex.normSq (vector k t i) = 1 := by
  simp_rw [vector_normSq k ht ht1]
  exact probability_sum k t

/-- The residual mass really is one minus the squared overlap with the
first (measured) coordinate direction. -/
theorem residual_mass (k : Fin m) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    1 - Complex.normSq (vector k t none) = t := by
  rw [vector_normSq k ht ht1]
  simp [probability]

theorem state_posSemidef (k : Fin m) (t : ℝ) : (state k t).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem state_rank_le_one (k : Fin m) (t : ℝ) : (state k t).rank ≤ 1 :=
  Matrix.rank_vecMulVec_le _ _

theorem state_hermitian (k : Fin m) (t : ℝ) : (state k t).IsHermitian :=
  (state_posSemidef k t).isHermitian

theorem state_diagonal (k : Fin m) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (i : Index m) : state k t i i = (probability k t i : ℂ) := by
  change vector k t i * star (vector k t i) = _
  rw [Complex.star_def, Complex.mul_conj, vector_normSq k ht ht1]

theorem state_trace (k : Fin m) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Matrix.trace (state k t) = 1 := by
  simp only [Matrix.trace, Matrix.diag_apply, state_diagonal k ht ht1,
    ← Complex.ofReal_sum, probability_sum, Complex.ofReal_one]

theorem state_trace_coordinates (k : Fin m) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∑ i, (state k t i i).re = 1 := by
  simp only [state_diagonal k ht ht1, Complex.ofReal_re, probability_sum]

theorem state_normSq (k : Fin m) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (i j : Index m) :
    Complex.normSq (state k t i j) = probability k t i * probability k t j := by
  change Complex.normSq (vector k t i * star (vector k t j)) = _
  rw [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
    vector_normSq k ht ht1, vector_normSq k ht ht1]

theorem outputSpectrum_pos (k : Fin m) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (i : Index m) : 0 < outputSpectrum a i := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 (tail_dimension_pos k)
  cases i with
  | none => exact sub_pos.2 ha1
  | some i => exact div_pos ha hm

theorem outputSpectrum_sum (k : Fin m) (a : ℝ) : ∑ i : Index m, outputSpectrum a i = 1 := by
  have hm : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.2 (tail_dimension_pos k))
  rw [Fintype.sum_option]
  simp only [outputSpectrum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp [hm]
  <;> ring

theorem output_posDef (k : Fin m) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (output (m := m) a).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  exact Complex.zero_lt_real.2 (outputSpectrum_pos k ha ha1 i)

theorem output_trace (k : Fin m) (a : ℝ) : Matrix.trace (output (m := m) a) = 1 := by
  simp only [output, Matrix.trace_diagonal, ← Complex.ofReal_sum,
    outputSpectrum_sum k, Complex.ofReal_one]

theorem weighted_probability_sum (k : Fin m) (t : ℝ)
    (w : Index m → Index m → ℝ) :
    (∑ i, ∑ j, w i j * probability k t i * probability k t j) =
      w none none * (1 - t) ^ 2 +
        w none (some k) * (1 - t) * t +
        w (some k) none * t * (1 - t) + w (some k) (some k) * t ^ 2 := by
  simp_rw [sum_probability_mul k t]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    sum_probability_mul, sum_probability_mul]
  ring

theorem bures_eq_energy (k : Fin m) (t a : ℝ) :
    SpectralLoss.bures (outputSpectrum a) (state k t - output a) =
      Normalization.buresEnergy (state k t) (outputSpectrum a) := by
  unfold SpectralLoss.bures Normalization.buresEnergy Normalization.spectralEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.sub_apply, output, Normalization.diagonalMatrix]
  ring

theorem rightInverse_eq_energy (k : Fin m) (t a : ℝ) :
    SpectralLoss.rightInverse (outputSpectrum a) (state k t - output a) =
      Normalization.rightEnergy (state k t) (outputSpectrum a) := by
  unfold SpectralLoss.rightInverse Normalization.rightEnergy Normalization.spectralEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.sub_apply, output, Normalization.diagonalMatrix]
  ring

/-- Equation (38), evaluated on the actual rank-one complex input matrix. -/
theorem bures_formula (k : Fin m) {t a : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (ha : 0 < a) (ha1 : a < 1) :
    SpectralLoss.bures (outputSpectrum a) (state k t - output a) =
      (a - t) ^ 2 / (1 - a) + (m : ℝ) * t ^ 2 / a - 2 * t + a +
        4 * t * (1 - t) / (1 - a + a / (m : ℝ)) := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 (tail_dimension_pos k)
  have hq := outputSpectrum_pos k ha ha1
  have hdiag (i : Index m) :
      2 / (outputSpectrum a i + outputSpectrum a i) = 1 / outputSpectrum a i := by
    field_simp [ne_of_gt (hq i)]
    <;> ring
  rw [bures_eq_energy]
  unfold Normalization.buresEnergy
  rw [Normalization.spectralEnergy_expansion _ _ _ (fun i => ne_of_gt (hq i)) hdiag,
    state_trace_coordinates k ht ht1, outputSpectrum_sum k]
  simp_rw [state_normSq k ht ht1, ← mul_assoc]
  rw [weighted_probability_sum]
  simp only [outputSpectrum]
  have hden : 1 - a + a / (m : ℝ) ≠ 0 :=
    ne_of_gt (add_pos (sub_pos.2 ha1) (div_pos ha hm))
  have hden' : a / (m : ℝ) + (1 - a) ≠ 0 := by simpa only [add_comm] using hden
  field_simp [ne_of_gt ha, ne_of_gt (sub_pos.2 ha1), ne_of_gt hm, hden, hden']
  <;> ring

/-- Equation (39), evaluated on the same actual rank-one complex matrix. -/
theorem rightInverse_formula (k : Fin m) {t a : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (ha : 0 < a) (ha1 : a < 1) :
    SpectralLoss.rightInverse (outputSpectrum a) (state k t - output a) =
      (1 - t) / (1 - a) + (m : ℝ) * t / a - 1 := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 (tail_dimension_pos k)
  have hq := outputSpectrum_pos k ha ha1
  rw [rightInverse_eq_energy]
  unfold Normalization.rightEnergy
  rw [Normalization.spectralEnergy_expansion _ _ _ (fun i => ne_of_gt (hq i))
    (fun _ => rfl), state_trace_coordinates k ht ht1, outputSpectrum_sum k]
  simp_rw [state_normSq k ht ht1, ← mul_assoc]
  rw [weighted_probability_sum]
  simp only [outputSpectrum]
  field_simp [ne_of_gt ha, ne_of_gt (sub_pos.2 ha1), ne_of_gt hm]
  <;> ring

/-- The deterministic Bures event estimate immediately after Equation (38). -/
theorem bures_small_tail (k : Fin m) {t a : ℝ}
    (ha : 0 < a) (haSmall : a ≤ 1 / 16) (ht : 0 ≤ t)
    (htEvent : t ≤ a / Real.sqrt (m : ℝ)) :
    SpectralLoss.bures (outputSpectrum a) (state k t - output a) ≤ 11 * a := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 (tail_dimension_pos k)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (tail_dimension_pos k)
  have hs1 : 1 ≤ Real.sqrt (m : ℝ) := Real.one_le_sqrt.2 hm1
  have hs : 0 < Real.sqrt (m : ℝ) := lt_of_lt_of_le zero_lt_one hs1
  have hdiv : a / Real.sqrt (m : ℝ) ≤ a := by
    apply (div_le_iff₀ hs).2
    nlinarith [mul_le_mul_of_nonneg_left hs1 ha.le]
  have hta : t ≤ a := htEvent.trans hdiv
  have ht1 : t ≤ 1 := by linarith
  have ha1 : a < 1 := by linarith
  have hden : 0 < 1 - a := sub_pos.2 ha1
  have hhead : (a - t) ^ 2 / (1 - a) ≤ 2 * a ^ 2 := by
    apply (div_le_iff₀ hden).2
    have hprod := mul_nonneg ht (by linarith : 0 ≤ 2 * a - t)
    have hprod' := mul_nonneg (sq_nonneg a) (by linarith : 0 ≤ 1 - 2 * a)
    nlinarith
  have hmul : t * Real.sqrt (m : ℝ) ≤ a := (le_div_iff₀ hs).1 htEvent
  have hsq := (sq_le_sq₀ (mul_nonneg ht hs.le) ha.le).2 hmul
  rw [mul_pow, Real.sq_sqrt hm.le] at hsq
  have htail : (m : ℝ) * t ^ 2 / a ≤ a := by
    apply (div_le_iff₀ ha).2
    nlinarith
  have hcrossden : 0 < 1 - a + a / (m : ℝ) := by positivity
  have hhalf : (1 / 2 : ℝ) ≤ 1 - a + a / (m : ℝ) := by
    have hpos := div_pos ha hm
    linarith
  have hcross : 4 * t * (1 - t) / (1 - a + a / (m : ℝ)) ≤ 8 * t := by
    apply (div_le_iff₀ hcrossden).2
    have hdenmul := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 8 * t)
    nlinarith [sq_nonneg t]
  rw [bures_formula k ht ht1 ha ha1]
  have hsmall := mul_nonneg ha.le (by linarith : 0 ≤ 1 - 2 * a)
  nlinarith

/-- At `a = ε/16`, the Bures event in the paper implies strict success. -/
theorem bures_epsilon (k : Fin m) {t ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t)
    (htEvent : t ≤ (ε / 16) / Real.sqrt (m : ℝ)) :
    SpectralLoss.bures (outputSpectrum (ε / 16))
      (state k t - output (ε / 16)) < ε := by
  have h := bures_small_tail k (by positivity : 0 < ε / 16)
    (by linarith : ε / 16 ≤ 1 / 16) ht htEvent
  linarith

/-- At `a = ε/4`, the right-inverse event in the paper implies success. -/
theorem rightInverse_epsilon (k : Fin m) {t ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t)
    (htEvent : t ≤ ε ^ 2 / (8 * (m : ℝ))) :
    SpectralLoss.rightInverse (outputSpectrum (ε / 4))
      (state k t - output (ε / 4)) ≤ ε := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 (tail_dimension_pos k)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (tail_dimension_pos k)
  have hepsSq : ε ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ hε.le (by norm_num : (0 : ℝ) ≤ 1)).2 hε1
  have ht1 : t ≤ 1 := by
    apply htEvent.trans
    apply (div_le_iff₀ (by positivity : 0 < 8 * (m : ℝ))).2
    nlinarith
  have ha : 0 < ε / 4 := by positivity
  have ha1 : ε / 4 < 1 := by linarith
  have hden : 0 < 1 - ε / 4 := by linarith
  have hhead : (1 - t) / (1 - ε / 4) ≤ 1 + ε / 2 := by
    apply (div_le_iff₀ hden).2
    have hprod := mul_nonneg hε.le (sub_nonneg.2 hε1)
    nlinarith
  have htail : (m : ℝ) * t / (ε / 4) ≤ ε / 2 := by
    apply (div_le_iff₀ ha).2
    have hprod := (le_div_iff₀ (by positivity : 0 < 8 * (m : ℝ))).1 htEvent
    nlinarith
  rw [rightInverse_formula k ht ht1 ha ha1]
  linarith

end
end Paper26.PureState
