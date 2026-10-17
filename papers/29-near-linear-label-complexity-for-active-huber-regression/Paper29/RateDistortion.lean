import Paper29.InformationDefs
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Lemma 4.2. A finite joint law and its standard logarithmic mutual information.
The proof uses Gibbs' inequality against a binary product channel, rather than
assuming an entropy chain rule or a Fano bound. -/
noncomputable section
open scoped BigOperators

namespace Paper29.RateDistortion

namespace JointLaw
variable {r : ℕ} (P : JointLaw r)

lemma source_nonneg (s : Cube r) : 0 ≤ P.source s :=
  Finset.sum_nonneg fun t _ => P.nonneg s t

lemma estimate_nonneg (t : Cube r) : 0 ≤ P.estimate t :=
  Finset.sum_nonneg fun s _ => P.nonneg s t

lemma mass_le_source (s t : Cube r) : P.mass s t ≤ P.source s :=
  Finset.single_le_sum (fun u _ => P.nonneg s u) (Finset.mem_univ t)

lemma mass_le_estimate (s t : Cube r) : P.mass s t ≤ P.estimate t :=
  Finset.single_le_sum (fun u _ => P.nonneg u t) (Finset.mem_univ s)

lemma estimate_total : ∑ t, P.estimate t = 1 := by
  unfold estimate
  rw [Finset.sum_comm]
  exact P.total

/-- This is exactly the usual joint-versus-product log-density formula for MI. -/
theorem mutualInformation_eq_log_ratio :
    P.mutualInformation = ∑ s, ∑ t,
      P.mass s t * Real.log (P.mass s t / (P.source s * P.estimate t)) := by
  unfold mutualInformation
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  by_cases hp : P.mass s t = 0
  · simp [hp]
  · have hp0 : 0 < P.mass s t := lt_of_le_of_ne (P.nonneg s t) (Ne.symm hp)
    have hs : 0 < P.source s := hp0.trans_le (P.mass_le_source s t)
    have ht : 0 < P.estimate t := hp0.trans_le (P.mass_le_estimate s t)
    rw [Real.log_div hp (ne_of_gt (mul_pos hs ht)), Real.log_mul hs.ne' ht.ne']
    ring

/-- Uniformity gives exactly `r log 2` source entropy. -/
theorem uniform_information (hu : ∀ s, P.source s = ((2 : ℝ) ^ r)⁻¹) :
    P.mutualInformation = P.conditionalLogMass + (r : ℝ) * Real.log 2 := by
  have hlog : ∀ s, Real.log (P.source s) = -(r : ℝ) * Real.log 2 := by
    intro s
    rw [hu, Real.log_inv, Real.log_pow]
    ring
  have hterm : ∀ s t, P.mass s t *
      (Real.log (P.mass s t) - Real.log (P.source s) - Real.log (P.estimate t)) =
      P.mass s t * (Real.log (P.mass s t) - Real.log (P.estimate t)) +
        P.mass s t * ((r : ℝ) * Real.log 2) := by
    intro s t
    rw [hlog]
    ring
  unfold mutualInformation
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [P.total, one_mul]
  rfl

end JointLaw

lemma errorChannel_pos {r : ℕ} (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (s t : Cube r) : 0 < errorChannel δ s t := by
  apply Finset.prod_pos
  intro j _
  split_ifs <;> linarith

/-- The product error channel is normalized for each estimated word. -/
lemma errorChannel_total {r : ℕ} (δ : ℝ) (t : Cube r) :
    ∑ s : Cube r, errorChannel δ s t = 1 := by
  unfold errorChannel
  rw [← Fintype.prod_sum (fun (j : Fin r) (b : Bool) =>
    if b = t j then 1 - δ else δ)]
  have hsum : ∀ j : Fin r, (∑ b : Bool, if b = t j then 1 - δ else δ) = 1 := by
    intro j
    cases t j <;> simp
  simp_rw [hsum]
  simp

/-- Log likelihood of the error channel is affine in Hamming distance. -/
lemma errorChannel_log {r : ℕ} (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (s t : Cube r) :
    Real.log (errorChannel δ s t) =
      hamming s t * Real.log δ + ((r : ℝ) - hamming s t) * Real.log (1 - δ) := by
  unfold errorChannel
  rw [Real.log_prod]
  · have ht : ∀ j : Fin r,
        Real.log (if s j = t j then 1 - δ else δ) =
          Real.log (1 - δ) + (if s j = t j then (0 : ℝ) else 1) *
            (Real.log δ - Real.log (1 - δ)) := by
      intro j
      split_ifs <;> ring
    simp_rw [ht]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold hamming
    ring
  · intro j _
    split_ifs <;> linarith

/-- Pointwise Gibbs inequality; the zero-mass case is included explicitly. -/
lemma gibbs_term (p m w : ℝ) (hp : 0 ≤ p) (hpm : p ≤ m) (hw : 0 < w) :
    p * Real.log w + p - m * w ≤ p * (Real.log p - Real.log m) := by
  by_cases hpz : p = 0
  · have hm : 0 ≤ m := hp.trans hpm
    simp only [hpz, zero_mul, zero_add, zero_sub]
    nlinarith [mul_nonneg hm (le_of_lt hw)]
  · have hp0 : 0 < p := lt_of_le_of_ne hp (Ne.symm hpz)
    have hm0 : 0 < m := hp0.trans_le hpm
    have hmw : 0 < m * w := mul_pos hm0 hw
    have hl := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hmw hp0)) hp
    rw [Real.log_div hmw.ne' hp0.ne', Real.log_mul hm0.ne' hw.ne'] at hl
    have hc : p * (m * w / p - 1) = m * w - p := by
      field_simp
    rw [hc] at hl
    nlinarith

/-- Genuine finite conditional-entropy bound, derived from Gibbs and a normalized channel. -/
theorem conditional_log_mass_bound {r : ℕ} (P : JointLaw r)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    expectedHamming P * Real.log δ +
      ((r : ℝ) - expectedHamming P) * Real.log (1 - δ) ≤ P.conditionalLogMass := by
  have htotal : ∑ s, ∑ t, P.estimate t * errorChannel δ s t = 1 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, errorChannel_total, mul_one]
    exact P.estimate_total
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Cube r))) =>
    Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Cube r))) =>
      gibbs_term (P.mass s t) (P.estimate t) (errorChannel δ s t)
        (P.nonneg s t) (P.mass_le_estimate s t) (errorChannel_pos δ hδ hδ1 s t)))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  rw [P.total, htotal] at hsum
  have hlog : ∀ s t, P.mass s t * Real.log (errorChannel δ s t) =
      P.mass s t * hamming s t * (Real.log δ - Real.log (1 - δ)) +
        P.mass s t * ((r : ℝ) * Real.log (1 - δ)) := by
    intro s t
    rw [errorChannel_log δ hδ hδ1]
    ring
  simp_rw [hlog, Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  rw [P.total, one_mul] at hsum
  change expectedHamming P * (Real.log δ - Real.log (1 - δ)) +
    (r : ℝ) * Real.log (1 - δ) + 1 - 1 ≤ P.conditionalLogMass at hsum
  nlinarith

/-- The binary rate-distortion inequality for the arbitrary joint law. -/
theorem binary_rate_distortion {r : ℕ} (P : JointLaw r)
    (hu : ∀ s, P.source s = ((2 : ℝ) ^ r)⁻¹)
    (herr : expectedHamming P < (1 / 25 : ℝ) * r) :
    (Real.log 2 - Real.binEntropy (1 / 25)) * r ≤ P.mutualInformation := by
  have hbound := conditional_log_mass_bound P (1 / 25) (by norm_num) (by norm_num)
  have hlogs : Real.log (1 / 25 : ℝ) ≤ Real.log (1 - (1 / 25 : ℝ)) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonpos_right (le_of_lt herr) (sub_nonpos.mpr hlogs)
  rw [P.uniform_information hu]
  rw [Real.binEntropy, Real.log_inv, Real.log_inv]
  nlinarith

/-- The strict numerical constant in equation (4.5), with certified log-series errors. -/
theorem cRD_gt : (0.525 : ℝ) < cRD := by
  have ha := Real.abs_log_sub_add_sum_range_le
    (show |(1 / 5 : ℝ)| < 1 by norm_num) 7
  have hb := Real.abs_log_sub_add_sum_range_le
    (show |(1 / 25 : ℝ)| < 1 by norm_num) 3
  norm_num [Finset.sum_range_succ] at ha hb
  have ha' : -(0.22315 : ℝ) < Real.log (4 / 5 : ℝ) := by
    have := (abs_le.mp ha).1
    linarith
  have hb' : -(0.04083 : ℝ) < Real.log (24 / 25 : ℝ) := by
    have := (abs_le.mp hb).1
    linarith
  have hlog : Real.log (1 / 25 : ℝ) =
      2 * Real.log (4 / 5 : ℝ) - 4 * Real.log 2 := by
    have heq : (1 / 25 : ℝ) = (4 / 5 : ℝ) ^ 2 / (2 : ℝ) ^ 4 := by norm_num
    rw [heq, Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  unfold cRD
  rw [Real.binEntropy, Real.log_inv, Real.log_inv]
  norm_num only [show (1 : ℝ) - 1 / 25 = 24 / 25 by norm_num]
  rw [hlog]
  linarith [Real.log_two_gt_d9]

/-- Lemma 4.2, including its explicit strict constant. -/
theorem lemma4_2 {r : ℕ} (P : JointLaw r)
    (hu : ∀ s, P.source s = ((2 : ℝ) ^ r)⁻¹)
    (herr : expectedHamming P < (0.04 : ℝ) * r) :
    cRD * r ≤ P.mutualInformation ∧ (0.525 : ℝ) < cRD := by
  constructor
  · apply binary_rate_distortion P hu
    convert herr using 1
    norm_num
  · exact cRD_gt

end Paper29.RateDistortion
