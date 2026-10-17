import Paper25.Basic
import Paper25.Norms

/-!
# Numerical signed-bias definitions

These definitions support the scalar decision-gap estimates. Source and target
operational models require actual channels and unitary gate lists; they are
not represented merely by arbitrary acceptance numbers.
-/

noncomputable section

namespace Paper25

/-- Signed acceptance bias `e_x = 2 p_x - 1`. -/
def signedBias (p : ℝ) : ℝ := 2 * p - 1

lemma signedBias_eq_two_mul_sub_one (p : ℝ) : signedBias p = 2 * p - 1 := rfl

lemma signedBias_of_prob {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    -1 ≤ signedBias p ∧ signedBias p ≤ 1 := by
  unfold signedBias
  constructor <;> linarith

lemma signedBias_ge_third {p : ℝ} (hp : 2 / 3 ≤ p) : 1 / 3 ≤ signedBias p := by
  unfold signedBias
  linarith

lemma signedBias_le_neg_third {p : ℝ} (hp : p ≤ 1 / 3) : signedBias p ≤ -1 / 3 := by
  unfold signedBias
  linarith

lemma signedBias_neg (p : ℝ) : signedBias (1 - p) = -signedBias p := by
  unfold signedBias
  ring

/-- Numerical content of Theorem 1: a source bias of magnitude at least `1/3`
and error budget `|a - lam e/√K| ≤ lam/(100K)` yields a simulator bias of
magnitude at least `lam/(4√K)`. -/
theorem theorem1_signed_gap (lam K e a : ℝ)
    (hlam : 0 < lam) (hK : 1 ≤ K) (he : (1 / 3 : ℝ) ≤ |e|)
    (herr : |a - lam * e / Real.sqrt K| ≤ lam / (100 * K)) :
    (0 < e → lam / (4 * Real.sqrt K) ≤ a) ∧
    (e < 0 → a ≤ -lam / (4 * Real.sqrt K)) := by
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le (by norm_num) hK
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hsK : Real.sqrt K ≤ K := by
    nlinarith [sq_nonneg (Real.sqrt K - 1), Real.sq_sqrt (le_of_lt hK0), Real.sqrt_nonneg K]
  have hdiv : lam / (100 * K) ≤ lam / (100 * Real.sqrt K) :=
    div_le_div_of_nonneg_left (le_of_lt hlam) (by positivity) (by nlinarith)
  have herr' : |a - lam * e / Real.sqrt K| ≤ lam / (100 * Real.sqrt K) :=
    le_trans herr hdiv
  have hgap : (1 / 3 : ℝ) - 1 / 100 > 1 / 4 := by norm_num
  set x : ℝ := lam / Real.sqrt K with hx
  have hxpos : 0 < x := by positivity
  have hcore : x * (1 / 3) - x * (1 / 100) ≥ x * (1 / 4) := by
    nlinarith [hgap, hxpos]
  have hcore' : x * (1 / 4) = lam / (4 * Real.sqrt K) := by
    rw [hx]
    have hne : Real.sqrt K ≠ 0 := ne_of_gt hs
    first | field_simp [hne] | (field_simp [hne]; ring)
  constructor
  · intro hepos
    have hep : e = |e| := (abs_of_pos hepos).symm
    have hball : lam * e / Real.sqrt K - lam / (100 * Real.sqrt K) ≤ a := by
      have := herr'
      rw [abs_le] at this
      linarith
    have hedge : x * (1 / 3) ≤ lam * e / Real.sqrt K := by
      rw [hx, hep]
      have : lam * |e| / Real.sqrt K = x * |e| := by
        rw [hx]
        have hne : Real.sqrt K ≠ 0 := ne_of_gt hs
        first | field_simp [hne] | (field_simp [hne]; ring)
      rw [this]
      exact mul_le_mul_of_nonneg_left he (le_of_lt hxpos)
    have hmid : x * (1 / 3) - lam / (100 * Real.sqrt K) ≤ a := by
      have : x * (1 / 3) - lam / (100 * Real.sqrt K)
          = lam * e / Real.sqrt K - lam / (100 * Real.sqrt K)
            - (lam * e / Real.sqrt K - x * (1 / 3)) := by ring
      nlinarith [hedge, hball]
    have h100 : lam / (100 * Real.sqrt K) = x * (1 / 100) := by
      rw [hx]
      have hne : Real.sqrt K ≠ 0 := ne_of_gt hs
      first | field_simp [hne] | (field_simp [hne]; ring)
    rw [h100] at hmid
    nlinarith [hcore, hcore']
  · intro heneg
    have hep : e = -|e| := by
      rw [abs_of_neg heneg]
      ring
    have hball : a ≤ lam * e / Real.sqrt K + lam / (100 * Real.sqrt K) := by
      have := herr'
      rw [abs_le] at this
      linarith
    have hedge : lam * e / Real.sqrt K ≤ x * (-(1 / 3 : ℝ)) := by
      rw [hx, hep]
      have : lam * (-|e|) / Real.sqrt K = x * (-|e|) := by
        rw [hx]
        have hne : Real.sqrt K ≠ 0 := ne_of_gt hs
        first | field_simp [hne] | (field_simp [hne]; ring)
      rw [this]
      have : (-|e| : ℝ) ≤ -(1 / 3 : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_left this (le_of_lt hxpos)
    have h100 : lam / (100 * Real.sqrt K) = x * (1 / 100) := by
      rw [hx]
      have hne : Real.sqrt K ≠ 0 := ne_of_gt hs
      first | field_simp [hne] | (field_simp [hne]; ring)
    have hmid : a ≤ x * (-(1 / 3 : ℝ)) + x * (1 / 100) := by
      rw [← h100]
      nlinarith [hedge, hball]
    have : x * (-(1 / 3 : ℝ)) + x * (1 / 100) = -(x * (1 / 3) - x * (1 / 100)) := by
      ring
    rw [this] at hmid
    have hneg : -(x * (1 / 4)) = -lam / (4 * Real.sqrt K) := by
      have hne : Real.sqrt K ≠ 0 := ne_of_gt hs
      rw [hx]
      first | field_simp [hne] | (field_simp [hne]; ring)
    nlinarith [hcore, hneg]

end Paper25
