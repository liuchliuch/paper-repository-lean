import ELV.LineCost

/-! Derive the line-walk spectral and cost parameters from the invariant
plane matrix (3.3), including the probability endpoints algebraically. -/
noncomputable section
namespace ELV.Line

def matrixMean (p : ℝ) : ℝ := 1-2*p
def matrixOff (p : ℝ) : ℝ := 2*Real.sqrt (p*(1-p))
def lowRatio (p : ℝ) : ℝ := Real.sqrt (p/(1-p))
def highRatio (p : ℝ) : ℝ := -Real.sqrt ((1-p)/p)
def ratio (p : ℝ) : ℝ := if p < 1/2 then lowRatio p else highRatio p
def phaseSign (p : ℝ) : ℂ := if p < 1/2 then 1 else -1

lemma lowRatio_sq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1/2) :
    lowRatio p ^ 2 = p/(1-p) := by
  exact Real.sq_sqrt (div_nonneg hp0 (by linarith))

lemma highRatio_sq (p : ℝ) (hp0 : 1/2 < p) (hp1 : p ≤ 1) :
    highRatio p ^ 2 = (1-p)/p := by
  simpa [highRatio] using Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hp1) (by linarith : 0 ≤ p))

lemma lowRatio_lt_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1/2) : lowRatio p ^ 2 < 1 := by
  rw [lowRatio_sq p hp0 hp1]
  exact (div_lt_one (by linarith : 0 < 1-p)).2 (by linarith)

lemma highRatio_lt_one (p : ℝ) (hp0 : 1/2 < p) (hp1 : p ≤ 1) : highRatio p ^ 2 < 1 := by
  rw [highRatio_sq p hp0 hp1]
  exact (div_lt_one (by linarith : 0 < p)).2 (by linarith)

lemma matrixOff_low (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1/2) :
    matrixOff p = 2*(1-p)*lowRatio p := by
  have hn : 1-p ≠ 0 := by linarith
  have hid : p*(1-p) = (1-p)^2 * (p/(1-p)) := by field_simp [hn] <;> ring
  unfold matrixOff lowRatio
  rw [hid,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by linarith : 0 ≤ 1-p)]
  ring

lemma matrixOff_high (p : ℝ) (hp0 : 1/2 < p) (hp1 : p ≤ 1) :
    matrixOff p = -2*p*highRatio p := by
  have hn : p ≠ 0 := by linarith
  have hid : p*(1-p) = p^2 * ((1-p)/p) := by field_simp [hn]
  unfold matrixOff highRatio
  rw [hid,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by linarith : 0 ≤ p)]
  ring

lemma low_spectral (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1/2) :
    matrixMean p + lowRatio p * matrixOff p = 1 ∧
    matrixOff p - lowRatio p * matrixMean p = lowRatio p := by
  have hsq := lowRatio_sq p hp0 hp1
  have hn : 1-p ≠ 0 := by linarith
  have hmul : lowRatio p ^ 2 * (1-p) = p := by rw [hsq]; exact div_mul_cancel₀ _ hn
  rw [matrixOff_low p hp0 hp1]
  unfold matrixMean
  constructor <;> nlinarith

lemma high_spectral (p : ℝ) (hp0 : 1/2 < p) (hp1 : p ≤ 1) :
    matrixMean p + highRatio p * matrixOff p = -1 ∧
    matrixOff p - highRatio p * matrixMean p = -highRatio p := by
  have hsq := highRatio_sq p hp0 hp1
  have hn : p ≠ 0 := by linarith
  have hmul : highRatio p ^ 2 * p = 1-p := by rw [hsq]; exact div_mul_cancel₀ _ hn
  rw [matrixOff_high p hp0 hp1]
  unfold matrixMean
  constructor <;> nlinarith

lemma ratio_lt_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hne : p ≠ 1/2) : ratio p ^ 2 < 1 := by
  unfold ratio
  split_ifs with hl
  · exact lowRatio_lt_one p hp0 hl
  · exact highRatio_lt_one p (lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm hne)) hp1

lemma ratio_spectral (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hne : p ≠ 1/2) :
    (matrixMean p : ℂ) + (ratio p : ℂ) * (matrixOff p : ℂ) = phaseSign p ∧
    (matrixOff p : ℂ) - (ratio p : ℂ) * (matrixMean p : ℂ) = phaseSign p * (ratio p : ℂ) := by
  unfold ratio phaseSign
  split_ifs with hl
  · have hh := low_spectral p hp0 hl
    constructor
    · exact_mod_cast hh.1
    · simpa using (show (matrixOff p : ℂ) - (lowRatio p : ℂ) * (matrixMean p : ℂ) = (lowRatio p : ℂ) by exact_mod_cast hh.2)
  · have hh := high_spectral p (lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm hne)) hp1
    constructor
    · exact_mod_cast hh.1
    · simpa using (show (matrixOff p : ℂ) - (highRatio p : ℂ) * (matrixMean p : ℂ) = -(highRatio p : ℂ) by exact_mod_cast hh.2)

lemma phaseSign_sq (p : ℝ) : phaseSign p ^ 2 = 1 := by unfold phaseSign; split_ifs <;> norm_num

lemma ratio_costs (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hne : p ≠ 1/2) :
    (1+ratio p ^ 2)/(1-ratio p ^ 2) = 1/|1-2*p| ∧
    ratio p ^ 2/(1-ratio p ^ 2) = min p (1-p)/|1-2*p| := by
  unfold ratio
  split_ifs with hl
  · rw [lowRatio_sq p hp0 hl,abs_of_pos (by linarith : 0 < 1-2*p),min_eq_left (by linarith)]
    have hn : 1-p ≠ 0 := by linarith
    have hm : 1-2*p ≠ 0 := by linarith
    constructor <;> field_simp [hn,hm] <;> ring
  · have hh : 1/2 < p := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm hne)
    rw [highRatio_sq p hh hp1,abs_of_neg (by linarith : 1-2*p < 0),min_eq_right (by linarith)]
    have hn : p ≠ 0 := by linarith
    have hm : 1-2*p ≠ 0 := by linarith
    constructor <;> field_simp [hn,hm] <;> ring_nf <;>
      simp only [show -1+p*2 = -(1-p*2) by ring, inv_neg] <;> ring

end ELV.Line
