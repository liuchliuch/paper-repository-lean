import Paper36.Target
import Paper36.HybridCharging

/-! Exact numerical conversions for the source posterior simulation constants. -/
namespace Paper36.Bounds
noncomputable section

def budget (s a h : ℝ) (K : ℕ) : ℝ := 8*s*a*h*(K : ℝ)^2

def rewardLog (s a h : ℝ) (K : ℕ) : ℝ := s*Real.log 2 + Real.log (budget s a h K)

def certificateBudget (s a h δ : ℝ) (K : ℕ) : ℝ := 4*s*a*h*(K : ℝ)^2/δ

def certificateLog (s a h δ : ℝ) (K : ℕ) : ℝ :=
  s*Real.log ((K : ℝ)*h+1) + Real.log (certificateBudget s a h δ K)

def ell (δ : ℝ) : ℝ := Real.log (4/δ)

def certificate (s a h W w δ : ℝ) (K : ℕ) : ℝ :=
  w*(4*s*a*h+2*h*ell δ) + 4*W*Real.sqrt
    (certificateLog s a h δ K*(K : ℝ)*(4*s*a*Real.log (Real.exp 1*(K : ℝ)*h)+2*ell δ))

lemma budget_lower {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h)
    {K : ℕ} (hK : 1 ≤ K) : 8 ≤ budget s a h K := by
  have hsa := one_le_mul_of_one_le_of_one_le hs ha
  have hsah := one_le_mul_of_one_le_of_one_le hsa hh
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hk2 : (1 : ℝ) ≤ (K : ℝ)^2 := by nlinarith
  have hprod := one_le_mul_of_one_le_of_one_le hsah hk2
  unfold budget
  nlinarith

lemma Lambda_nonneg {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h)
    {K : ℕ} (hK : 1 ≤ K) : 0 ≤ Target.Lambda s a h K := by
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hkh := one_le_mul_of_one_le_of_one_le hk hh
  have hl1 : 0 ≤ Real.log ((K : ℝ)*h+1) := Real.log_nonneg (by linarith)
  have hl2 : 0 ≤ Real.log (8*s*a*h*(K : ℝ)^2) :=
    Real.log_nonneg ((show (1 : ℝ) ≤ 8 by norm_num).trans (budget_lower hs ha hh hK))
  exact add_nonneg (mul_nonneg (by linarith) hl1) hl2

/-- The high-count expectation expression is literally C_K sqrt(K). -/
theorem expected_high_eq_confidence {s a h W : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a)
    (hh : 1 ≤ h) (K : ℕ) (hK : 1 ≤ K) :
    4*W*Real.sqrt (Target.Lambda s a h K*(K : ℝ)*
      (2*(s*a)*Real.log (Real.exp 1*(K : ℝ)*h))) =
      Target.confidence (Target.scale W s a) s a h K * Real.sqrt (K : ℝ) := by
  have hΛ := Lambda_nonneg hs ha hh hK
  have hlog : 0 ≤ Real.log (Real.exp 1*(K : ℝ)*h) := by
    have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
    exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le he hk) hh)
  have hs0 : 0 ≤ s := by linarith
  have ha0 : 0 ≤ a := by linarith
  let X := s*a*Target.Lambda s a h K*Real.log (Real.exp 1*(K : ℝ)*h)
  let Y := Target.Lambda s a h K*(K : ℝ)*(2*(s*a)*Real.log (Real.exp 1*(K : ℝ)*h))
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hsq : (Real.sqrt 2*Real.sqrt X*Real.sqrt (K : ℝ))^2 = Y := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt hX, Real.sq_sqrt (Nat.cast_nonneg K)]
    dsimp [X, Y]
    ring
  have heq : Real.sqrt Y = Real.sqrt 2*Real.sqrt X*Real.sqrt (K : ℝ) := by
    have hy := Real.sq_sqrt hY
    have hpos : 0 ≤ Real.sqrt 2*Real.sqrt X*Real.sqrt (K : ℝ) := by positivity
    nlinarith [Real.sqrt_nonneg Y]
  rw [Target.confidence_source_formula hs0 ha0]
  change 4*W*Real.sqrt Y = _
  rw [heq]
  dsimp [X]
  ring

/-- Frozen-count plus confidence budgets yield precisely 1/(8K) per current model. -/
lemma budget_charge {s a h : ℝ} (hs : 0 < s) (ha : 0 < a) (hh : 0 < h)
    {K : ℕ} (hK : 0 < K) : (s*a)*((K : ℝ)*h)/budget s a h K = 1/(8*(K : ℝ)) := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  unfold budget
  field_simp

lemma rewardLog_one_le {s a h : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h)
    {K : ℕ} (hK : 1 ≤ K) : 1 ≤ rewardLog s a h K := by
  have hlog2 : (1 : ℝ)/2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog8 : Real.log 8 = 3*Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 3
    norm_num at h
    exact h
  have hb := budget_lower hs ha hh hK
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 8) hb
  unfold rewardLog
  rw [hlog8] at hl
  have hslog : 0 ≤ s*Real.log 2 := mul_nonneg (by linarith) (by linarith)
  linarith

/-- The high-count reward term matches the source's H^(3/2) scale exactly. -/
theorem reward_high_factor {R h K L : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h)
    (hK : 0 ≤ K) (hL : 0 ≤ L) :
    h*Real.sqrt (2*L)*(3*Real.sqrt (R*K*h)) =
      3*Real.sqrt 2*(h*Real.sqrt h*Real.sqrt (R*K*L)) := by
  have hx : 0 ≤ 2*L := by positivity
  have hy : 0 ≤ R*K*h := by positivity
  have hz : 0 ≤ R*K*L := by positivity
  have hsq : (Real.sqrt (2*L)*Real.sqrt (R*K*h))^2 =
      (Real.sqrt 2*Real.sqrt h*Real.sqrt (R*K*L))^2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hh, Real.sq_sqrt hz]
    ring
  have heq : Real.sqrt (2*L)*Real.sqrt (R*K*h) =
      Real.sqrt 2*Real.sqrt h*Real.sqrt (R*K*L) := by
    have h1 : 0 ≤ Real.sqrt (2*L)*Real.sqrt (R*K*h) := by positivity
    have h2 : 0 ≤ Real.sqrt 2*Real.sqrt h*Real.sqrt (R*K*L) := by positivity
    nlinarith
  calc
    _ = 3*h*(Real.sqrt (2*L)*Real.sqrt (R*K*h)) := by ring
    _ = _ := by rw [heq]; ring

lemma certificateBudget_one_le {s a h δ : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (hδ : 0 < δ) (hδ1 : δ < 1) {K : ℕ} (hK : 1 ≤ K) :
    1 ≤ certificateBudget s a h δ K := by
  have hb := budget_lower hs ha hh hK
  unfold certificateBudget budget at *
  apply (le_div_iff₀ hδ).2
  nlinarith

lemma ell_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : 0 < ell δ := by
  apply Real.log_pos
  exact (lt_div_iff₀ hδ).2 (by linarith)

lemma exp_neg_ell {δ : ℝ} (hδ : 0 < δ) : Real.exp (-ell δ) = δ/4 := by
  unfold ell
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 4/δ)]
  field_simp

lemma certificate_budget_charge {s a h δ : ℝ} (hs : 0 < s) (ha : 0 < a) (hh : 0 < h)
    (hδ : 0 < δ) {K : ℕ} (hK : 0 < K) :
    (s*a)*((K : ℝ)*h)/certificateBudget s a h δ K = δ/(4*(K : ℝ)) := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  unfold certificateBudget
  field_simp

end
end Paper36.Bounds
