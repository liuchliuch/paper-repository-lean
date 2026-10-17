import Paper37.AdaptivePrediction
import Paper37.BoundaryHazard
import Paper37.LowerBound

/-! The deterministic-period endpoint, including arbitrary private randomness.
The threshold log n ≥32 is an explicit eventual condition, not a finite check. -/
noncomputable section
namespace Paper37.PeriodMinimax
open scoped BigOperators ENNReal
open Paper37.Renewal Paper37.Prediction Paper37.Boundary Paper37.AnalyticBounds
open MeasureTheory

lemma sqrt_ge_four_log {x : ℝ} (hx : 0 < x) (hlog : 32 ≤ Real.log x) :
    4*(1+Real.log x) ≤ Real.sqrt x := by
  have hL : 0 ≤ Real.log x/2 := by linarith
  have he := Real.quadratic_le_exp_of_nonneg hL
  have hx' : Real.exp (Real.log x/2) = Real.sqrt x := by
    have hs : Real.exp (Real.log x/2)^2 = x := by
      calc
        _ = Real.exp (Real.log x/2+Real.log x/2) := by rw [Real.exp_add]; ring
        _ = x := by rw [show Real.log x/2+Real.log x/2 = Real.log x by ring, Real.exp_log hx]
    have hsq := Real.sq_sqrt hx.le
    have he0 := Real.exp_pos (Real.log x/2)
    have hr0 := Real.sqrt_nonneg x
    nlinarith
  rw [hx'] at he
  nlinarith [sq_nonneg (Real.log x-32)]

lemma entropy_reciprocal_le {x : ℝ} (hx : 1 < x) :
    Real.binEntropy (1/x) ≤ (1+Real.log x)/x := by
  have hp : 0 < 1/x := one_div_pos.mpr (by linarith)
  have hp1 : 1/x < 1 := (div_lt_one (by linarith : 0 < x)).mpr hx
  have hs : 0 < 1-1/x := by linarith
  have hl := Real.log_le_sub_one_of_pos (one_div_pos.mpr hs)
  rw [one_div, Real.log_inv] at hl
  have hm := mul_le_mul_of_nonneg_left hl hs.le
  have hc : (1-1/x)*((1-1/x)⁻¹-1) = 1/x := by
    rw [mul_sub, mul_inv_cancel₀ hs.ne']
    ring
  rw [hc] at hm
  simp only [one_div] at hm
  rw [Real.binEntropy]
  simp only [one_div, inv_inv, Real.log_inv]
  have he : (1 + Real.log x) / x = x⁻¹ * Real.log x + x⁻¹ := by ring
  rw [he]
  nlinarith

lemma klReal_ge_linear {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    (1-p)*q - Real.binEntropy p ≤ klReal p q := by
  rw [klReal_eq_crossEntropy hq0.ne' hq1.ne]
  have hlq : Real.log q ≤ 0 := Real.log_nonpos hq0.le hq1.le
  have hl := Real.log_le_sub_one_of_pos (by linarith : 0 < 1-q)
  have hm := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ 1-p)
  have hpq := mul_nonpos_of_nonneg_of_nonpos hp0 hlq
  nlinarith

/-- A pointwise lower bound before integrating any private output distribution. -/
lemma period_two_losses {n : ℕ} (hn : 2 ≤ n) (hlog : 32 ≤ Real.log (n:ℝ))
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ENNReal.ofReal (Real.log n/(4*(n:ℝ))) ≤
      ENNReal.ofReal (1/((n:ℝ)+1))*kl 1 q +
        ENNReal.ofReal (1/2:ℝ)*kl (1/(n:ℝ)) q := by
  have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (1:ℝ)/n := one_div_pos.mpr hnp
  have hp1 : (1:ℝ)/n < 1 := (div_lt_one hnp).mpr (by linarith)
  by_cases hqz : q = 0
  · subst q
    simp only [kl_one_zero]
    rw [ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (one_div_pos.mpr (by positivity))))]
    simp
  by_cases hqo : q = 1
  · subst q
    rw [kl_right_one hp1.ne]
    norm_num
  have hq : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
  have hq' : q < 1 := lt_of_le_of_ne hq1 hqo
  have hr := Real.sqrt_pos.mpr hnp
  have hs := Real.sq_sqrt hnp.le
  have hlarge := sqrt_ge_four_log hnp hlog
  by_cases ht : q ≤ 1/Real.sqrt (n:ℝ)
  · have hl := Real.log_le_log hq ht
    rw [one_div, Real.log_inv, Real.log_sqrt hnp.le] at hl
    have hreal : Real.log n/(4*(n:ℝ)) ≤ (1/((n:ℝ)+1))*(-Real.log q) := by
      have hmul := mul_le_mul_of_nonneg_left (show Real.log (n:ℝ)/2 ≤ -Real.log q by linarith)
        (show 0 ≤ (1:ℝ)/((n:ℝ)+1) by positivity)
      have hh : Real.log n/(4*(n:ℝ)) ≤ (Real.log (n:ℝ)/2)/((n:ℝ)+1) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith
      calc
        _ ≤ (Real.log (n:ℝ)/2)/((n:ℝ)+1) := hh
        _ = (1/((n:ℝ)+1))*(Real.log (n:ℝ)/2) := by ring
        _ ≤ _ := hmul
    apply (ENNReal.ofReal_le_ofReal hreal).trans
    rw [ENNReal.ofReal_mul (by positivity), kl_one q hqz]
    exact le_add_right le_rfl
  · have hkl := klReal_ge_linear hp.le hp1.le hq hq'
    have hent := entropy_reciprocal_le (show (1:ℝ) < n by linarith)
    have hpHalf : (1:ℝ)/n ≤ 1/2 := by
      exact one_div_le_one_div_of_le (by norm_num) hn2
    have hqR : 1 < q*Real.sqrt (n:ℝ) := by
      apply (div_lt_iff₀ hr).mp
      exact lt_of_not_ge ht
    have hreal : Real.log n/(4*(n:ℝ)) ≤ (1/2:ℝ)*klReal (1/(n:ℝ)) q := by
      have hlin : q/2-(1+Real.log (n:ℝ))/(n:ℝ) ≤ klReal (1/(n:ℝ)) q := by
        have hmul := mul_le_mul_of_nonneg_right (show (1:ℝ)/2 ≤ 1-1/(n:ℝ) by linarith) hq.le
        linarith
      have hscalar : Real.log n/(4*(n:ℝ)) ≤ 1/(4*Real.sqrt (n:ℝ)) -
          (1+Real.log n)/(2*(n:ℝ)) := by
        apply le_sub_iff_add_le.mpr
        rw [show Real.log n/(4*(n:ℝ))+(1+Real.log n)/(2*(n:ℝ)) =
          (2+3*Real.log n)/(4*(n:ℝ)) by ring]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        have hm := mul_le_mul_of_nonneg_left
          (show 2+3*Real.log (n:ℝ) ≤ Real.sqrt (n:ℝ) by linarith) hr.le
        nlinarith
      have hqdiv : 1/(4*Real.sqrt (n:ℝ)) < q/4 := by
        apply (div_lt_iff₀ (by positivity)).2
        nlinarith
      have he : (1+Real.log n)/(2*(n:ℝ)) = (1/2:ℝ)*((1+Real.log n)/(n:ℝ)) := by ring
      rw [he] at hscalar
      linarith
    apply (ENNReal.ofReal_le_ofReal hreal).trans
    have hklEq : kl (1/(n:ℝ)) q = ENNReal.ofReal (klReal (1/(n:ℝ)) q) := by
      unfold kl
      rw [if_neg (by intro h; rcases h with h | h; exact hqz h.1; exact hqo h.1)]
    rw [ENNReal.ofReal_mul (by norm_num), ← hklEq]
    exact le_add_left le_rfl


/-- Source criterion restricted to every unknown deterministic positive period. -/
def periodRisk (n : ℕ) (q : RandomizedPredictor) : ℝ≥0∞ :=
  ⨆ a : ℕ, risk n q (pointLaw a)

def periodMinimax (n : ℕ) : ℝ≥0∞ := ⨅ q : RandomizedPredictor, periodRisk n q

lemma zero_contribution_le (n : ℕ) (q : RandomizedPredictor) (μ : Law) :
    ENNReal.ofReal (blockMass μ (List.replicate n false)) *
      (∫⁻ r : Set.Icc (0:ℝ) 1, kl (conditional μ (List.replicate n false)) r.val
        ∂(q (List.replicate n false)).toMeasure) ≤ risk n q μ := by
  unfold risk
  refine Finset.single_le_sum (s := (words n).toFinset)
    (f := fun x : List Bool => ENNReal.ofReal (blockMass μ x) *
      ∫⁻ r : Set.Icc (0:ℝ) 1, kl (conditional μ x) r.val ∂(q x).toMeasure)
    (a := List.replicate n false) (fun x hx => zero_le _) ?_
  exact List.mem_toFinset.mpr ((mem_words n _).mpr (by simp))

lemma two_period_zero_formulas {n : ℕ} (hn : 1 ≤ n) :
    blockMass (pointLaw n) (List.replicate n false) = 1/((n:ℝ)+1) ∧
    conditional (pointLaw n) (List.replicate n false) = 1 ∧
    blockMass (pointLaw (n+(n-1))) (List.replicate n false) = 1/2 ∧
    conditional (pointLaw (n+(n-1))) (List.replicate n false) = 1/(n:ℝ) := by
  have hsum : n+(n-1)+1 = 2*n := by omega
  have hsub : n+(n-1)+1-n = n := by omega
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hmean : (n+(n-1):ℕ) + 1 = 2*n := hsum
  have hcast : ((n+(n-1):ℕ):ℝ)+1 = 2*(n:ℝ) := by exact_mod_cast hsum
  simp only [blockMass_zeros,conditional_zeros,pointLaw_residual,pointLaw_mean,pointLaw_tail]
  rw [if_pos (by omega : n ≤ n), if_pos (by omega : n ≤ n+(n-1))]
  simp only [Nat.add_sub_cancel_left, Nat.cast_one, div_one, hsub, hcast]
  constructor
  · trivial
  constructor
  · trivial
  constructor
  · field_simp
  · trivial

/-- The pointwise two-period dichotomy is integrated for an arbitrary private
output law. Neither finite randomization nor an integrability condition is used. -/
theorem periodRisk_lower (n : ℕ) (hn : 2 ≤ n) (hlog : 32 ≤ Real.log (n:ℝ))
    (q : RandomizedPredictor) :
    ENNReal.ofReal (Real.log n/(8*(n:ℝ))) ≤ periodRisk n q := by
  let ν := (q (List.replicate n false)).toMeasure
  let A := ∫⁻ r : Set.Icc (0:ℝ) 1, kl 1 r.val ∂ν
  let B := ∫⁻ r : Set.Icc (0:ℝ) 1, kl (1/(n:ℝ)) r.val ∂ν
  have hpoint : ENNReal.ofReal (Real.log n/(4*(n:ℝ))) ≤
      ENNReal.ofReal (1/((n:ℝ)+1))*A + ENNReal.ofReal (1/2:ℝ)*B := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hmeas : Measurable (fun r : Set.Icc (0:ℝ) 1 =>
        ENNReal.ofReal (1/((n:ℝ)+1))*kl 1 r.val) :=
      measurable_const.mul ((measurable_kl_right 1).comp measurable_subtype_coe)
    rw [← lintegral_add_left hmeas]
    calc
      _ = ∫⁻ _r : Set.Icc (0:ℝ) 1, ENNReal.ofReal (Real.log n/(4*(n:ℝ))) ∂ν := by simp [ν]
      _ ≤ _ := lintegral_mono fun r => period_two_losses hn hlog r.property.1 r.property.2
  have hf := two_period_zero_formulas (show 1 ≤ n by omega)
  have h0 := zero_contribution_le n q (pointLaw n)
  have h1 := zero_contribution_le n q (pointLaw (n+(n-1)))
  rw [hf.1,hf.2.1] at h0
  rw [hf.2.2.1,hf.2.2.2] at h1
  have hsum : ENNReal.ofReal (Real.log n/(4*(n:ℝ))) ≤ periodRisk n q + periodRisk n q := by
    apply hpoint.trans
    exact add_le_add (h0.trans (le_iSup (fun a => risk n q (pointLaw a)) n))
      (h1.trans (le_iSup (fun a => risk n q (pointLaw a)) (n+(n-1))))
  by_contra h
  have hlt := ENNReal.add_lt_add (lt_of_not_ge h) (lt_of_not_ge h)
  have hc : 0 ≤ Real.log n/(8*(n:ℝ)) := div_nonneg (by linarith) (by positivity)
  rw [← ENNReal.ofReal_add hc hc,
    show Real.log n/(8*(n:ℝ))+Real.log n/(8*(n:ℝ)) = Real.log n/(4*(n:ℝ)) by ring] at hlt
  exact (not_lt_of_ge hsum) hlt

/-- The source lower bound permits every privately randomized predictor. -/
theorem periodMinimax_lower (n : ℕ) (hn : 2 ≤ n) (hlog : 32 ≤ Real.log (n:ℝ)) :
    ENNReal.ofReal (Real.log n/(8*(n:ℝ))) ≤ periodMinimax n :=
  le_iInf fun q => periodRisk_lower n hn hlog q

lemma period_occupied_le_one (a N : ℕ) :
    occupiedComplexity N (fun d => (pointLaw a).mass (d-1)) (mean (pointLaw a)) ≤ 1 := by
  unfold occupiedComplexity
  calc
    _ ≤ ∑ d ∈ Finset.Ico 1 N, if d = a+1 then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases h : d = a+1
      · rw [if_pos h]; exact min_le_left _ _
      · rw [if_neg h]
        have he : d-1 ≠ a := by have := Finset.mem_Ico.mp hd; omega
        simp [pointLaw,he]
    _ ≤ 1 := by simp; split_ifs <;> norm_num

/-- The same one predictor adapts to all unknown periods, giving E.6's upper
bound without receiving the period as input. -/
theorem periodMinimax_upper (n : ℕ) (hn : 0 < n) :
    periodMinimax n ≤ ENNReal.ofReal (10*Real.log (n+2:ℝ)/n) := by
  apply iInf_le_of_le (Paper37.AdaptivePrediction.sourcePredictor n hn)
  apply iSup_le
  intro a
  apply (Paper37.AdaptivePrediction.adaptive_risk_oracle (pointLaw a) n hn).trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have hv := period_occupied_le_one a (n+1)
  have hl : 0 ≤ Real.log (n+2:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n+2 by omega))
  have h2 : Real.log 2 ≤ Real.log (n+2:ℝ) := Real.log_le_log (by norm_num)
    (by exact_mod_cast (show 2 ≤ n+2 by omega))
  have hm := min_le_right (redundancyBound (n+1))
    ((2*occupiedComplexity (n+1) (fun d => (pointLaw a).mass (d-1)) (mean (pointLaw a))+6)*Real.log (n+2:ℝ))
  nlinarith

/-- Explicit eventual two-sided bounds: a precise Theta(log n/n) statement of
Proposition E.6 on the original unrestricted randomized minimax criterion. -/
theorem periodMinimax_rate :
    ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (Real.log n/(8*(n:ℝ))) ≤ periodMinimax n ∧
      periodMinimax n ≤ ENNReal.ofReal (20*Real.log n/(n:ℝ)) := by
  have hlog : ∀ᶠ n : ℕ in Filter.atTop, 32 ≤ Real.log (n:ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 32)
  filter_upwards [Filter.eventually_ge_atTop 2, hlog] with n hn hl
  refine ⟨periodMinimax_lower n hn hl, (periodMinimax_upper n (by omega)).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0:ℝ) < n := by linarith
  have harg : (n+2:ℝ) ≤ (n:ℝ)^2 := by nlinarith
  have h := Real.log_le_log (by positivity : (0:ℝ) < (n+2:ℝ)) harg
  rw [Real.log_pow] at h
  norm_num at h
  nlinarith

end Paper37.PeriodMinimax

