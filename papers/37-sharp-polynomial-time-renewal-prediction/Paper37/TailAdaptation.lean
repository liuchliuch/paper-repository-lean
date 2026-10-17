import Paper37.AdaptivePrediction
import Paper37.RateUpper

/-! Explicit finite-sample forms of all three source rates in Corollary E.5.
The same implemented adaptive predictor is used in every statement. Constants
are displayed and bounds hold for every `n ≥ 2`, rather than only eventually. -/
namespace Paper37.TailAdaptation

open Finset Renewal Prediction AnalyticBounds AdaptivePrediction
open scoped ENNReal

noncomputable def universalConstant : ℝ :=
  2*Real.pi/Real.sqrt 3 + 3*Real.sqrt 2 + Real.log 2

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

lemma log_bounds {n : ℕ} (hn : 2 ≤ n) :
    0 < Real.log (n : ℝ) ∧ Real.log 2 ≤ Real.log (n : ℝ) ∧
      Real.log ((n : ℝ)+2) ≤ 2*Real.log (n : ℝ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) := by linarith
  have hl := Real.log_le_log (by norm_num : 0 < (2 : ℝ)) hn'
  refine ⟨log_two_pos.trans_le hl, hl, ?_⟩
  have hsq : (n : ℝ)+2 ≤ (n : ℝ)^2 := by nlinarith
  have h := Real.log_le_log (by linarith : 0 < (n : ℝ)+2) hsq
  rw [Real.log_pow] at h
  norm_num at h
  exact h

/-- The universal square-root branch, retained automatically by the adaptive mixture. -/
theorem adaptive_universal_risk (μ : Law) (n : ℕ) (hn : 2 ≤ n) :
    risk n (sourcePredictor n (by omega)) μ ≤
      ENNReal.ofReal (universalConstant / Real.sqrt n) := by
  apply (adaptive_risk_oracle μ n (by omega)).trans
  apply ENNReal.ofReal_le_ofReal
  have hmin := min_le_left (redundancyBound (n+1))
    ((2*occupiedComplexity (n+1) (fun d => μ.mass (d-1)) (mean μ)+6)*Real.log (n+2 : ℝ))
  have hpre : (Real.log 2 + min (redundancyBound (n+1))
      ((2*occupiedComplexity (n+1) (fun d => μ.mass (d-1)) (mean μ)+6)*Real.log (n+2 : ℝ)) +
      Real.log (n+2 : ℝ)) / n ≤
      Real.log 2 / n + (redundancyBound (n+1)+Real.log (n+2 : ℝ))/n := by
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)).2
    linarith
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsn : Real.sqrt (n : ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hdiv := div_le_div_of_nonneg_left log_two_pos.le hs hsn
  have hfixed := fixed_time_explicit_constant (show 1 ≤ n by omega)
  apply hpre.trans
  calc
    _ ≤ Real.log 2 / Real.sqrt n + (2*Real.pi/Real.sqrt 3 + 3*Real.sqrt 2) / Real.sqrt n :=
      add_le_add hdiv hfixed
    _ = universalConstant / Real.sqrt n := by unfold universalConstant; ring

/-- The occupied-type branch of the actual adaptive oracle, in a convenient linear form. -/
theorem adaptive_occupancy_risk (μ : Law) (n : ℕ) (hn : 2 ≤ n) :
    risk n (sourcePredictor n (by omega)) μ ≤ ENNReal.ofReal
      ((Real.log 2 + (2*occupiedComplexity (n+1) (fun d => μ.mass (d-1)) (mean μ)+7)*
        Real.log (n+2 : ℝ))/n) := by
  apply (adaptive_risk_oracle μ n (by omega)).trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have hmin := min_le_right (redundancyBound (n+1))
    ((2*occupiedComplexity (n+1) (fun d => μ.mass (d-1)) (mean μ)+6)*Real.log (n+2 : ℝ))
  nlinarith

/-- Source support cardinality is transported correctly from gap-minus-one to
positive gaps; the extra sentinel zero is harmless in the finite occupancy bound. -/
lemma occupiedComplexity_support (μ : Law) (N s : ℕ) (S : Finset ℕ)
    (hS : ∀ d, d ∉ S → μ.mass d = 0) (hcard : S.card ≤ s) :
    occupiedComplexity N (fun d => μ.mass (d-1)) (mean μ) ≤ s+1 := by
  let T := insert 0 (S.image Nat.succ)
  have hT : ∀ d, d ∉ T → μ.mass (d-1) = 0 := by
    intro d hd
    apply hS
    intro hmem
    apply hd
    apply mem_insert_of_mem
    apply mem_image.mpr
    refine ⟨d-1, hmem, ?_⟩
    have hd0 : d ≠ 0 := by intro h; apply hd; simp [T, h]
    omega
  have hb := occupiedComplexity_le_support N (fun d => μ.mass (d-1)) (mean μ) T hT
  have htc : T.card ≤ s+1 :=
    (card_insert_le _ _).trans (Nat.add_le_add_right ((card_image_le).trans hcard) 1)
  exact hb.trans (by exact_mod_cast htc)

/-- E.5(1): one explicit bound retains both the minimax rate and finite-support adaptation. -/
theorem finite_support_rate (μ : Law) (s : ℕ) (S : Finset ℕ)
    (hS : ∀ d, d ∉ S → μ.mass d = 0) (hcard : S.card ≤ s)
    (n : ℕ) (hn : 2 ≤ n) :
    risk n (sourcePredictor n (by omega)) μ ≤ ENNReal.ofReal
      (min (universalConstant / Real.sqrt n) (19*(s+1 : ℝ)*Real.log (n : ℝ)/n)) := by
  rw [ENNReal.ofReal_min]
  apply le_min (adaptive_universal_risk μ n hn)
  apply (adaptive_occupancy_risk μ n hn).trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have hv := occupiedComplexity_support μ (n+1) s S hS hcard
  have hl := log_bounds hn
  have hL : 0 ≤ Real.log (n+2 : ℝ) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hcoef : 0 ≤ 2*(s+1 : ℝ)+7 := by positivity
  have h1 := mul_le_mul_of_nonneg_right (by linarith :
    2*occupiedComplexity (n+1) (fun d => μ.mass (d-1)) (mean μ)+7 ≤ 2*(s+1 : ℝ)+7) hL
  have h2 := mul_le_mul_of_nonneg_left hl.2.2 hcoef
  have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
  nlinarith

noncomputable def exponentialConstant (C c : ℝ) : ℝ :=
  8/c + (4*(C/(1-Real.exp (-c)))+19) / Real.log 2

/-- E.5(2), with a displayed constant depending only on the tail parameters. -/
theorem exponential_tail_rate (μ : Law) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (htail : ∀ d : ℕ, 1 ≤ d → μ.mass (d-1) ≤ C * Real.exp (-c*d))
    (n : ℕ) (hn : 2 ≤ n) :
    risk n (sourcePredictor n (by omega)) μ ≤ ENNReal.ofReal
      (exponentialConstant C c * (Real.log (n : ℝ))^2 / n) := by
  apply (adaptive_occupancy_risk μ n hn).trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have hv := occupiedComplexity_le_exponential (n+1) (show 1 ≤ n+1 by omega)
    (fun d => μ.nonneg (d-1)) (mean_ge_one μ) hC hc htail
  have hl := log_bounds hn
  have hNlog : Real.log (n+1 : ℝ) ≤ 2*Real.log (n : ℝ) :=
    (Real.log_le_log (by positivity : 0 < (n+1 : ℝ)) (by norm_num)).trans hl.2.2
  have hden : 0 < 1-Real.exp (-c) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hD : 0 ≤ C/(1-Real.exp (-c)) := div_nonneg hC hden.le
  have hv' : occupiedComplexity (n+1) (fun d => μ.mass (d-1)) (mean μ) ≤
      (2/c)*Real.log (n : ℝ) + 1 + C/(1-Real.exp (-c)) := by
    have hd := div_le_div_of_nonneg_right hNlog hc.le
    push_cast at hv
    have hd' : Real.log (n+1 : ℝ) / c ≤ (2/c)*Real.log (n : ℝ) := by
      convert hd using 1 <;> ring
    exact hv.trans (by linarith)
  have hL : 0 ≤ Real.log (n+2 : ℝ) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hcoef : 0 ≤ 2*((2/c)*Real.log (n : ℝ)+1+C/(1-Real.exp (-c)))+7 := by positivity
  have h1 := mul_le_mul_of_nonneg_right (by linarith :
    2*occupiedComplexity (n+1) (fun d => μ.mass (d-1)) (mean μ)+7 ≤
      2*((2/c)*Real.log (n : ℝ)+1+C/(1-Real.exp (-c)))+7) hL
  have h2 := mul_le_mul_of_nonneg_left hl.2.2 hcoef
  have hlogquad : (4*(C/(1-Real.exp (-c)))+19)*Real.log (n : ℝ) ≤
      ((4*(C/(1-Real.exp (-c)))+19)/Real.log 2) * (Real.log (n : ℝ))^2 := by
    calc
      _ ≤ ((4*(C/(1-Real.exp (-c)))+19) * (Real.log (n : ℝ))^2) / Real.log 2 := by
        apply (le_div_iff₀ log_two_pos).mpr
        have hm := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hl.2.1 hl.1.le)
          (by linarith : 0 ≤ 4*(C/(1-Real.exp (-c)))+19)
        nlinarith
      _ = _ := by ring
  calc
    _ ≤ Real.log (n : ℝ) +
        (2*((2/c)*Real.log (n : ℝ)+1+C/(1-Real.exp (-c)))+7)*(2*Real.log (n : ℝ)) :=
      add_le_add hl.2.1 (h1.trans h2)
    _ = (8/c)*(Real.log (n : ℝ))^2 +
        (4*(C/(1-Real.exp (-c)))+19)*Real.log (n : ℝ) := by ring
    _ ≤ (8/c)*(Real.log (n : ℝ))^2 +
        ((4*(C/(1-Real.exp (-c)))+19)/Real.log 2)*(Real.log (n : ℝ))^2 :=
      add_le_add_left hlogquad _
    _ = exponentialConstant C c * (Real.log (n : ℝ))^2 := by unfold exponentialConstant; ring

noncomputable def powerConstant (C α : ℝ) : ℝ := 27 + 12*C/(α-1)

/-- E.5(3), with all quantifiers and the exact negative power made explicit. -/
theorem power_tail_rate (μ : Law) (C α : ℝ) (hC : 0 ≤ C) (hα : 2 < α)
    (htail : ∀ d : ℕ, 1 ≤ d → μ.mass (d-1) ≤ C * (d : ℝ)^(-α))
    (n : ℕ) (hn : 2 ≤ n) :
    risk n (sourcePredictor n (by omega)) μ ≤ ENNReal.ofReal
      (powerConstant C α * (n : ℝ)^(-(1-1/α)) * Real.log (n : ℝ)) := by
  apply (adaptive_occupancy_risk μ n hn).trans
  apply ENNReal.ofReal_le_ofReal
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hr : 0 ≤ 1/α := by positivity
  have hr1 : 1/α ≤ 1 := (div_le_one (by linarith : 0 < α)).mpr (by linarith)
  have hu : 1 ≤ (n : ℝ)^(1/α) := Real.one_le_rpow hn1 hr
  have hshift : (n+1 : ℝ)^(1/α) ≤ 2*(n : ℝ)^(1/α) := by
    calc
      _ ≤ (2*(n : ℝ))^(1/α) := Real.rpow_le_rpow (by positivity) (by linarith) hr
      _ = (2 : ℝ)^(1/α) * (n : ℝ)^(1/α) := Real.mul_rpow (by norm_num) hnp.le
      _ ≤ 2*(n : ℝ)^(1/α) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hnp.le _)
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hr1
  have hv := occupiedComplexity_le_power (n+1) (show 1 ≤ n+1 by omega)
    (fun d => μ.nonneg (d-1)) (mean_ge_one μ) hC (show 1 < α by linarith) htail
  have ha1 : 0 < α-1 := by linarith
  have hA : 0 ≤ 1+C/(α-1) := add_nonneg zero_le_one (div_nonneg hC ha1.le)
  have hv' : occupiedComplexity (n+1) (fun d => μ.mass (d-1)) (mean μ) ≤
      3*(1+C/(α-1))*(n : ℝ)^(1/α) := by
    push_cast at hv
    have hm := mul_le_mul_of_nonneg_left hshift hA
    have hm' := mul_le_mul_of_nonneg_left hu hA
    nlinarith
  have hl := log_bounds hn
  have hL : 0 ≤ Real.log (n+2 : ℝ) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hcoef : 0 ≤ 6*(1+C/(α-1))*(n : ℝ)^(1/α)+7 := by positivity
  have h1 := mul_le_mul_of_nonneg_right (by linarith :
    2*occupiedComplexity (n+1) (fun d => μ.mass (d-1)) (mean μ)+7 ≤
      6*(1+C/(α-1))*(n : ℝ)^(1/α)+7) hL
  have h2 := mul_le_mul_of_nonneg_left hl.2.2 hcoef
  have hpow : (n : ℝ)^(-(1-1/α)) = (n : ℝ)^(1/α) / n := by
    have he : -(1-1/α) = 1/α-1 := by ring
    rw [he, Real.rpow_sub hnp, Real.rpow_one]
  have hnum : Real.log 2 +
      (2*occupiedComplexity (n+1) (fun d => μ.mass (d-1)) (mean μ)+7)*Real.log (n+2 : ℝ) ≤
      powerConstant C α * (n : ℝ)^(1/α) * Real.log (n : ℝ) := by
    calc
      _ ≤ Real.log (n : ℝ) +
          (6*(1+C/(α-1))*(n : ℝ)^(1/α)+7)*(2*Real.log (n : ℝ)) :=
        add_le_add hl.2.1 (h1.trans h2)
      _ = 12*(1+C/(α-1))*(n : ℝ)^(1/α)*Real.log (n : ℝ)+15*Real.log (n : ℝ) := by ring
      _ ≤ 12*(1+C/(α-1))*(n : ℝ)^(1/α)*Real.log (n : ℝ)+
          15*((n : ℝ)^(1/α)*Real.log (n : ℝ)) := by
        apply add_le_add_left
        exact mul_le_mul_of_nonneg_left (by simpa using mul_le_mul_of_nonneg_right hu hl.1.le) (by norm_num)
      _ = _ := by unfold powerConstant; ring
  calc
    _ ≤ (powerConstant C α * (n : ℝ)^(1/α) * Real.log (n : ℝ))/n :=
      div_le_div_of_nonneg_right hnum hnp.le
    _ = powerConstant C α * (n : ℝ)^(-(1-1/α)) * Real.log (n : ℝ) := by rw [hpow]; ring


lemma universalConstant_pos : 0 < universalConstant := by
  have hp := Real.pi_pos
  have hs := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)
  have hl := log_two_pos
  unfold universalConstant
  positivity

lemma exponentialConstant_pos (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    0 < exponentialConstant C c := by
  have hd : 0 < 1-Real.exp (-c) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hl := log_two_pos
  unfold exponentialConstant
  positivity

lemma powerConstant_pos (C α : ℝ) (hC : 0 ≤ C) (hα : 2 < α) :
    0 < powerConstant C α := by
  have ha : 0 < α-1 := by linarith
  unfold powerConstant
  positivity

end Paper37.TailAdaptation
