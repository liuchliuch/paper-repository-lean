import BoundaryReduction.MeasureGrow

open Real Set MeasureTheory InformationTheory
open scoped Classical ENNReal NNReal
namespace BoundaryReduction.MeasureGrow

variable {α : Type*} [MeasurableSpace α]

/-- The negative part of log, with the genuine value -∞ at zero. -/
noncomputable def logNegative (S : α → ℝ) (x : α) : ℝ≥0∞ :=
  if S x = 0 then ∞ else ENNReal.ofReal (-log (S x))

/-- Lebesgue expectation of the extended logarithm. Its positive part is finite
for every e-variable under a law of finite relative entropy. -/
noncomputable def logExpectation (P : Measure α) (S : α → ℝ) : EReal :=
  (↑(∫⁻ x, ENNReal.ofReal (log (S x)) ∂P) : EReal) -
    (↑(∫⁻ x, logNegative S x ∂P) : EReal)

lemma measurable_logNegative {S : α → ℝ} (hS : Measurable S) :
    Measurable (logNegative S) := by
  exact Measurable.ite (hS (measurableSet_singleton 0)) measurable_const hS.log.neg.ennreal_ofReal

lemma logNegative_toReal (S : α → ℝ) (x : α) :
    (logNegative S x).toReal = max (-log (S x)) 0 := by
  by_cases h : S x = 0 <;> simp [logNegative, h, ENNReal.toReal_ofReal', max_comm]

lemma logNegative_ae {P : Measure α} {S : α → ℝ}
    (hzero : ∀ᵐ x ∂P, S x ≠ 0) :
    logNegative S =ᵐ[P] fun x => ENNReal.ofReal (-log (S x)) := by
  filter_upwards [hzero] with x hx
  simp [logNegative, hx]

lemma lintegral_posLog_ne_top {P : Measure α} {S : α → ℝ}
    (hp : Integrable (fun x => max (log (S x)) 0) P) :
    (∫⁻ x, ENNReal.ofReal (log (S x)) ∂P) ≠ ∞ := by
  have heq : (fun x => ENNReal.ofReal (log (S x))) =
      (fun x => ENNReal.ofReal (max (log (S x)) 0)) := by
    ext x
    simp [ENNReal.ofReal_max]
  rw [heq]
  exact (lintegral_ofReal_ne_top_iff_integrable hp.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => le_max_right _ _))).mpr hp

lemma negative_finite_iff {P : Measure α} {S : α → ℝ} (hS : Measurable S)
    (hp : Integrable (fun x => max (log (S x)) 0) P) :
    (∫⁻ x, logNegative S x ∂P) ≠ ∞ ↔
      (∀ᵐ x ∂P, S x ≠ 0) ∧ Integrable (fun x => log (S x)) P := by
  constructor
  · intro hn
    have hae := ae_lt_top (measurable_logNegative hS) hn
    have hzero : ∀ᵐ x ∂P, S x ≠ 0 := by
      filter_upwards [hae] with x hx
      intro hz
      simpa [logNegative, hz] using hx
    have hi := integrable_toReal_of_lintegral_ne_top (measurable_logNegative hS).aemeasurable hn
    simp_rw [logNegative_toReal] at hi
    refine ⟨hzero, (hp.sub hi).congr ?_⟩
    exact Filter.Eventually.of_forall (fun x => by
      simp only [Pi.sub_apply]
      rcases le_total 0 (log (S x)) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]
        ring
      · rw [max_eq_right h, max_eq_left (by linarith)]
        ring)
  · rintro ⟨hz, hi⟩
    rw [lintegral_congr_ae (logNegative_ae hz)]
    have hn := (lintegral_ofReal_ne_top_iff_integrable hi.neg_part.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => le_max_right (-log (S x)) 0))).mpr hi.neg_part
    simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (zero_le _)] using hn

lemma logExpectation_eq_integral {P : Measure α} {S : α → ℝ}
    (hzero : ∀ᵐ x ∂P, S x ≠ 0) (hi : Integrable (fun x => log (S x)) P) :
    logExpectation P S = (↑(∫ x, log (S x) ∂P) : EReal) := by
  have hp := lintegral_posLog_ne_top hi.pos_part
  have hn : (∫⁻ x, ENNReal.ofReal (-log (S x)) ∂P) ≠ ∞ := by
    have hh := (lintegral_ofReal_ne_top_iff_integrable hi.neg_part.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => le_max_right (-log (S x)) 0))).mpr hi.neg_part
    simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (zero_le _)] using hh
  rw [logExpectation, lintegral_congr_ae (logNegative_ae hzero),
    ← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
    ← EReal.coe_sub, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi]

lemma logExpectation_eq_bot {P : Measure α} {S : α → ℝ} (hS : Measurable S)
    (hp : Integrable (fun x => max (log (S x)) 0) P)
    (hbad : ¬ ((∀ᵐ x ∂P, S x ≠ 0) ∧ Integrable (fun x => log (S x)) P)) :
    logExpectation P S = ⊥ := by
  have hn : (∫⁻ x, logNegative S x ∂P) = ∞ := by
    by_contra hh
    exact hbad ((negative_finite_iff hS hp).mp hh)
  simp [logExpectation, hn, EReal.sub_top]

variable {P₀ R : Measure α} [IsProbabilityMeasure P₀] [IsProbabilityMeasure R]

lemma evar_integral_log_bound (S : MeasureEVar P₀) (hKL : klDiv R P₀ ≠ ∞)
    (hz : ∀ᵐ x ∂R, S.value x ≠ 0) (hi : Integrable (fun x => log (S.value x)) R) :
    (∫ x, log (S.value x) ∂R) ≤ (klDiv R P₀).toReal := by
  have hδ : ∀ δ : ℝ, 0 < δ →
      (∫ x, log (S.value x) ∂R) ≤ (klDiv R P₀).toReal+log (1+δ) := by
    intro δ hδ
    apply le_trans (integral_mono_ae hi
      (integrable_log_add S.measurable S.nonneg S.integrable hKL hδ) ?_)
      (evar_truncated_bound S hKL hδ)
    filter_upwards [hz] with x hx
    exact log_le_log (lt_of_le_of_ne (S.nonneg x) (Ne.symm hx)) (by linarith)
  by_contra hh
  have hgap : 0 < (∫ x, log (S.value x) ∂R)-(klDiv R P₀).toReal := sub_pos.mpr (lt_of_not_ge hh)
  let a := ((∫ x, log (S.value x) ∂R)-(klDiv R P₀).toReal)/2
  have ha : 0 < a := by dsimp [a]; linarith
  have he : 0 < exp a-1 := sub_pos.mpr ((one_lt_exp_iff).mpr ha)
  have hb := hδ (exp a-1) he
  have heq : 1+(exp a-1) = exp a := by ring
  rw [heq, log_exp] at hb
  dsimp [a] at hb
  linarith

/-- General entropy bound, including the cases S=0 and an infinite negative
logarithmic part. No integrability of log S is assumed. -/
theorem evar_logExpectation_le_kl (S : MeasureEVar P₀) (hKL : klDiv R P₀ ≠ ∞) :
    logExpectation R S.value ≤ (↑(klDiv R P₀) : EReal) := by
  by_cases hg : (∀ᵐ x ∂R, S.value x ≠ 0) ∧ Integrable (fun x => log (S.value x)) R
  · rw [logExpectation_eq_integral hg.1 hg.2, ← EReal.coe_ennreal_toReal hKL]
    exact_mod_cast evar_integral_log_bound S hKL hg.1 hg.2
  · rw [logExpectation_eq_bot S.measurable
      (integrable_posLog S.measurable S.nonneg S.integrable hKL) hg]
    exact bot_le

/-- The full entropy inequality (2.9), including zeros and an infinite
negative logarithmic part, when the null mean is positive. -/
theorem evar_logExpectation_le_kl_add_log_mean (S : MeasureEVar P₀)
    (hKL : klDiv R P₀ ≠ ∞) (hm : 0 < ∫ x, S.value x ∂P₀) :
    logExpectation R S.value ≤ (↑(klDiv R P₀) : EReal)+
      (↑(log (∫ x, S.value x ∂P₀)) : EReal) := by
  by_cases hg : (∀ᵐ x ∂R, S.value x ≠ 0) ∧ Integrable (fun x => log (S.value x)) R
  · let m := ∫ x, S.value x ∂P₀
    have hm0 : 0 < m := hm
    let T : MeasureEVar P₀ :=
      ⟨fun x => S.value x/m,S.measurable.div_const m,
        fun x => div_nonneg (S.nonneg x) hm0.le,S.integrable.div_const m,by
          rw [integral_div]
          change m/m ≤ 1
          rw [div_self hm0.ne']⟩
    have hzT : ∀ᵐ x ∂R, T.value x ≠ 0 := hg.1.mono (fun x hx => div_ne_zero hx hm0.ne')
    have hlogeq : (fun x => log (T.value x)) =ᵐ[R] fun x => log (S.value x)-log m :=
      hg.1.mono (fun x hx => log_div hx hm0.ne')
    have hiT : Integrable (fun x => log (T.value x)) R :=
      (hg.2.sub (integrable_const (log m))).congr (Filter.EventuallyEq.symm hlogeq)
    have hb := evar_integral_log_bound T hKL hzT hiT
    rw [integral_congr_ae hlogeq,integral_sub hg.2 (integrable_const (log m))] at hb
    simp only [integral_const,measureReal_univ_eq_one,smul_eq_mul,one_mul] at hb
    rw [logExpectation_eq_integral hg.1 hg.2,← EReal.coe_ennreal_toReal hKL,← EReal.coe_add]
    exact_mod_cast (show (∫ x, log (S.value x) ∂R) ≤ (klDiv R P₀).toReal+log m by linarith)
  · rw [logExpectation_eq_bot S.measurable
      (integrable_posLog S.measurable S.nonneg S.integrable hKL) hg]
    exact bot_le

/-- The extended expectation is always below +∞ under finite KL. -/
theorem evar_logExpectation_lt_top (S : MeasureEVar P₀) (hKL : klDiv R P₀ ≠ ∞) :
    logExpectation R S.value < ⊤ := by
  by_cases hg : (∀ᵐ x ∂R, S.value x ≠ 0) ∧ Integrable (fun x => log (S.value x)) R
  · rw [logExpectation_eq_integral hg.1 hg.2]
    simp
  · rw [logExpectation_eq_bot S.measurable
      (integrable_posLog S.measurable S.nonneg S.integrable hKL) hg]
    exact bot_lt_top

/-- The m=0 case in the proof of Lemma 2.1. -/
theorem evar_zero_mean (S : MeasureEVar P₀) (hKL : klDiv R P₀ ≠ ∞)
    (hm : (∫ x, S.value x ∂P₀) = 0) : logExpectation R S.value = ⊥ := by
  have hz0 := (integral_eq_zero_iff_of_nonneg S.nonneg S.integrable).mp hm
  have hz : ∀ᵐ x ∂R, S.value x = 0 := (klDiv_ne_top_iff.mp hKL).1.ae_le hz0
  have hp : (fun x => ENNReal.ofReal (log (S.value x))) =ᵐ[R] fun _ => 0 :=
    hz.mono (fun x hx => by simp [hx])
  have hn : logNegative S.value =ᵐ[R] fun _ => ∞ :=
    hz.mono (fun x hx => by simp [logNegative,hx])
  rw [logExpectation,lintegral_congr_ae hp,lintegral_congr_ae hn]
  simp [EReal.sub_top]

end BoundaryReduction.MeasureGrow
