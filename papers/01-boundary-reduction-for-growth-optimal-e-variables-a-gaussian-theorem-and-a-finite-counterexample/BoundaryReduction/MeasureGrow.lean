import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.EReal.Operations

open Real Set MeasureTheory InformationTheory
open scoped Classical ENNReal NNReal
namespace BoundaryReduction

/-- A measurable nonnegative e-variable with finite null expectation at most one. -/
structure MeasureEVar {α : Type*} [MeasurableSpace α] (P₀ : Measure α) where
  value : α → ℝ
  measurable : Measurable value
  nonneg : ∀ x, 0 ≤ value x
  integrable : Integrable value P₀
  mean_le_one : (∫ x, value x ∂P₀) ≤ 1

namespace MeasureGrow

lemma entropy_young_posLog {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) :
    u*max (log s) 0 ≤ klFun u+s := by
  by_cases hs1 : s ≤ 1
  · rw [max_eq_right (log_nonpos hs hs1), mul_zero]
    exact add_nonneg (klFun_nonneg hu) hs
  · have hsp : 0 < s := by linarith
    have hlog : 0 ≤ log s := (log_nonneg_iff hsp).mpr (by linarith)
    rw [max_eq_left hlog]
    by_cases hu0 : u = 0
    · simp [hu0, klFun]
      linarith
    · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have h := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hsp hup)) hu
      rw [log_div hsp.ne' hup.ne'] at h
      have heq : u*(s/u-1) = s-u := by field_simp
      rw [heq] at h
      dsimp [klFun]
      nlinarith

variable {α : Type*} [MeasurableSpace α]
variable {P₀ R : Measure α} [IsProbabilityMeasure P₀] [IsProbabilityMeasure R]

/-- Finite relative entropy makes the positive part of log S integrable,
without a positivity hypothesis on S. -/
theorem integrable_posLog {S : α → ℝ} (hS : Measurable S) (hS0 : ∀ x, 0 ≤ S x)
    (hSnull : Integrable S P₀) (hKL : klDiv R P₀ ≠ ∞) :
    Integrable (fun x => max (log (S x)) 0) R := by
  have hac := (klDiv_ne_top_iff.mp hKL).1
  have hllr := (klDiv_ne_top_iff.mp hKL).2
  have hkl := (integrable_klFun_rnDeriv_iff hac).mpr hllr
  have hmeas : AEStronglyMeasurable
      (fun x => (R.rnDeriv P₀ x).toReal*max (log (S x)) 0) P₀ :=
    (((Measure.measurable_rnDeriv R P₀).ennreal_toReal).mul (hS.log.max measurable_const)).aestronglyMeasurable
  have hw : Integrable (fun x => (R.rnDeriv P₀ x).toReal*max (log (S x)) 0) P₀ := by
    apply (hkl.add hSnull).mono' hmeas
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _))]
    exact entropy_young_posLog ENNReal.toReal_nonneg (hS0 x)
  exact (integrable_rnDeriv_smul_iff hac).mp (by simpa only [smul_eq_mul] using hw)

/-- The measure-theoretic information bound for an integrable logarithm. -/
theorem integral_log_le_kl_add_log_mean {S : α → ℝ}
    (hS : ∀ x, 0 < S x) (hSnull : Integrable S P₀)
    (hlog : Integrable (fun x => log (S x)) R) (hKL : klDiv R P₀ ≠ ∞) :
    (∫ x, log (S x) ∂R) ≤ (klDiv R P₀).toReal+log (∫ x, S x ∂P₀) := by
  have hac := (klDiv_ne_top_iff.mp hKL).1
  have hllr := (klDiv_ne_top_iff.mp hKL).2
  have heq : (fun x => exp (log (S x))) = S := by ext x; exact exp_log (hS x)
  have hexp : Integrable (fun x => exp (log (S x))) P₀ := by rwa [heq]
  letI := isProbabilityMeasure_tilted hexp
  have hat : R ≪ P₀.tilted (fun x => log (S x)) := hac.trans (absolutelyContinuous_tilted hexp)
  have htilt := integrable_llr_tilted_right hac hlog hllr hexp
  have hn := integral_llr_add_sub_measure_univ_nonneg hat htilt
  simp only [measureReal_univ_eq_one, add_sub_cancel_right] at hn
  rw [integral_llr_tilted_right hac hlog hexp hllr, heq] at hn
  have hreal := toReal_klDiv_of_measure_eq hac (by simp)
  linarith

/-- Adding a positive floor yields a truly integrable logarithm under R. -/
theorem integrable_log_add {S : α → ℝ} (hS : Measurable S) (hS0 : ∀ x, 0 ≤ S x)
    (hSnull : Integrable S P₀) (hKL : klDiv R P₀ ≠ ∞) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x => log (S x+δ)) R := by
  have hp := integrable_posLog (hS.add_const δ) (fun x => by linarith [hS0 x])
    (hSnull.add (integrable_const δ)) hKL
  apply (hp.add (integrable_const |log δ|)).mono' (hS.add_const δ).log.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  have hg : log δ ≤ log (S x+δ) := log_le_log hδ (by linarith [hS0 x])
  rcases le_total 0 (log (S x+δ)) with hsign | hsign
  · rw [abs_of_nonneg hsign, max_eq_left hsign]
    linarith [abs_nonneg (log δ)]
  · rw [abs_of_nonpos hsign, max_eq_right hsign]
    linarith [neg_le_abs (log δ)]

/-- Uniform truncated bound for all e-variables, including ones with zeros. -/
theorem evar_truncated_bound (S : MeasureEVar P₀) (hKL : klDiv R P₀ ≠ ∞)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ x, log (S.value x+δ) ∂R) ≤ (klDiv R P₀).toReal+log (1+δ) := by
  have hb := integral_log_le_kl_add_log_mean (S := fun x => S.value x+δ) (fun x => by linarith [S.nonneg x])
    (S.integrable.add (integrable_const δ))
    (integrable_log_add S.measurable S.nonneg S.integrable hKL hδ) hKL
  have hm : (∫ x, S.value x+δ ∂P₀) ≤ 1+δ := by
    have hs := integral_add S.integrable (integrable_const δ)
    simp only [Pi.add_apply] at hs
    rw [hs]
    simpa using add_le_add_right S.mean_le_one δ
  have hmpos : 0 < ∫ x, S.value x+δ ∂P₀ := by
    apply (integral_pos_iff_support_of_nonneg (f := fun x => S.value x+δ) (fun x => by change (0:ℝ) ≤ S.value x+δ; linarith [S.nonneg x])
      (S.integrable.add (integrable_const δ))).mpr
    have hs : Function.support (fun x => S.value x+δ) = Set.univ := by
      ext x
      have hx : S.value x+δ ≠ 0 := by linarith [S.nonneg x]
      simp [hx]
    simp [hs]
  exact hb.trans (add_le_add_left (log_le_log hmpos hm) _)

end MeasureGrow
end BoundaryReduction
