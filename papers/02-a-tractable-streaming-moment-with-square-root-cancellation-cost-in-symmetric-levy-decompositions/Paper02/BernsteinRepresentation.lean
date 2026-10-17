import Paper02.Bernstein
import Paper02.GaussianMixture
import Paper02.MeasureDual
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Explicit positive Bernstein representing measures

This file gives actual positive measures and computes their Laplace integrals.
It does not assume a representation theorem for analytic Pick functions.
The general analytic-to-measure representation remains a separate theorem.
-/

noncomputable section
namespace Paper02.Bernstein
open MeasureTheory ProbabilityTheory Set Real

/-- The positive-measure representation (B.1), with its original integrability
and support conditions. This is distinct from the analytic characterization;
the implication between them is not assumed. -/
def HasBernsteinRepresentation (φ : ℝ → ℝ) : Prop :=
  ∃ (b : ℝ) (μ : Measure ℝ), 0 ≤ b ∧ μ.restrict (Iic 0) = 0 ∧
    Integrable (fun u : ℝ => min u 1) μ ∧
    ∀ t : ℝ, 0 ≤ t → φ t = b * t + ∫ u, (1 - exp (-u * t)) ∂μ

/-- The measure-theoretic subordination step (B.2), from the actual positive
representation (B.1), without a finiteness or σ-finiteness assumption on μ. -/
theorem isLSym_comp_square_of_representation {φ : ℝ → ℝ}
    (hφ : HasBernsteinRepresentation φ) : IsLSym (fun x : ℝ => φ (x ^ 2)) := by
  rcases hφ with ⟨b, μ, hb, hsupport, hμ, heq⟩
  have hpos : ∀ᵐ u ∂μ, 0 ≤ u := by
    have hr := Measure.restrict_add_restrict_compl (μ := μ)
      (s := Ioi (0 : ℝ)) measurableSet_Ioi
    have hrestrict : μ.restrict (Ioi 0) = μ := by
      simpa only [compl_Ioi, hsupport, add_zero] using hr
    have hp := ae_restrict_mem (μ := μ) (s := Ioi (0 : ℝ)) measurableSet_Ioi
    rw [hrestrict] at hp
    exact hp.mono (fun _ hu => le_of_lt hu)
  have h := LSym.isLSym_add (isLSym_gaussian hb)
    (isLSym_gaussian_mixture μ hpos hμ)
  have hfun : (fun x : ℝ => φ (x ^ 2)) =
      (fun x : ℝ => b * x ^ 2 + ∫ u, (1 - exp (-u * x ^ 2)) ∂μ) := by
    funext x
    exact heq _ (sq_nonneg x)
  rwa [hfun]

/-- A concrete positive measure, of density `exp (-u)` on the positive axis. -/
def resolventMeasure : Measure ℝ := (expMeasure 1).restrict (Ioi 0)

instance resolventMeasure_finite : IsFiniteMeasure resolventMeasure := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  unfold resolventMeasure
  infer_instance

lemma resolventMeasure_support : resolventMeasure.restrict (Iic 0) = 0 := by
  unfold resolventMeasure
  rw [Measure.restrict_restrict measurableSet_Iic]
  have hs : Iic (0:ℝ) ∩ Ioi 0 = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false]
    constructor
    · rintro ⟨ha,hb⟩
      linarith
    · intro h
      exact False.elim h
  rw [hs, Measure.restrict_empty]

lemma integral_resolventMeasure (f : ℝ → ℝ) :
    ∫ u, f u ∂resolventMeasure = ∫ u in Ioi (0:ℝ), exp (-u) * f u := by
  unfold resolventMeasure expMeasure gammaMeasure gammaPDF
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    ((measurable_gammaPDFReal 1 1).ennreal_ofReal) (by simp) f measurableSet_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  simp [gammaPDFReal, hu0, ENNReal.toReal_ofReal (exp_nonneg _)]

lemma resolvent_integrability :
    Integrable (fun u : ℝ => min u 1) resolventMeasure := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  have ha : ∀ᵐ u ∂resolventMeasure, 0 < u := by
    exact ae_restrict_mem measurableSet_Ioi
  filter_upwards [ha] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min hu.le zero_le_one)]
  exact min_le_right _ _

/-- The resolvent kernel is a genuine Laplace mixture, with no representation hypothesis. -/
lemma resolvent_representation (t : ℝ) (ht : 0 ≤ t) :
    t / (1+t) = ∫ u, (1-exp (-u*t)) ∂resolventMeasure := by
  rw [integral_resolventMeasure]
  have hp : 0 < 1+t := by linarith
  have he : (fun u : ℝ => exp (-u)*(1-exp (-u*t))) =
      (fun u => exp (-u)-exp (-(1+t)*u)) := by
    funext u
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2
    ring
  rw [he, integral_sub (integrableOn_exp_neg_Ioi 0)
    (integrableOn_exp_mul_Ioi (by linarith : -(1+t)<0) 0),
    integral_exp_neg_Ioi_zero, integral_exp_mul_Ioi (by linarith : -(1+t)<0) 0]
  simp only [mul_zero, exp_zero]
  field_simp
  ring

lemma resolvent_cosine_integral (x : ℝ) :
    ∫ s, cos (x*s) ∂resolventMeasure = 1/(1+x^2) := by
  rw [integral_resolventMeasure]
  have hi := integrableOn_exp_mul_complex_Ioi (a := (⟨-1,x⟩:ℂ)) (by norm_num) 0
  have hc := congrArg Complex.re
    (integral_exp_mul_complex_Ioi (a := (⟨-1,x⟩:ℂ)) (by norm_num) 0)
  change RCLike.re (∫ s in Ioi (0:ℝ), Complex.exp ((⟨-1,x⟩:ℂ) * (s:ℂ))) = _ at hc
  rw [← integral_re hi] at hc
  simpa [Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.normSq_apply, sq] using hc

lemma resolventMeasure_mass : (resolventMeasure Set.univ).toReal = 1 := by
  have h := integral_resolventMeasure (fun _ => (1:ℝ))
  simp only [mul_one, integral_const, smul_eq_mul, mul_one] at h
  rw [integral_exp_neg_Ioi_zero] at h
  exact h

/-- A fully explicit Lévy certificate for the admissible `(a,b,c)=(1,1,1)` case. -/
theorem isLSym_quadratic_resolvent : IsLSym (fun x : ℝ => x^2/(1+x^2)) := by
  refine ⟨{
    A := 0
    A_nonneg := le_rfl
    ν := resolventMeasure
    ν_pos := bot_le
    ν_support := resolventMeasure_support
    ν_integrable := ?_
    apply_eq := ?_ }⟩
  · unfold LevyIntegrable
    calc
      (∫⁻ s, ENNReal.ofReal (min (s^2) 1) ∂resolventMeasure) ≤
          ∫⁻ s, (1:ENNReal) ∂resolventMeasure := lintegral_mono fun s => by
            simp
      _ < ⊤ := by simp
  · intro x
    rw [zero_mul, zero_add]
    have hrestrict : resolventMeasure.restrict (Ioi 0) = resolventMeasure := by
      unfold resolventMeasure
      rw [Measure.restrict_restrict measurableSet_Ioi, inter_self]
    rw [hrestrict]
    have hi : Integrable (fun s : ℝ => cos (x*s)) resolventMeasure := by
      apply (integrable_const (1:ℝ)).mono' (by fun_prop)
      filter_upwards [] with s
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (x*s)
    rw [integral_sub (integrable_const _) hi, integral_const,
      resolvent_cosine_integral, measureReal_def, resolventMeasure_mass, smul_eq_mul, one_mul]
    field_simp
    ring

end Paper02.Bernstein
