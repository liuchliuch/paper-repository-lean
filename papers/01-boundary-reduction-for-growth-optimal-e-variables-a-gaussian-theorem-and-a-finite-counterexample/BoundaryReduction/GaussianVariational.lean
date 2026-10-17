import BoundaryReduction.GaussianCrossEntropy

open Real Set MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]

noncomputable def componentChi (W : ProbabilityMeasure Γ) (r : Γ) (x : Space d) : ℝ :=
  (exp (exponent K r x)-likelihood K (W : Measure Γ) x)^2 / likelihood K (W : Measure Γ) x

noncomputable def componentChiIntegral (W : ProbabilityMeasure Γ) (r : Γ) : ℝ :=
  ∫ x, componentChi K W r x ∂Z

lemma componentChi_bound (W : ProbabilityMeasure Γ) (r : Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) (x : Space d) :
    componentChi K W r x ≤
      4*exp ((R:ℝ)^2*‖K‖/2)*exp ((3*(R:ℝ)*‖K‖)*‖x‖) := by
  let A := (R:ℝ)*‖K‖
  let b := (R:ℝ)^2*‖K‖/2
  let v := likelihood K (W : Measure Γ) x
  let p := exp (exponent K r x)
  have hv : 0 < v := likelihood_pos K (W : Measure Γ) x
  have hp : 0 < p := exp_pos _
  have hvu : v ≤ exp (A*‖x‖) := (likelihood_envelope K (W : Measure Γ) R hR hK x).2
  have hvl : exp (-A*‖x‖-b) ≤ v := by
    simpa only [A, b, v, neg_mul, mul_assoc] using
      (likelihood_envelope K (W : Measure Γ) R hR hK x).1
  have hpu : p ≤ exp (A*‖x‖) := by
    simpa only [likelihood_point] using (likelihood_envelope K (pointPrior r : Measure Γ) R hR hK x).2
  have hab : |p-v| ≤ 2*exp (A*‖x‖) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hsq : (p-v)^2 ≤ 4*(exp (A*‖x‖))^2 := by
    nlinarith [sq_abs (p-v), abs_nonneg (p-v), exp_pos (A*‖x‖)]
  change (p-v)^2/v ≤ _
  calc
    _ ≤ 4*(exp (A*‖x‖))^2/v := div_le_div_of_nonneg_right hsq hv.le
    _ ≤ 4*(exp (A*‖x‖))^2/exp (-A*‖x‖-b) :=
      div_le_div_of_nonneg_left (by positivity) (exp_pos _) hvl
    _ = _ := by
      rw [show 3*(R:ℝ)*‖K‖*‖x‖ = 3*A*‖x‖ by dsimp [A]; ring]
      change 4*(exp (A*‖x‖))^2/exp (-A*‖x‖-b) = 4*exp b*exp (3*A*‖x‖)
      rw [show -A*‖x‖-b = -(A*‖x‖+b) by ring, exp_neg, div_inv_eq_mul,
        exp_add, show 3*A*‖x‖ = A*‖x‖+(A*‖x‖+A*‖x‖) by ring, exp_add, exp_add]
      ring

lemma integrable_componentChi (W : ProbabilityMeasure Γ) (r : Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) : Integrable (componentChi K W r) Z := by
  have hb := (gaussian_integrable_exp_norm Z (3*(R:ℝ)*‖K‖)).const_mul
    (4*exp ((R:ℝ)^2*‖K‖/2))
  have hc : Continuous (componentChi K W r) := by
    apply Continuous.div
    · apply Continuous.pow
      apply Continuous.sub
      · exact Real.continuous_exp.comp (by unfold exponent; fun_prop)
      · exact continuous_likelihood K (W : Measure Γ) R hR
    · exact continuous_likelihood K (W : Measure Γ) R hR
    · intro x
      exact (likelihood_pos K (W : Measure Γ) x).ne'
  apply hb.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    unfold componentChi
    exact div_nonneg (sq_nonneg _) (likelihood_pos K (W : Measure Γ) x).le)]
  exact componentChi_bound K W r R hR hK x

lemma componentChiIntegral_nonneg (W : ProbabilityMeasure Γ) (r : Γ) :
    0 ≤ componentChiIntegral K Z W r := by
  apply integral_nonneg
  intro x
  exact div_nonneg (sq_nonneg _) (likelihood_pos K (W : Measure Γ) x).le

noncomputable def componentScore (W : ProbabilityMeasure Γ) (r : Γ) (x : Space d) : ℝ :=
  (exp (exponent K r x)-likelihood K (W : Measure Γ) x)*(1+phi K (W : Measure Γ) x)

variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d),
  covariance L (precisionForm K v) Z = L v)
include hcenter hcov

lemma integrable_componentScore (W : ProbabilityMeasure Γ) (r : Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) : Integrable (componentScore K W r) Z := by
  have hvar := precision_variance_of_covariance K Z hcenter hcov
  have hp := integrable_component K Z hcenter hvar r
  have hv := integrable_likelihood K Z hcenter hvar (W : Measure Γ)
  have hc := integrable_cross K Z (pointPrior r) W R hR hK
  simp only [likelihood_point] at hc
  have he := integrable_entropy K Z (W : Measure Γ) R hR hK
  apply ((hp.sub hv).add (hc.sub he)).congr
  apply Filter.Eventually.of_forall
  intro x
  unfold componentScore
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

lemma integral_componentScore (W : ProbabilityMeasure Γ) (r : Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    (∫ x, componentScore K W r x ∂Z) =
      expectedLog K (W : Measure Γ) Z (r : Space d)-mixtureEntropy K Z W := by
  have hvar := precision_variance_of_covariance K Z hcenter hcov
  have hp := integrable_component K Z hcenter hvar r
  have hv := integrable_likelihood K Z hcenter hvar (W : Measure Γ)
  have hc := integrable_cross K Z (pointPrior r) W R hR hK
  simp only [likelihood_point] at hc
  have he := integrable_entropy K Z (W : Measure Γ) R hR hK
  have hfun : componentScore K W r = fun x =>
      (exp (exponent K r x)-likelihood K (W : Measure Γ) x)+
        (exp (exponent K r x)*phi K (W : Measure Γ) x-
          likelihood K (W : Measure Γ) x*phi K (W : Measure Γ) x) := by
    ext x
    unfold componentScore
    ring
  rw [hfun]
  have hadd := integral_add (hp.sub hv) (hc.sub he)
  have hsub1 := integral_sub hp hv
  have hsub2 := integral_sub hc he
  simp only [Pi.add_apply, Pi.sub_apply] at hadd hsub1 hsub2
  rw [hadd, hsub1, hsub2, integral_component K Z hcenter hvar r,
    integral_likelihood K Z hcenter hvar (W : Measure Γ)]
  rw [← expectedLog_component_identity K Z hcenter hcov (W : Measure Γ) R hR r]
  simp only [sub_self, zero_add, mixtureEntropy]

lemma entropy_perturbation_upper (W : ProbabilityMeasure Γ) (r : Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) :
    mixtureEntropy K Z (priorMix (pointPrior r) W a ha) ≤ mixtureEntropy K Z W+
      a*(expectedLog K (W : Measure Γ) Z (r : Space d)-mixtureEntropy K Z W)+
      a^2*componentChiIntegral K Z W r := by
  let U := priorMix (pointPrior r) W a ha
  have hpt : ∀ x : Space d,
      likelihood K (U : Measure Γ) x*phi K (U : Measure Γ) x-
        likelihood K (W : Measure Γ) x*phi K (W : Measure Γ) x ≤
        a*componentScore K W r x+a^2*componentChi K W r x := by
    intro x
    have hu : likelihood K (U : Measure Γ) x-likelihood K (W : Measure Γ) x =
        a*(exp (exponent K r x)-likelihood K (W : Measure Γ) x) := by
      dsimp [U]
      rw [likelihood_mix, likelihood_point]
      ring
    have h := entropy_remainder_upper (likelihood_pos K (U : Measure Γ) x)
      (likelihood_pos K (W : Measure Γ) x)
    rw [hu] at h
    calc
      _ ≤ (a*(exp (exponent K r x)-likelihood K (W : Measure Γ) x))*
          (1+phi K (W : Measure Γ) x)+
          (a*(exp (exponent K r x)-likelihood K (W : Measure Γ) x))^2 /
            likelihood K (W : Measure Γ) x := by
        dsimp [phi]
        linarith
      _ = _ := by unfold componentScore componentChi; ring
  have hEU := integrable_entropy K Z (U : Measure Γ) R hR hK
  have hEW := integrable_entropy K Z (W : Measure Γ) R hR hK
  have hS := integrable_componentScore K Z hcenter hcov W r R hR hK
  have hC := integrable_componentChi K Z W r R hR hK
  have hi := integral_mono (hEU.sub hEW) ((hS.const_mul a).add (hC.const_mul (a^2))) hpt
  simp only [Pi.sub_apply, Pi.add_apply] at hi
  have hs := integral_sub hEU hEW
  have ht := integral_add (hS.const_mul a) (hC.const_mul (a^2))
  simp only [Pi.sub_apply, Pi.add_apply] at hs ht
  rw [hs, ht, integral_const_mul, integral_const_mul,
    integral_componentScore K Z hcenter hcov W r R hR hK] at hi
  change mixtureEntropy K Z U-mixtureEntropy K Z W ≤
    a*(expectedLog K (W : Measure Γ) Z (r : Space d)-mixtureEntropy K Z W)+
      a^2*componentChiIntegral K Z W r at hi
  dsimp [U] at hi
  linarith

omit hcenter hcov in
lemma nonneg_of_quadratic_perturbation {C q : ℝ} (hC : 0 ≤ C)
    (h : ∀ a ∈ Icc (0:ℝ) 1, 0 ≤ a*q+a^2*C) : 0 ≤ q := by
  by_contra! hq
  let a := min (1/2 : ℝ) (-q/(2*(C+1)))
  have hden : 0 < 2*(C+1) := by linarith
  have ha : 0 < a := lt_min (by norm_num) (div_pos (by linarith) hden)
  have ha1 : a ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hab : a*(2*(C+1)) ≤ -q := (le_div_iff₀ hden).mp (min_le_right _ _)
  have hneg : q+a*C < 0 := by nlinarith
  have hprod := mul_neg_of_pos_of_neg ha hneg
  have hzero := h a ⟨ha.le,ha1⟩
  nlinarith

/-- Necessity in Proposition 4.2, proved by an actual quadratic perturbation. -/
theorem boundary_condition_of_minimizer (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hmin : ∀ V : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z V) :
    ∀ r : Γ, mixtureEntropy K Z W ≤ expectedLog K (W : Measure Γ) Z (r : Space d) := by
  intro r
  have hq : 0 ≤ expectedLog K (W : Measure Γ) Z (r : Space d)-mixtureEntropy K Z W := by
    apply nonneg_of_quadratic_perturbation (componentChiIntegral_nonneg K Z W r)
    intro a ha
    have hu := entropy_perturbation_upper K Z hcenter hcov W r R hR hK a ha
    have hl := hmin (priorMix (pointPrior r) W a ha)
    linarith
  linarith

/-- Proposition 4.2, exact Borel boundary optimality criterion. -/
theorem proposition_4_2_iff (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    (∀ V : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z V) ↔
    (∀ r : Γ, mixtureEntropy K Z W ≤ expectedLog K (W : Measure Γ) Z (r : Space d)) := by
  exact ⟨boundary_condition_of_minimizer K Z hcenter hcov W R hR hK,
    minimizer_of_boundary_condition K Z hcenter hcov W R hR hK⟩

end BoundaryReduction.Gaussian
