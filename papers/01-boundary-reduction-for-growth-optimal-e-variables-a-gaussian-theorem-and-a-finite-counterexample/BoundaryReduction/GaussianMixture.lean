/- Gaussian mixture likelihoods on compact Borel priors, as in (4.7). -/
import BoundaryReduction.FirstExit
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique

open Real Set BigOperators MeasureTheory
open scoped Classical NNReal
namespace BoundaryReduction.Gaussian

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (W : Measure Γ) [IsProbabilityMeasure W]

/-- Exponent of the Gaussian likelihood ratio with precision operator K. -/
noncomputable def exponent (r : Γ) (x : Space d) : ℝ :=
  inner ℝ (r : Space d) (K x) - inner ℝ (r : Space d) (K (r : Space d))/2

lemma continuous_exponent (x : Space d) : Continuous (fun r : Γ => exponent K r x) := by
  unfold exponent
  fun_prop

lemma integrable_exp_shift (x : Space d) (c : ℝ) :
    Integrable (fun r : Γ => exp (exponent K r x-c)) W := by
  have hc : Continuous (fun r : Γ => exp (exponent K r x-c)) :=
    Real.continuous_exp.comp ((continuous_exponent K x).sub continuous_const)
  simpa using hc.continuousOn.integrableOn_compact (μ := W) isCompact_univ

/-- Equation (4.7), with an actual countably additive prior on a compact set. -/
noncomputable def likelihood (x : Space d) : ℝ := ∫ r, exp (exponent K r x) ∂W
noncomputable def phi (x : Space d) : ℝ := log (likelihood K W x)

lemma likelihood_pos (x : Space d) : 0 < likelihood K W x := by
  apply integral_exp_pos
  simpa using integrable_exp_shift K W x 0

lemma integral_exp_sub (x : Space d) (c : ℝ) :
    (∫ r : Γ, exp (exponent K r x-c) ∂W) = likelihood K W x / exp c := by
  simp only [exp_sub, div_eq_mul_inv]
  rw [integral_mul_const]
  rfl

lemma integral_normalized (x : Space d) :
    (∫ r : Γ, exp (exponent K r x-phi K W x) ∂W) = 1 := by
  rw [integral_exp_sub, phi, exp_log (likelihood_pos K W x), div_self (likelihood_pos K W x).ne']

lemma exponent_affine (r : Γ) (x y : Space d) {a b : ℝ} (hab : a+b=1) :
    exponent K r (a • x+b • y) = a*exponent K r x+b*exponent K r y := by
  simp only [exponent, map_add, map_smul, inner_add_right, real_inner_smul_right]
  have h := congrArg (fun t : ℝ => t * (inner ℝ (r : Space d) (K (r : Space d))/2)) hab
  nlinarith

/-- Log mixtures of Gaussian likelihood ratios are convex for arbitrary compact Borel priors. -/
theorem convex_phi : ConvexOn ℝ Set.univ (phi K W) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let c := a*phi K W x+b*phi K W y
  have hpt : ∀ r : Γ,
      exp (exponent K r (a • x+b • y)-c) ≤
        a*exp (exponent K r x-phi K W x)+b*exp (exponent K r y-phi K W y) := by
    intro r
    have h := convexOn_exp.2 (Set.mem_univ (exponent K r x-phi K W x))
      (Set.mem_univ (exponent K r y-phi K W y)) ha hb hab
    simp only [smul_eq_mul] at h
    have heq : exponent K r (a • x+b • y)-c =
        a*(exponent K r x-phi K W x)+b*(exponent K r y-phi K W y) := by
      rw [exponent_affine K r x y hab]
      dsimp [c]
      ring
    rw [heq]
    exact h
  have hi := integral_mono (integrable_exp_shift K W (a • x+b • y) c)
    (((integrable_exp_shift K W x (phi K W x)).const_mul a).add
      ((integrable_exp_shift K W y (phi K W y)).const_mul b)) hpt
  simp only [Pi.add_apply] at hi
  rw [integral_add ((integrable_exp_shift K W x (phi K W x)).const_mul a)
    ((integrable_exp_shift K W y (phi K W y)).const_mul b), integral_const_mul,
    integral_const_mul, integral_normalized, integral_normalized,
    mul_one, mul_one, hab, integral_exp_sub] at hi
  have hL := (div_le_one (exp_pos c)).mp hi
  have hl := log_le_log (likelihood_pos K W (a • x+b • y)) hL
  simpa only [log_exp, phi, smul_eq_mul] using hl

lemma exponent_sub (r : Γ) (x y : Space d) :
    exponent K r x-exponent K r y = inner ℝ (r : Space d) (K (x-y)) := by
  simp [exponent, map_sub, inner_sub_right]

lemma exponent_sub_le (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (r : Γ) (x y : Space d) :
    exponent K r x-exponent K r y ≤ (R:ℝ)*‖K‖*‖x-y‖ := by
  rw [exponent_sub]
  calc
    _ ≤ ‖(r : Space d)‖*‖K (x-y)‖ := real_inner_le_norm _ _
    _ ≤ (R:ℝ)*(‖K‖*‖x-y‖) :=
      mul_le_mul (hR r) (K.le_opNorm (x-y)) (norm_nonneg _) R.coe_nonneg
    _ = _ := by ring

lemma phi_sub_le (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (x y : Space d) : phi K W x-phi K W y ≤ (R:ℝ)*‖K‖*‖x-y‖ := by
  let c := (R:ℝ)*‖K‖*‖x-y‖
  have hpt : ∀ r : Γ, exp (exponent K r x-c) ≤ exp (exponent K r y) := by
    intro r
    apply exp_le_exp.mpr
    have h := exponent_sub_le K R hR r x y
    dsimp [c]
    linarith
  have hi := integral_mono (integrable_exp_shift K W x c)
    (by simpa using integrable_exp_shift K W y 0) hpt
  rw [integral_exp_sub] at hi
  change likelihood K W x / exp c ≤ likelihood K W y at hi
  have hm := (div_le_iff₀ (exp_pos c)).mp hi
  have hl := log_le_log (likelihood_pos K W x) hm
  rw [log_mul (likelihood_pos K W y).ne' (exp_pos c).ne', log_exp] at hl
  change log (likelihood K W x)-log (likelihood K W y) ≤ c
  linarith

/-- The global Lipschitz bound in (4.12), for actual compact Borel mixtures. -/
theorem lipschitz_phi (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) :
    LipschitzWith (R*‖K‖₊) (phi K W) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  apply abs_sub_le_iff.mpr
  constructor
  · exact phi_sub_le K W R hR x y
  · simpa only [norm_sub_rev] using phi_sub_le K W R hR y x

lemma phi_linear_bound (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) (x : Space d) :
    |phi K W x| ≤ |phi K W 0|+(R:ℝ)*‖K‖*‖x‖ := by
  have h := (lipschitz_phi K W R hR).dist_le_mul x 0
  rw [Real.dist_eq, dist_eq_norm, sub_zero] at h
  have ht := abs_add_le (phi K W x-phi K W 0) (phi K W 0)
  have heq : phi K W x-phi K W 0+phi K W 0 = phi K W x := by ring
  rw [heq] at ht
  simpa only [NNReal.coe_mul, coe_nnnorm, add_comm] using (le_trans ht (add_le_add_right h _))

lemma quadratic_abs_le (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) (r : Γ) :
    |inner ℝ (r : Space d) (K (r : Space d))| ≤ (R:ℝ)^2*‖K‖ := by
  have hk := (K.le_opNorm (r : Space d)).trans
    (mul_le_mul_of_nonneg_left (hR r) (norm_nonneg K))
  have hm := mul_le_mul (hR r) hk (norm_nonneg _) R.coe_nonneg
  exact (abs_real_inner_le_norm _ _).trans (by nlinarith)

/-- The explicit likelihood envelope (4.8). -/
theorem likelihood_envelope (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) (x : Space d) :
    exp (-(R:ℝ)*‖K‖*‖x‖-(R:ℝ)^2*‖K‖/2) ≤ likelihood K W x ∧
      likelihood K W x ≤ exp ((R:ℝ)*‖K‖*‖x‖) := by
  have he : ∀ r : Γ,
      -(R:ℝ)*‖K‖*‖x‖-(R:ℝ)^2*‖K‖/2 ≤ exponent K r x ∧
      exponent K r x ≤ (R:ℝ)*‖K‖*‖x‖ := by
    intro r
    have hp := exponent_sub_le K R hR r x 0
    have hn := exponent_sub_le K R hR r 0 x
    have hq := quadratic_abs_le K R hR r
    have hpos := hK (r : Space d)
    simp only [exponent, map_zero, inner_zero_right, zero_sub, sub_zero,
      zero_sub, norm_neg] at hp hn ⊢
    have hqa := abs_le.mp hq
    constructor <;> linarith
  have hint : Integrable (fun r : Γ => exp (exponent K r x)) W := by
    simpa using integrable_exp_shift K W x 0
  constructor
  · have h := integral_mono (integrable_const (exp (-(R:ℝ)*‖K‖*‖x‖-(R:ℝ)^2*‖K‖/2)))
      hint (fun r => exp_le_exp.mpr (he r).1)
    simpa [likelihood] using h
  · have h := integral_mono hint (integrable_const (exp ((R:ℝ)*‖K‖*‖x‖)))
      (fun r => exp_le_exp.mpr (he r).2)
    simpa [likelihood] using h

/-- The explicit linear growth bound for the logarithm in (4.8). -/
theorem phi_envelope (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) (x : Space d) :
    |phi K W x| ≤ (R:ℝ)*‖K‖*‖x‖+(R:ℝ)^2*‖K‖/2 := by
  have he := likelihood_envelope K W R hR hK x
  have hl := log_le_log (exp_pos _) he.1
  have hu := log_le_log (likelihood_pos K W x) he.2
  rw [log_exp] at hl hu
  apply abs_le.mpr
  constructor
  · change -((R:ℝ)*‖K‖*‖x‖+(R:ℝ)^2*‖K‖/2) ≤ log (likelihood K W x)
    linarith
  · change log (likelihood K W x) ≤ _
    have hb : 0 ≤ (R:ℝ)^2*‖K‖/2 := by positivity
    linarith

variable (Z : Measure (Space d)) [ProbabilityTheory.IsGaussian Z]

/-- The Gaussian translation expression (4.13). -/
noncomputable def expectedLog (μ : Space d) : ℝ := ∫ z, phi K W (z+μ) ∂Z

lemma integrable_phi_shift (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (μ : Space d) : Integrable (fun z => phi K W (z+μ)) Z := by
  have hmeas : AEStronglyMeasurable (fun z => phi K W (z+μ)) Z :=
    ((lipschitz_phi K W R hR).continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  have hz : Integrable (fun z : Space d => ‖z‖) Z :=
    ProbabilityTheory.IsGaussian.integrable_fun_id (μ := Z) |>.norm
  have hb : Integrable (fun z : Space d => |phi K W 0|+(R:ℝ)*‖K‖*(‖z‖+‖μ‖)) Z :=
    (integrable_const _).add ((hz.add (integrable_const _)).const_mul _)
  apply hb.mono' hmeas
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs]
  have h := phi_linear_bound K W R hR (z+μ)
  have hnorm := norm_add_le z μ
  have hm := mul_le_mul_of_nonneg_left hnorm
    (mul_nonneg R.coe_nonneg (norm_nonneg K))
  linarith

/-- Gaussian translation preserves convexity of expected log mixture likelihoods. -/
theorem convex_expectedLog (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R) :
    ConvexOn ℝ Set.univ (expectedLog K W Z) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hpt : ∀ z : Space d,
      phi K W (z+(a • x+b • y)) ≤ a*phi K W (z+x)+b*phi K W (z+y) := by
    intro z
    have h := (convex_phi K W).2 (Set.mem_univ (z+x)) (Set.mem_univ (z+y)) ha hb hab
    have heq : a • (z+x)+b • (z+y) = z+(a • x+b • y) := by
      rw [smul_add, smul_add]
      have hh : a • z+b • z = z := by rw [← add_smul, hab, one_smul]
      calc
        a • z+a • x+(b • z+b • y) = (a • z+b • z)+(a • x+b • y) := by abel
        _ = _ := by rw [hh]
    rw [heq] at h
    exact h
  have hi := integral_mono (integrable_phi_shift K W Z R hR (a • x+b • y))
    (((integrable_phi_shift K W Z R hR x).const_mul a).add
      ((integrable_phi_shift K W Z R hR y).const_mul b)) hpt
  simp only [Pi.add_apply] at hi
  rw [integral_add ((integrable_phi_shift K W Z R hR x).const_mul a)
    ((integrable_phi_shift K W Z R hR y).const_mul b), integral_const_mul,
    integral_const_mul] at hi
  exact hi

end BoundaryReduction.Gaussian
