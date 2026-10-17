import Paper26.GraphPrior
import Paper26.WeakPosteriorIdentity
import Paper26.NumericPriorArithmetic
import Paper26.GaussianRootCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The explicit numerical local prior in Section 3

The three inputs below are generic Gaussian mass/moment, Gaussian rectangular
matrix-tail, and compact Lipschitz weak-H1 facts. Their fields quantify over
all dimensions, variances and functions; none contains a cutoff prior,
normalizer, Fisher bound, loss or tomography conclusion. The variance is that
of each real coordinate, hence of each real and imaginary matrix entry.
The actual cutoff, weak root, probability normalization and 65536 bound are
constructed locally. This root need not be smooth at the cutoff corners.
-/
noncomputable section
open scoped BigOperators ENNReal NNReal ComplexOrder Matrix
open MeasureTheory Set Metric

namespace Paper26.NumericGraphPrior
open H1PosteriorBound WeakPosteriorIdentity

abbrev Space (p : ℕ) := ParameterSpace p

def gaussianRoot (p : ℕ) (v : ℝ) (x : Space p) : ℝ :=
  (2 * Real.pi * v) ^ (-(p : ℝ) / 4) * Real.exp (-‖x‖ ^ 2 / (4 * v))

def gaussianMeasure (p : ℕ) (v : ℝ) : Measure (Space p) :=
  volume.withDensity (fun x => ENNReal.ofReal (gaussianRoot p v x ^ 2))

/-- Standard isotropic real Gaussian normalization and second moment.
Vershynin, High-Dimensional Probability (first edition), Section 3.3.2,
Equation (3.4), with scaling by sqrt(v); p=0 is the one-point convention.
Primary source: https://webapps.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf . -/
structure GaussianMassMomentInput : Prop where
  mass : ∀ (p : ℕ) (v : ℝ), 0 < v →
    Integrable (fun x : Space p => gaussianRoot p v x ^ 2) volume ∧
      (∫ x : Space p, gaussianRoot p v x ^ 2) = 1
  moment : ∀ (p : ℕ) (v : ℝ), 0 < v →
    Integrable (fun x : Space p => ‖x‖ ^ 2 * gaussianRoot p v x ^ 2) volume ∧
      (∫ x : Space p, ‖x‖ ^ 2 * gaussianRoot p v x ^ 2) = (p : ℝ) * v

/-- Generic complex Gaussian matrix tail from two quarter-nets and the
scalar radial Gaussian tail. All real coordinates have variance v.
The precise generic corollary uses Vershynin Corollary 4.2.13 for the
complex spheres viewed as real spheres, and the complex Gaussian Cartesian
and radial density in Mezzadri (2007), Section 3, Equations (3.1)--(3.3):
https://arxiv.org/pdf/math-ph/0609050v2 . It contains no chosen cutoff. -/
structure GaussianMatrixTailInput : Prop where
  tail : ∀ (r s : ℕ), 0 < r → 0 < s → ∀ (v u : ℝ), 0 < v → 0 < u →
    gaussianMeasure (2 * r * s) v
      {x | u < ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖} ≤
        ENNReal.ofReal ((9 : ℝ) ^ (2 * (r + s)) * Real.exp (-u ^ 2 / (8 * v)))

/-- Compact Lipschitz functions belong to weak H1, with the a.e. classical
Fréchet derivative as representative. This is a generic Rademacher/weak-
derivative theorem; no derivative-energy or prior conclusion is a field.
Hajlasz, Sobolev spaces and calculus of variations, Theorems 2.23 and 2.42
(ACL/weak derivatives and Rademacher). The a.e. derivative representative
can be chosen to equal the total classical fderiv at every point. -/
structure CompactLipschitzH1Input : Prop where
  root : ∀ (p : ℕ) (f : Space p → ℝ) (L : ℝ≥0), LipschitzWith L f →
    HasCompactSupport f → ∃ h : WeakH1Root p,
      (∀ x, h.root x = f x) ∧ (∀ x, h.weakDerivative x = fderiv ℝ f x)

lemma gaussianRoot_nonneg (p : ℕ) (v : ℝ) (hv : 0 < v) (x : Space p) :
    0 ≤ gaussianRoot p v x := by
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

lemma gaussianRoot_smooth (p : ℕ) (v : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gaussianRoot p v) := by
  unfold gaussianRoot
  exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const _).exp)

lemma gaussianMeasure_probability (G : GaussianMassMomentInput) (p : ℕ) (v : ℝ) (hv : 0 < v) :
    IsProbabilityMeasure (gaussianMeasure p v) := by
  constructor
  rw [gaussianMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (G.mass p v hv).1 (ae_of_all _ fun x => sq_nonneg _),
    (G.mass p v hv).2, ENNReal.ofReal_one]

lemma operator_apply_sq_le (r s : ℕ) (X : Matrix (Fin s) (Fin r) ℂ)
    (v : EuclideanSpace ℂ (Fin r)) :
    ‖ChartVolume.operator X v‖ ^ 2 ≤ ShellAccounting.frobeniusSq X * ‖v‖ ^ 2 := by
  calc
    _ ≤ ∑ i : Fin s, (∑ j : Fin r, ‖X i j‖ ^ 2) * ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_le_sum
      intro i _
      change ‖∑ j, X i j * v j‖ ^ 2 ≤ _
      have hs := norm_sum_le (s := Finset.univ) (f := fun j => X i j * v j)
      simp only [norm_mul] at hs
      have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j => ‖X i j‖) (fun j => ‖v j‖)
      have hv : (∑ j : Fin r, ‖v j‖ ^ 2) = ‖v‖ ^ 2 := (EuclideanSpace.norm_sq_eq v).symm
      rw [hv] at hc
      exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ =>
        mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr hs).trans hc
    _ = _ := by simp [ShellAccounting.frobeniusSq, Finset.sum_mul]

lemma operator_norm_le_coordinates (r s : ℕ) (X : Matrix (Fin s) (Fin r) ℂ) :
    ‖ChartVolume.operator X‖ ≤ ‖MatrixCoordinates.coordinates r s X‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, ← MatrixCoordinates.frobeniusSq_eq_norm_sq]
  exact operator_apply_sq_le r s X v

lemma operator_sub (r s : ℕ) (X Y : Matrix (Fin s) (Fin r) ℂ) :
    ChartVolume.operator (X - Y) = ChartVolume.operator X - ChartVolume.operator Y := by
  ext v i
  simp [ChartVolume.operator_apply, Matrix.sub_mulVec]

lemma operatorNorm_lipschitz (r s : ℕ) :
    LipschitzWith 1 (fun x : Space (2 * r * s) =>
      ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  calc
    _ ≤ ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x) -
        ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm y)‖ := by simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le _ _
    _ = ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm (x-y))‖ := by
      rw [map_sub, operator_sub]
    _ ≤ ‖x-y‖ := by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        operator_norm_le_coordinates r s ((MatrixCoordinates.coordinates r s).symm (x-y))

/-- The exact piecewise-linear cutoff from the source, at radius a. -/
def cutoff (r s : ℕ) (a : ℝ) (x : Space (2 * r * s)) : ℝ :=
  max 0 (min 1 (2 - (2 / a) *
    ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖))

lemma cutoff_nonneg (r s : ℕ) (a : ℝ) (x : Space (2 * r * s)) :
    0 ≤ cutoff r s a x := le_max_left _ _

lemma cutoff_le_one (r s : ℕ) (a : ℝ) (x : Space (2 * r * s)) :
    cutoff r s a x ≤ 1 := max_le (by norm_num) (min_le_left _ _)

lemma cutoff_eq_one (r s : ℕ) {a : ℝ} (ha : 0 < a) (x : Space (2 * r * s))
    (hx : ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖ ≤ a/2) :
    cutoff r s a x = 1 := by
  unfold cutoff
  have h : (2/a) * ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖ ≤ 1 := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ ha).mpr (by linarith)
  rw [min_eq_left (by linarith : 1 ≤ 2 - (2/a) *
    ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖)]
  norm_num

lemma cutoff_eq_zero (r s : ℕ) {a : ℝ} (ha : 0 < a) (x : Space (2 * r * s))
    (hx : a ≤ ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖) :
    cutoff r s a x = 0 := by
  unfold cutoff
  apply max_eq_left
  apply (min_le_right _ _).trans
  have h : 2 ≤ (2/a) * ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖ := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ ha).mpr (by linarith)
  linarith

lemma cutoff_lipschitz (r s : ℕ) {a : ℝ} (ha : 0 < a) :
    LipschitzWith ⟨2/a, by positivity⟩ (cutoff r s a) := by
  have h : LipschitzWith ⟨2/a, by positivity⟩ (fun x : Space (2*r*s) =>
      2 - (2/a) * ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm, NNReal.coe_mk]
    have he (u v : ℝ) : (2-(2/a)*u)-(2-(2/a)*v) = -(2/a)*(u-v) := by ring
    rw [he, norm_mul, norm_neg, Real.norm_eq_abs (2/a), abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [NNReal.coe_one, one_mul] using (operatorNorm_lipschitz r s).norm_sub_le x y
  exact (h.const_min 1).const_max 0

lemma operator_entry_le (r s : ℕ) (X : Matrix (Fin s) (Fin r) ℂ) (i : Fin s) (j : Fin r) :
    ‖X i j‖ ≤ ‖ChartVolume.operator X‖ := by
  let e : EuclideanSpace ℂ (Fin r) := EuclideanSpace.single j 1
  have he : (ChartVolume.operator X e) i = X i j := by
    change (X *ᵥ Pi.single j 1) i = X i j
    simp only [Matrix.mulVec_single_one, Matrix.col_apply]
  calc
    _ = ‖(ChartVolume.operator X e) i‖ := by rw [he]
    _ ≤ ‖ChartVolume.operator X e‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖ChartVolume.operator X‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
    _ = _ := by simp [e]

lemma coordinate_norm_sq_le (r s : ℕ) (x : Space (2*r*s)) :
    ‖x‖ ^ 2 ≤ (r : ℝ)*s *
      ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖ ^ 2 := by
  rw [← MatrixCoordinates.frobeniusSq_symm_eq_norm_sq]
  unfold ShellAccounting.frobeniusSq
  calc
    _ ≤ ∑ _i : Fin s, ∑ _j : Fin r,
        ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (operator_entry_le _ _ _ i j)
    _ = _ := by simp; ring

lemma cutoff_compact (r s : ℕ) {a : ℝ} (ha : 0 < a) : HasCompactSupport (cutoff r s a) := by
  let R : ℝ := (r : ℝ)*s*a^2+1
  change IsCompact (tsupport (cutoff r s a))
  apply (isCompact_closedBall (0 : Space (2*r*s)) R).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hn : ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖ < a := by
    by_contra h
    exact hx (cutoff_eq_zero r s ha x (le_of_not_gt h))
  have hb := coordinate_norm_sq_le r s x
  have hsq := (sq_le_sq₀ (norm_nonneg _) ha.le).mpr hn.le
  have hm := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (r : ℝ)*s)
  simp only [mem_closedBall, dist_zero_right]
  dsimp [R]
  nlinarith [sq_nonneg (‖x‖-1), norm_nonneg x]

lemma gaussian_derivative_integrable (G : GaussianMassMomentInput) (p : ℕ) {v : ℝ} (hv : 0 < v) :
    Integrable (fun x : Space p => ‖fderiv ℝ (gaussianRoot p v) x‖ ^ 2) volume :=
  GaussianRootCalculus.integrable_energy volume _ v hv (G.moment p v hv).1

lemma gaussian_derivative_energy (G : GaussianMassMomentInput) (p : ℕ) {v : ℝ} (hv : 0 < v) :
    (∫ x : Space p, ‖fderiv ℝ (gaussianRoot p v) x‖ ^ 2) = (p : ℝ)/(4*v) :=
  GaussianRootCalculus.integral_energy volume _ v p hv (G.moment p v hv).2

/-- The actual unnormalized cutoff-root probability mass. -/
def normalizer (r s : ℕ) (a v : ℝ) : ℝ :=
  ∫ x : Space (2*r*s), cutoff r s a x ^ 2 * gaussianRoot (2*r*s) v x ^ 2

lemma normalizer_integrable (G : GaussianMassMomentInput) (r s : ℕ)
    {a v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    Integrable (fun x : Space (2*r*s) => cutoff r s a x ^ 2 * gaussianRoot (2*r*s) v x ^ 2) volume := by
  apply (G.mass (2*r*s) v hv).1.mono'
    (((cutoff_lipschitz r s ha).continuous.pow 2).mul
      ((gaussianRoot_smooth _ _).continuous.pow 2)).aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hc : cutoff r s a x ^ 2 ≤ 1 := by
    nlinarith [cutoff_nonneg r s a x, cutoff_le_one r s a x]
  exact mul_le_of_le_one_left (sq_nonneg _) hc

lemma normalizer_le_one (G : GaussianMassMomentInput) (r s : ℕ)
    {a v : ℝ} (ha : 0 < a) (hv : 0 < v) : normalizer r s a v ≤ 1 := by
  rw [← (G.mass (2*r*s) v hv).2]
  apply integral_mono (normalizer_integrable G r s ha hv) (G.mass _ _ hv).1
  intro x
  exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith [cutoff_nonneg r s a x, cutoff_le_one r s a x])

lemma normalizer_nonneg (r s : ℕ) (a v : ℝ) : 0 ≤ normalizer r s a v := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

lemma cutoffMean_eq_normalizer (G : GaussianMassMomentInput) (r s : ℕ)
    {a v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    (∫⁻ x, ENNReal.ofReal (cutoff r s a x ^ 2) ∂gaussianMeasure (2*r*s) v) =
      ENNReal.ofReal (normalizer r s a v) := by
  rw [gaussianMeasure, lintegral_withDensity_eq_lintegral_mul₀
    (((gaussianRoot_smooth _ _).continuous.measurable.pow_const 2).ennreal_ofReal.aemeasurable)
    (((cutoff_lipschitz r s ha).continuous.measurable.pow_const 2).ennreal_ofReal.aemeasurable)]
  rw [normalizer, ofReal_integral_eq_lintegral_ofReal (normalizer_integrable G r s ha hv)
    (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal (gaussianRoot (2*r*s) v x ^ 2) * ENNReal.ofReal (cutoff r s a x ^ 2) =
    ENNReal.ofReal (cutoff r s a x ^ 2 * gaussianRoot (2*r*s) v x ^ 2)
  rw [ENNReal.ofReal_mul (sq_nonneg _)]
  exact mul_comm _ _

/-- A cutoff equal to one on the inner operator ball retains its actual
Gaussian probability mass. No normalization bound is an input. -/
lemma normalizer_lower_of_tail (G : GaussianMassMomentInput) (r s : ℕ)
    {a v b : ℝ} (ha : 0 < a) (hv : 0 < v) (hb : 0 ≤ b)
    (htail : gaussianMeasure (2*r*s) v
      {x | a/2 < ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖} ≤
        ENNReal.ofReal b) :
    1-b ≤ normalizer r s a v := by
  let μ := gaussianMeasure (2*r*s) v
  letI : IsProbabilityMeasure μ := gaussianMeasure_probability G _ _ hv
  let S : Set (Space (2*r*s)) :=
    {x | ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖ ≤ a/2}
  have hS : MeasurableSet S := measurableSet_le (operatorNorm_lipschitz r s).continuous.measurable measurable_const
  have hcomp : Sᶜ = {x | a/2 < ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖} := by
    ext x
    simp only [S, mem_compl_iff, mem_setOf_eq, not_le]
  have hmean : μ S ≤ ENNReal.ofReal (normalizer r s a v) := by
    rw [← cutoffMean_eq_normalizer G r s ha hv]
    have he : (∫⁻ x, S.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) = μ S := by
      rw [lintegral_indicator hS]
      simp
    rw [← he]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      change 1 ≤ ENNReal.ofReal (cutoff r s a x ^ 2)
      rw [cutoff_eq_one r s ha x hx]
      norm_num
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (normalizer r s a v + b) := by
    calc
      _ = μ S + μ Sᶜ := by simpa only [measure_univ] using (measure_add_measure_compl (μ := μ) hS).symm
      _ ≤ ENNReal.ofReal (normalizer r s a v) + ENNReal.ofReal b := by
        apply add_le_add hmean
        simpa only [hcomp] using htail
      _ = _ := (ENNReal.ofReal_add (normalizer_nonneg r s a v) hb).symm
  have hreal : 1 ≤ normalizer r s a v + b := by
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (normalizer_nonneg r s a v) hb)).mp
      (by simpa only [ENNReal.ofReal_one] using hone)
  linarith

lemma numeric_normalizer_ge_half (G : GaussianMassMomentInput) (T : GaussianMatrixTailInput)
    {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) :
    1/2 ≤ normalizer r s (1/2) (NumericPriorArithmetic.variance s) := by
  have hs : 0 < s := hr.trans_le hrs
  have hv := NumericPriorArithmetic.variance_pos hs
  have ht := T.tail r s hr hs (NumericPriorArithmetic.variance s) ((1/2)/2) hv (by norm_num)
  have hnet := NumericPriorArithmetic.net_tail_lt_half hr hrs
  have htail : gaussianMeasure (2*r*s) (NumericPriorArithmetic.variance s)
      {x | (1/2:ℝ)/2 < ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖} ≤
        ENNReal.ofReal (1/2 : ℝ) :=
    ht.trans (ENNReal.ofReal_le_ofReal (by convert hnet.le using 1; norm_num))
  have h := normalizer_lower_of_tail G r s (by norm_num : (0:ℝ)<1/2) hv (by norm_num) htail
  linarith

lemma cutoff_half_lipschitz (r s : ℕ) : LipschitzWith 4 (cutoff r s (1/2)) := by
  have h := cutoff_lipschitz r s (by norm_num : (0:ℝ)<1/2)
  have he : (⟨2/(1/2:ℝ), by norm_num⟩ : ℝ≥0) = 4 := by ext; norm_num
  rwa [he] at h

/-- Actual compact weak cutoff root, from the generic Lipschitz H1 theorem. -/
def cutoffRoot (C : CompactLipschitzH1Input) (r s : ℕ) : WeakH1Root (2*r*s) :=
  Classical.choose (C.root (2*r*s) (cutoff r s (1/2)) 4
    (cutoff_half_lipschitz r s) (cutoff_compact r s (by norm_num)))

lemma cutoffRoot_spec (C : CompactLipschitzH1Input) (r s : ℕ) :
    (∀ x, (cutoffRoot C r s).root x = cutoff r s (1/2) x) ∧
      (∀ x, (cutoffRoot C r s).weakDerivative x = fderiv ℝ (cutoff r s (1/2)) x) :=
  Classical.choose_spec (C.root (2*r*s) (cutoff r s (1/2)) 4
    (cutoff_half_lipschitz r s) (cutoff_compact r s (by norm_num)))

lemma gaussianRoot_locallyLipschitz (p : ℕ) (v : ℝ) : LocallyLipschitz (gaussianRoot p v) := by
  have h : ContDiff ℝ 1 (gaussianRoot p v) := by
    unfold gaussianRoot
    exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const _).exp)
  exact h.locallyLipschitz

def unnormalizedRoot (C : CompactLipschitzH1Input) (r s : ℕ) (v : ℝ)
    (P : WeakLocallyLipschitzProductInput (2*r*s)) : WeakH1Root (2*r*s) :=
  weakProductRoot P (cutoffRoot C r s) (gaussianRoot (2*r*s) v)

lemma unnormalizedRoot_value (C : CompactLipschitzH1Input) (r s : ℕ) (v : ℝ)
    (P : WeakLocallyLipschitzProductInput (2*r*s)) (x : Space (2*r*s)) :
    (unnormalizedRoot C r s v P).root x = cutoff r s (1/2) x * gaussianRoot (2*r*s) v x := by
  rw [unnormalizedRoot, weakProductRoot_root _ _ _ (gaussianRoot_locallyLipschitz _ _),
    (cutoffRoot_spec C r s).1]

lemma unnormalizedRoot_derivative (C : CompactLipschitzH1Input) (r s : ℕ) (v : ℝ)
    (P : WeakLocallyLipschitzProductInput (2*r*s)) (x : Space (2*r*s)) :
    (unnormalizedRoot C r s v P).weakDerivative x =
      gaussianRoot (2*r*s) v x • fderiv ℝ (cutoff r s (1/2)) x +
        cutoff r s (1/2) x • fderiv ℝ (gaussianRoot (2*r*s) v) x := by
  rw [unnormalizedRoot, weakProductRoot_derivative _ _ _ (gaussianRoot_locallyLipschitz _ _)]
  simp only [weakProductDerivative, (cutoffRoot_spec C r s).1, (cutoffRoot_spec C r s).2]

lemma unnormalizedRoot_derivative_bound (C : CompactLipschitzH1Input) (r s : ℕ)
    {v : ℝ} (hv : 0 < v) (P : WeakLocallyLipschitzProductInput (2*r*s))
    (x : Space (2*r*s)) :
    ‖(unnormalizedRoot C r s v P).weakDerivative x‖ ^ 2 ≤
      2 * (16 * gaussianRoot (2*r*s) v x ^ 2 + ‖fderiv ℝ (gaussianRoot (2*r*s) v) x‖ ^ 2) := by
  have hD : ‖fderiv ℝ (cutoff r s (1/2)) x‖ ≤ 4 := by
    exact norm_fderiv_le_of_lipschitz ℝ (cutoff_half_lipschitz r s)
  have hg := gaussianRoot_nonneg (2*r*s) v hv x
  have hc0 := cutoff_nonneg r s (1/2) x
  have hc1 := cutoff_le_one r s (1/2) x
  have hsum : ‖(unnormalizedRoot C r s v P).weakDerivative x‖ ≤
      4 * gaussianRoot (2*r*s) v x + ‖fderiv ℝ (gaussianRoot (2*r*s) v) x‖ := by
    rw [unnormalizedRoot_derivative]
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hg, abs_of_nonneg hc0]
    have h₁ := mul_le_mul_of_nonneg_left hD hg
    have h₂ := mul_le_of_le_one_left (norm_nonneg (fderiv ℝ (gaussianRoot (2*r*s) v) x)) hc1
    nlinarith
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (by positivity) (norm_nonneg _))).mpr hsum
  nlinarith [sq_nonneg (4 * gaussianRoot (2*r*s) v x - ‖fderiv ℝ (gaussianRoot (2*r*s) v) x‖)]

lemma unnormalizedRoot_energy (G : GaussianMassMomentInput) (C : CompactLipschitzH1Input)
    (r s : ℕ) {v : ℝ} (hv : 0 < v) (P : WeakLocallyLipschitzProductInput (2*r*s)) :
    (∫ x, ‖(unnormalizedRoot C r s v P).weakDerivative x‖ ^ 2) ≤
      2 * (((2*r*s : ℕ) : ℝ)/(4*v) + 16) := by
  have hi : Integrable (fun x => ‖(unnormalizedRoot C r s v P).weakDerivative x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (unnormalizedRoot C r s v P).derivative_aestronglyMeasurable).mp
      (unnormalizedRoot C r s v P).weakDerivative_memLp
  have h₁ := ((G.mass (2*r*s) v hv).1.const_mul 16).add (gaussian_derivative_integrable G _ hv)
  have hh := integral_mono hi (h₁.const_mul 2) (unnormalizedRoot_derivative_bound C r s hv P)
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul, integral_add ((G.mass _ _ hv).1.const_mul 16)
    (gaussian_derivative_integrable G _ hv), integral_const_mul,
    (G.mass _ _ hv).2, gaussian_derivative_energy G _ hv] at hh
  simpa only [mul_one, add_comm] using hh

/-- The actual normalized, compactly supported weak-H1 prior root. -/
def normalizedRoot (C : CompactLipschitzH1Input) (r s : ℕ) (v : ℝ)
    (P : WeakLocallyLipschitzProductInput (2*r*s)) : WeakH1Root (2*r*s) :=
  scaleRoot (Real.sqrt (normalizer r s (1/2) v))⁻¹ (unnormalizedRoot C r s v P)

lemma normalizedRoot_nonneg (C : CompactLipschitzH1Input) (r s : ℕ) {v : ℝ} (hv : 0 < v)
    (P : WeakLocallyLipschitzProductInput (2*r*s)) (x : Space (2*r*s)) :
    0 ≤ (normalizedRoot C r s v P).root x := by
  rw [normalizedRoot, scaleRoot_root, unnormalizedRoot_value]
  exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
    (mul_nonneg (cutoff_nonneg r s (1/2) x) (gaussianRoot_nonneg _ _ hv x))

lemma normalizedRoot_mass (C : CompactLipschitzH1Input) (r s : ℕ) (v : ℝ)
    (P : WeakLocallyLipschitzProductInput (2*r*s)) (hZ : 0 < normalizer r s (1/2) v) :
    (normalizedRoot C r s v P).mass univ = 1 := by
  have hb : (unnormalizedRoot C r s v P).mass univ = ENNReal.ofReal (normalizer r s (1/2) v) := by
    rw [GraphPrior.weak_mass_univ_eq_ofReal_integral]
    simp_rw [unnormalizedRoot_value, mul_pow]
    rfl
  rw [normalizedRoot, mass_scaleRoot, hb, ← ENNReal.ofReal_mul (sq_nonneg _),
    inv_pow, Real.sq_sqrt hZ.le, inv_mul_cancel₀ hZ.ne', ENNReal.ofReal_one]

lemma normalizedRoot_fisher (G : GaussianMassMomentInput) (C : CompactLipschitzH1Input)
    (r s : ℕ) {v : ℝ} (hv : 0 < v) (P : WeakLocallyLipschitzProductInput (2*r*s))
    (hZ : 0 < normalizer r s (1/2) v) :
    (normalizedRoot C r s v P).fisher ≤ ENNReal.ofReal
      ((8 / normalizer r s (1/2) v) * (((2*r*s : ℕ) : ℝ)/(4*v) + 16)) := by
  rw [GraphPrior.weak_fisher_eq_ofReal_integral]
  have he (x : Space (2*r*s)) :
      ‖(normalizedRoot C r s v P).weakDerivative x‖ ^ 2 =
        (normalizer r s (1/2) v)⁻¹ * ‖(unnormalizedRoot C r s v P).weakDerivative x‖ ^ 2 := by
    simp only [normalizedRoot, scaleRoot_derivative, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, inv_pow, Real.sq_sqrt hZ.le]
  simp_rw [he]
  rw [integral_const_mul]
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left (unnormalizedRoot_energy G C r s hv P)
    (by positivity : 0 ≤ 4 * (normalizer r s (1/2) v)⁻¹)
  convert h using 1 <;> simp only [div_eq_mul_inv] <;> ring

lemma normalizedRoot_zero (C : CompactLipschitzH1Input) (r s : ℕ) (v : ℝ)
    (P : WeakLocallyLipschitzProductInput (2*r*s)) (x : Space (2*r*s))
    (hx : 1/2 ≤ ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖) :
    (normalizedRoot C r s v P).root x = 0 := by
  rw [normalizedRoot, scaleRoot_root, unnormalizedRoot_value,
    cutoff_eq_zero r s (by norm_num) x hx, zero_mul, mul_zero]

/-- The source's closed operator-norm half-chart, on the genuine coordinates. -/
lemma normalizedRoot_support (C : CompactLipschitzH1Input) (r s : ℕ) (v : ℝ)
    (P : WeakLocallyLipschitzProductInput (2*r*s)) :
    tsupport (normalizedRoot C r s v P).root ⊆
      {x | ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖ ≤ 1/2} := by
  apply closure_minimal _ (isClosed_le (operatorNorm_lipschitz r s).continuous continuous_const)
  intro x hx
  by_contra hn
  exact hx (normalizedRoot_zero C r s v P x (le_of_lt (lt_of_not_ge hn)))

/-- The explicit source-scale choice of variance, for every matrix dimension. -/
def numericRoot (C : CompactLipschitzH1Input) (r s : ℕ)
    (P : WeakLocallyLipschitzProductInput (2*r*s)) : WeakH1Root (2*r*s) :=
  normalizedRoot C r s (NumericPriorArithmetic.variance s) P

/-- The actual probability measure is given by the squared constructed root. -/
def priorMeasure (h : WeakH1Root p) : Measure (Space p) :=
  volume.withDensity (fun x => ENNReal.ofReal (h.root x ^ 2))

lemma priorMeasure_probability (h : WeakH1Root p) (hm : h.mass univ = 1) :
    IsProbabilityMeasure (priorMeasure h) := by
  constructor
  rw [priorMeasure, withDensity_apply _ MeasurableSet.univ]
  exact hm

/-- The explicit 65536 example after source Equation (26). The actual root
is nonnegative, normalized, weak H1, compactly supported in the closed
operator-norm half-chart, and its actual Fisher information has the displayed
numerical bound. No prior or information-bound input is used. -/
theorem lemma_3_4_numeric (G : GaussianMassMomentInput) (T : GaussianMatrixTailInput)
    (C : CompactLipschitzH1Input) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (P : WeakLocallyLipschitzProductInput (2*r*s)) :
    (∀ x, 0 ≤ (numericRoot C r s P).root x) ∧
      (numericRoot C r s P).mass univ = 1 ∧
      HasCompactSupport (numericRoot C r s P).root ∧
      tsupport (numericRoot C r s P).root ⊆
        {x | ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖ ≤ 1/2} ∧
      (numericRoot C r s P).fisher ≤ ENNReal.ofReal (65536*(r : ℝ)*(s : ℝ)^2) ∧
      IsProbabilityMeasure (priorMeasure (numericRoot C r s P)) := by
  have hs : 0 < s := hr.trans_le hrs
  have hv := NumericPriorArithmetic.variance_pos hs
  have hZ := numeric_normalizer_ge_half G T hr hrs
  have hZp : 0 < normalizer r s (1/2) (NumericPriorArithmetic.variance s) := by linarith
  have hm := normalizedRoot_mass C r s (NumericPriorArithmetic.variance s) P hZp
  refine ⟨normalizedRoot_nonneg C r s hv P, hm,
    (numericRoot C r s P).compact_support, normalizedRoot_support C r s _ P, ?_,
    priorMeasure_probability _ hm⟩
  exact (normalizedRoot_fisher G C r s hv P hZp).trans
    (ENNReal.ofReal_le_ofReal (NumericPriorArithmetic.normalized_information_bound hr hrs hZ))

/-- Explicit existential version, on the same genuine matrix coordinates
and weak H1 definition used by the posterior argument. -/
theorem exists_numeric_prior (G : GaussianMassMomentInput) (T : GaussianMatrixTailInput)
    (C : CompactLipschitzH1Input) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (P : WeakLocallyLipschitzProductInput (2*r*s)) :
    ∃ h : WeakH1Root (2*r*s), (∀ x, 0 ≤ h.root x) ∧ h.mass univ = 1 ∧
      tsupport h.root ⊆
        {x | ‖ChartVolume.operator ((MatrixCoordinates.coordinates r s).symm x)‖ ≤ 1/2} ∧
      h.fisher ≤ ENNReal.ofReal (65536*(r : ℝ)*(s : ℝ)^2) ∧ IsProbabilityMeasure (priorMeasure h) := by
  obtain ⟨hn, hm, _, hs, hI, hp⟩ := lemma_3_4_numeric G T C hr hrs P
  exact ⟨numericRoot C r s P, hn, hm, hs, hI, hp⟩

/-- Real-integral spelling of the same actual numerical Fisher bound. -/
theorem numeric_fisher_real_bound (G : GaussianMassMomentInput) (T : GaussianMatrixTailInput)
    (C : CompactLipschitzH1Input) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (P : WeakLocallyLipschitzProductInput (2*r*s)) :
    4 * (∫ x, ‖(numericRoot C r s P).weakDerivative x‖ ^ 2) ≤
      65536*(r : ℝ)*(s : ℝ)^2 := by
  have h := (lemma_3_4_numeric G T C hr hrs P).2.2.2.2.1
  rw [GraphPrior.weak_fisher_eq_ofReal_integral] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

end Paper26.NumericGraphPrior
