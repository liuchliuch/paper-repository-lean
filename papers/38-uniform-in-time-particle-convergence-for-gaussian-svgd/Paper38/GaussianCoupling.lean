import Paper38.Model
import Paper38.Transport
import Paper38.GaussianStatistics
import Mathlib.Tactic

/-!
# Synchronous Gaussian coupling (P38, equation (5.9))

This file evaluates the actual synchronous transport plan. Its cost is computed
from the proved coordinate moments of the finite product Gaussian measure.
The matrices may be arbitrary; symmetric positive definite covariance roots
are therefore included without any additional hypothesis.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Matrix

namespace Paper38.GaussianCoupling
open Paper38.Model Paper38.GaussianStatistics

variable {d : ℕ}

abbrev productLaw (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ : Fin d => gaussianReal 0 1)

def linearForm (c : Fin d → ℝ) (ω : Fin d → ℝ) : ℝ := ∑ i, c i * ω i

lemma linearForm_memLp (c : Fin d → ℝ) :
    MemLp (linearForm c) 2 (productLaw d) := by
  exact memLp_finset_sum _ (fun i _ => (gaussianProduct_coordinate_memLp i).const_mul (c i))

lemma linearForm_integral (c : Fin d → ℝ) :
    ∫ ω, linearForm c ω ∂productLaw d = 0 := by
  unfold linearForm
  rw [integral_finset_sum]
  · simp only [integral_const_mul, gaussianProduct_coordinate_integral, mul_zero,
      Finset.sum_const_zero]
  · intro i _
    exact ((gaussianProduct_coordinate_memLp i).integrable (by norm_num)).const_mul (c i)

lemma coordinate_product_integrable (i j : Fin d) :
    Integrable (fun ω : Fin d → ℝ => ω i * ω j) (productLaw d) :=
  (gaussianProduct_coordinate_memLp i).integrable_mul (gaussianProduct_coordinate_memLp j)

lemma linearForm_product_integral (c e : Fin d → ℝ) :
    ∫ ω, linearForm c ω * linearForm e ω ∂productLaw d = ∑ i, c i * e i := by
  have he (ω : Fin d → ℝ) : linearForm c ω * linearForm e ω =
      ∑ i, ∑ j, (c i * e j) * (ω i * ω j) := by
    unfold linearForm
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    (∫ ω, linearForm c ω * linearForm e ω ∂productLaw d) =
        ∫ ω, ∑ i, ∑ j, (c i * e j) * (ω i * ω j) ∂productLaw d := by
      exact integral_congr_ae (Filter.Eventually.of_forall he)
    _ = ∑ i, ∑ j, ∫ ω, (c i * e j) * (ω i * ω j) ∂productLaw d := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finset_sum]
        intro j _
        exact (coordinate_product_integrable i j).const_mul _
      · intro i _
        exact integrable_finset_sum _ (fun j _ =>
          (coordinate_product_integrable i j).const_mul _)
    _ = ∑ i, ∑ j, (c i * e j) * (if i = j then 1 else 0) := by
      simp only [integral_const_mul, gaussianProduct_coordinate_mul_integral]
    _ = _ := by simp [mul_ite]

lemma linearForm_sq_integral (c : Fin d → ℝ) :
    ∫ ω, linearForm c ω ^ 2 ∂productLaw d = ∑ i, c i ^ 2 := by
  simpa only [pow_two] using linearForm_product_integral c c

lemma affineScalar_memLp (a : ℝ) (c : Fin d → ℝ) :
    MemLp (fun ω => a + linearForm c ω) 2 (productLaw d) :=
  (memLp_const a).add (linearForm_memLp c)

lemma affineScalar_sq_integral (a : ℝ) (c : Fin d → ℝ) :
    ∫ ω, (a + linearForm c ω) ^ 2 ∂productLaw d = a ^ 2 + ∑ i, c i ^ 2 := by
  have hL := linearForm_memLp c
  have hLi := hL.integrable (by norm_num)
  have he (ω : Fin d → ℝ) : (a + linearForm c ω) ^ 2 =
      (a ^ 2 + (2 * a) * linearForm c ω) + linearForm c ω ^ 2 := by ring
  calc
    _ = ∫ ω, (a ^ 2 + (2 * a) * linearForm c ω) + linearForm c ω ^ 2
        ∂productLaw d := integral_congr_ae (Filter.Eventually.of_forall he)
    _ = _ := by
      have hc : Integrable (fun _ : Fin d → ℝ => a ^ 2) (productLaw d) := integrable_const _
      have hl : Integrable (fun ω => (2 * a) * linearForm c ω) (productLaw d) :=
        hLi.const_mul _
      rw [integral_add (f := fun ω => a ^ 2 + (2 * a) * linearForm c ω)
        (g := fun ω => linearForm c ω ^ 2) (hc.add hl) hL.integrable_sq,
        integral_add hc hl, integral_const_mul, linearForm_integral, linearForm_sq_integral]
      simp

lemma continuous_vec : Continuous (vec d) := by
  exact PiLp.continuous_toLp 2 _

lemma continuous_matVec (A : Mat d) : Continuous (matVec A) := by
  unfold matVec vec Matrix.mulVec dotProduct
  fun_prop

/-- The two Gaussian variables are defined on the same product probability space. -/
def affineGaussian (μ : E d) (A : Mat d) (ω : Fin d → ℝ) : E d :=
  μ + matVec A (vec d ω)

lemma continuous_affineGaussian (μ : E d) (A : Mat d) : Continuous (affineGaussian μ A) :=
  continuous_const.add ((continuous_matVec A).comp continuous_vec)

lemma affineGaussian_sub_apply (μ ν : E d) (A B : Mat d) (ω : Fin d → ℝ) (j : Fin d) :
    (affineGaussian μ A ω - affineGaussian ν B ω) j =
      μ j - ν j + linearForm (fun k => A j k - B j k) ω := by
  change (μ j + ∑ k, A j k * ω k) - (ν j + ∑ k, B j k * ω k) =
    μ j - ν j + ∑ k, (A j k - B j k) * ω k
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

lemma affineGaussian_norm_sq (μ ν : E d) (A B : Mat d) (ω : Fin d → ℝ) :
    ‖affineGaussian μ A ω - affineGaussian ν B ω‖ ^ 2 =
      ∑ j, (μ j - ν j + linearForm (fun k => A j k - B j k) ω) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, affineGaussian_sub_apply]

lemma synchronous_cost_integrable (μ ν : E d) (A B : Mat d) :
    Integrable (fun ω => ‖affineGaussian μ A ω - affineGaussian ν B ω‖ ^ 2)
      (productLaw d) := by
  simp_rw [affineGaussian_norm_sq]
  exact integrable_finset_sum _ (fun j _ => (affineScalar_memLp _ _).integrable_sq)

/-- The exact cost of the common-standard-normal coupling. -/
theorem synchronous_cost (μ ν : E d) (A B : Mat d) :
    ∫ ω, ‖affineGaussian μ A ω - affineGaussian ν B ω‖ ^ 2 ∂productLaw d =
      ‖μ - ν‖ ^ 2 + frobSq (A - B) := by
  simp_rw [affineGaussian_norm_sq]
  rw [integral_finset_sum]
  · simp only [affineScalar_sq_integral, Finset.sum_add_distrib, EuclideanSpace.norm_sq_eq,
      Real.norm_eq_abs, sq_abs, PiLp.sub_apply, frobSq, Matrix.sub_apply]
  · intro j _
    exact (affineScalar_memLp _ _).integrable_sq

lemma gaussianLaw_eq_product_map (μ : E d) (A : Mat d) :
    gaussianLaw μ A = (productLaw d).map (affineGaussian μ A) := by
  unfold gaussianLaw standardGaussian
  rw [Measure.map_map]
  · rfl
  · exact (continuous_const.add (continuous_matVec A)).measurable
  · exact continuous_vec.measurable

/-- The source equation (5.9), for the paper's actual Gaussian laws.
The extended-valued transport infimum is bounded by the finite real cost. -/
theorem gaussian_w2sq_le (μ ν : E d) (A B : Mat d) :
    Paper38.Transport.w2sq (gaussianLaw μ A) (gaussianLaw ν B) ≤
      ENNReal.ofReal (‖μ - ν‖ ^ 2 + frobSq (A - B)) := by
  rw [gaussianLaw_eq_product_map, gaussianLaw_eq_product_map]
  refine (Paper38.Transport.w2sq_map_map_le (productLaw d)
    (affineGaussian μ A) (affineGaussian ν B)
    (continuous_affineGaussian μ A).measurable
    (continuous_affineGaussian ν B).measurable).trans_eq ?_
  simp_rw [edist_dist, dist_eq_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  rw [← ofReal_integral_eq_lintegral_ofReal (synchronous_cost_integrable μ ν A B)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)), synchronous_cost]

/-- Injective pushforward preserves the absence of point atoms. -/
lemma noAtoms_map_injective {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (θ : Measure α) [NoAtoms θ]
    (f : α → β) (hf : Measurable f) (hinj : Function.Injective f) :
    NoAtoms (θ.map f) := by
  constructor
  intro y
  rw [Measure.map_apply hf (measurableSet_singleton y)]
  exact (Set.subsingleton_singleton.preimage hinj).measure_zero θ

lemma vec_injective : Function.Injective (vec d) := by
  intro x y h
  exact congrArg WithLp.ofLp h

lemma matVec_injective (A : Mat d) (hA : IsUnit A) : Function.Injective (matVec A) := by
  intro x y h
  have hc : A *ᵥ WithLp.ofLp x = A *ᵥ WithLp.ofLp y := congrArg WithLp.ofLp h
  have he := (Matrix.mulVec_injective_iff_isUnit.mpr hA) hc
  exact congrArg (WithLp.toLp 2) he

lemma standardGaussian_probability (d : ℕ) : IsProbabilityMeasure (standardGaussian d) := by
  unfold standardGaussian
  exact Measure.isProbabilityMeasure_map continuous_vec.measurable.aemeasurable

lemma gaussianLaw_probability (μ : E d) (A : Mat d) : IsProbabilityMeasure (gaussianLaw μ A) := by
  letI := standardGaussian_probability d
  unfold gaussianLaw
  exact Measure.isProbabilityMeasure_map
    (continuous_const.add (continuous_matVec A)).measurable.aemeasurable

/-- In positive dimension the actual standard Gaussian measure is nonatomic. -/
theorem standardGaussian_noAtoms (hd : 0 < d) : NoAtoms (standardGaussian d) := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  letI : NoAtoms (productLaw d) := Measure.pi_noAtoms (μ := fun _ : Fin d => gaussianReal 0 1)
    ⟨0, hd⟩
  unfold standardGaussian
  exact noAtoms_map_injective (productLaw d) (vec d) continuous_vec.measurable vec_injective

/-- Every full-rank affine Gaussian has no point atoms. -/
theorem gaussianLaw_noAtoms (hd : 0 < d) (μ : E d) (A : Mat d) (hA : IsUnit A) :
    NoAtoms (gaussianLaw μ A) := by
  letI := standardGaussian_noAtoms hd
  unfold gaussianLaw
  apply noAtoms_map_injective (standardGaussian d) (fun z => μ + matVec A z)
    (continuous_const.add (continuous_matVec A)).measurable
  intro x y h
  exact matVec_injective A hA (add_left_cancel h)

lemma empiricalLaw_eq_transport_empirical {N : ℕ} (hN : 0 < N) (x : Fin N → E d) :
    empiricalLaw x = Paper38.Transport.empirical x := by
  rw [Paper38.Transport.empirical_eq_sum]
  unfold empiricalLaw
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hN), ENNReal.ofReal_natCast]
  simp only [Fintype.card_fin]

/-- The strict standardized-shape floor for every actual finite empirical cloud. -/
theorem empirical_standardGaussian_w2sq_pos {N : ℕ} (hd : 0 < d) (hN : 0 < N)
    (x : Fin N → E d) :
    0 < Paper38.Transport.w2sq (empiricalLaw x) (standardGaussian d) := by
  letI := standardGaussian_probability d
  letI := standardGaussian_noAtoms hd
  rw [empiricalLaw_eq_transport_empirical hN]
  exact Paper38.Transport.empirical_w2sq_pos x (standardGaussian d)

/-- Fixed finite clouds have strictly positive full-law error against any
full-rank Gaussian, including the limiting optimal Gaussian in Section 6. -/
theorem empirical_gaussian_w2sq_pos {N : ℕ} (hd : 0 < d) (hN : 0 < N)
    (x : Fin N → E d) (μ : E d) (A : Mat d) (hA : IsUnit A) :
    0 < Paper38.Transport.w2sq (empiricalLaw x) (gaussianLaw μ A) := by
  letI := gaussianLaw_probability μ A
  letI := gaussianLaw_noAtoms hd μ A hA
  rw [empiricalLaw_eq_transport_empirical hN]
  exact Paper38.Transport.empirical_w2sq_pos x (gaussianLaw μ A)

open scoped MatrixOrder

/-- The same strict error with the principal covariance root used by the paper. -/
theorem empirical_principal_gaussian_w2sq_pos {N : ℕ} (hd : 0 < d) (hN : 0 < N)
    (x : Fin N → E d) (μ : E d) (S : Mat d) (hS : S.PosDef) :
    0 < Paper38.Transport.w2sq (empiricalLaw x) (gaussianLaw μ (covarianceRoot S)) := by
  exact empirical_gaussian_w2sq_pos hd hN x μ _ hS.posDef_sqrt.isUnit

end Paper38.GaussianCoupling
