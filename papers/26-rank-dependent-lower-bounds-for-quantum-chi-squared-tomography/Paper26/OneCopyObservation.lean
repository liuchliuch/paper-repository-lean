import Paper26.PureCovariant
import Paper26.CollectiveSubmatrix
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Actual covariant observations for the one-copy submatrix estimator

The external Haar input contains only first and second coordinate moments of
actual rank-one projectors. These are the n=1 and n=2 instances of Harrow 2013,
Proposition 6, with P_sym=(I+swap)/2 at n=2. Neither weighted observations nor
any P26 expectation, variance, or concentration conclusion is an input.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory
namespace Paper26.OneCopyObservation
open QuantumModel HaarFrames

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev PureFrame (ι : Type*) [Fintype ι] := Frame ι (Fin 1)

def projector (U : PureFrame ι) : Matrix ι ι ℂ := U.projector.matrix

omit [Nonempty ι] in
lemma projector_eq_density (U : PureFrame ι) : projector U = U.density.matrix := by
  simp only [projector, Frame.density_matrix, Fintype.card_fin, Nat.cast_one,
    inv_one, one_smul, Frame.projector_matrix]

/-- Exact standard Haar coordinate moments, with no R, likelihood or Y in the
interface. The ambient dimension is the actual finite index cardinality. -/
structure HaarCoordinateMoments (μ : Measure (PureFrame ι)) : Prop where
  first : ∀ i j, (∫ U, projector U i j ∂μ) =
    (1 : Matrix ι ι ℂ) i j / (Fintype.card ι : ℂ)
  second : ∀ a b i j, (∫ U, projector U a b * projector U i j ∂μ) =
    ((1 : Matrix ι ι ℂ) a b * (1 : Matrix ι ι ℂ) i j +
      (1 : Matrix ι ι ℂ) a j * (1 : Matrix ι ι ℂ) i b) /
        ((Fintype.card ι : ℂ) * (Fintype.card ι + 1))

lemma measurable_projector_entry (i j : ι) :
    Measurable (fun U : PureFrame ι => projector U i j) := by
  simp_rw [projector_eq_density]
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp Frame.measurable_density_matrix)

lemma projector_entry_bound (U : PureFrame ι) (i j : ι) : ‖projector U i j‖ ≤ 1 := by
  rw [projector_eq_density]
  exact PureCovariant.density_entry_norm_le_one U.density i j

lemma projector_entry_integrable (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ] (i j : ι) :
    Integrable (fun U => projector U i j) μ := by
  apply Integrable.of_bound (measurable_projector_entry i j).aestronglyMeasurable 1
  exact ae_of_all _ fun U => projector_entry_bound U i j

lemma projector_product_integrable (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (a b i j : ι) : Integrable (fun U => projector U a b * projector U i j) μ := by
  apply Integrable.of_bound ((measurable_projector_entry a b).mul
    (measurable_projector_entry i j)).aestronglyMeasurable 1
  apply ae_of_all
  intro U
  rw [norm_mul]
  exact mul_le_one₀ (projector_entry_bound U a b) (norm_nonneg _) (projector_entry_bound U i j)

/-- Unconditional success likelihood on a full copy. -/
def likelihood (R : Matrix ι ι ℂ) (U : PureFrame ι) : ℝ :=
  Fintype.card ι * (Matrix.trace (projector U * R)).re

omit [Nonempty ι] in
lemma likelihood_complex (R : Matrix ι ι ℂ) (hR : R.IsHermitian) (U : PureFrame ι) :
    ((likelihood R U : ℝ) : ℂ) = (Fintype.card ι : ℂ) * Matrix.trace (projector U * R) := by
  unfold likelihood
  have hp : (projector U)ᴴ = projector U := U.projector.hermitian.eq
  rw [Complex.ofReal_mul, EnergyReality.trace_hermitian_product_real (projector U) R hp hR.eq]
  norm_cast

omit [Nonempty ι] in
lemma likelihood_nonneg (R : Matrix ι ι ℂ) (hR : R.PosSemidef) (U : PureFrame ι) :
    0 ≤ likelihood R U := by
  apply mul_nonneg (Nat.cast_nonneg _)
  exact TailConvexity.pairing_nonneg_psd (projector U) R U.projector.positive hR

omit [Nonempty ι] in
lemma likelihood_le (R : Matrix ι ι ℂ) (hR : R.PosSemidef) (U : PureFrame ι) :
    likelihood R U ≤ Fintype.card ι * (Matrix.trace R).re := by
  have ht := TailConvexity.pairing_nonneg_psd R (PureMinimax.complement U.projector).matrix
    hR (PureMinimax.complement U.projector).positive
  change 0 ≤ (Matrix.trace (R * (1 - projector U))).re at ht
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_mul_comm R (projector U),
    Complex.sub_re] at ht
  unfold likelihood
  exact mul_le_mul_of_nonneg_left (sub_nonneg.mp ht) (Nat.cast_nonneg _)

lemma measurable_likelihood (R : Matrix ι ι ℂ) : Measurable (likelihood R) := by
  unfold likelihood
  apply Measurable.const_mul
  apply Measurable.re (𝕜 := ℂ)
  change Measurable (fun U : PureFrame ι => ∑ i, ∑ j, projector U i j * R j i)
  apply Finset.measurable_sum Finset.univ
  intro i _
  apply Finset.measurable_sum Finset.univ
  intro j _
  exact (measurable_projector_entry i j).mul_const _

lemma likelihood_integrable (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (R : Matrix ι ι ℂ) (hR : R.PosSemidef) : Integrable (likelihood R) μ := by
  apply Integrable.of_bound (measurable_likelihood R).aestronglyMeasurable
    (Fintype.card ι * (Matrix.trace R).re)
  apply ae_of_all
  intro U
  rw [Real.norm_eq_abs, abs_of_nonneg (likelihood_nonneg R hR U)]
  exact likelihood_le R hR U

lemma weighted_projector_integrable (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (R : Matrix ι ι ℂ) (hR : R.PosSemidef) (i j : ι) :
    Integrable (fun U => ((likelihood R U : ℝ) : ℂ) * projector U i j) μ := by
  apply Integrable.of_bound (((measurable_likelihood R).complex_ofReal).mul
    (measurable_projector_entry i j)).aestronglyMeasurable
      (Fintype.card ι * (Matrix.trace R).re)
  apply ae_of_all
  intro U
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (likelihood_nonneg R hR U)]
  exact (mul_le_of_le_one_right (likelihood_nonneg R hR U) (projector_entry_bound U i j)).trans
    (likelihood_le R hR U)

omit [Nonempty ι] in
lemma contraction_first (R : Matrix ι ι ℂ) :
    (∑ a, ∑ b, R b a * (1 : Matrix ι ι ℂ) a b) = Matrix.trace R := by
  simp [Matrix.one_apply, Matrix.trace, Matrix.diag]

omit [Nonempty ι] in
lemma contraction_second (R : Matrix ι ι ℂ) (i j : ι) :
    (∑ a, ∑ b, R b a * ((1 : Matrix ι ι ℂ) a b * (1 : Matrix ι ι ℂ) i j +
      (1 : Matrix ι ι ℂ) a j * (1 : Matrix ι ι ℂ) i b)) =
        Matrix.trace R * (1 : Matrix ι ι ℂ) i j + R i j := by
  simp [Matrix.one_apply, Matrix.trace, Matrix.diag, mul_add, Finset.sum_add_distrib]

/-- The raw first coordinate moment proves that success has precisely the
actual block mass, before a failure atom is added. -/
theorem integral_likelihood (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef) :
    ∫ U, likelihood R U ∂μ = (Matrix.trace R).re := by
  have hc : (∫ U, ((likelihood R U : ℝ) : ℂ) ∂μ) = Matrix.trace R := by
    simp_rw [likelihood_complex R hR.1, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [integral_const_mul]
    rw [integral_finset_sum Finset.univ (fun a _ =>
      integrable_finset_sum Finset.univ (fun b _ => (projector_entry_integrable μ a b).mul_const (R b a)))]
    simp_rw [integral_finset_sum Finset.univ (fun b _ =>
      (projector_entry_integrable μ _ b).mul_const (R b _)), integral_mul_const, H.first]
    have hk : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hf : (∑ a, ∑ b, (1 : Matrix ι ι ℂ) a b / (Fintype.card ι : ℂ) * R b a) =
        (∑ a, ∑ b, R b a * (1 : Matrix ι ι ℂ) a b) / (Fintype.card ι : ℂ) := by
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    change (Fintype.card ι : ℂ) * _ = Matrix.trace R
    rw [hf, contraction_first]
    field_simp
  have hi : Integrable (fun U => ((likelihood R U : ℝ) : ℂ)) μ :=
    (likelihood_integrable μ R hR).ofReal
  calc
    (∫ U, likelihood R U ∂μ) = (∫ U, ((likelihood R U : ℝ) : ℂ) ∂μ).re := by
      simpa only [RCLike.re_eq_complex_re, Complex.ofReal_re] using
        integral_re hi
    _ = _ := congrArg Complex.re hc

/-- Contracting the raw second Haar coordinate moment with the actual block
matrix gives the weighted projector moment used in Eq. (42). -/
theorem integral_weighted_projector (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef) (i j : ι) :
    (∫ U, ((likelihood R U : ℝ) : ℂ) * projector U i j ∂μ) =
      (Matrix.trace R * (1 : Matrix ι ι ℂ) i j + R i j) / (Fintype.card ι + 1) := by
  have he : (fun U : PureFrame ι => ((likelihood R U : ℝ) : ℂ) * projector U i j) =
      fun U => (Fintype.card ι : ℂ) *
        ∑ a, ∑ b, R b a * (projector U a b * projector U i j) := by
    funext U
    rw [likelihood_complex R hR.1]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [he, integral_const_mul]
  rw [integral_finset_sum Finset.univ (fun a _ => integrable_finset_sum Finset.univ
    (fun b _ => (projector_product_integrable μ a b i j).const_mul (R b a)))]
  simp_rw [integral_finset_sum Finset.univ (fun b _ =>
    (projector_product_integrable μ _ b i j).const_mul (R b _)), integral_const_mul, H.second]
  have hf : (∑ a, ∑ b, R b a *
      (((1 : Matrix ι ι ℂ) a b * (1 : Matrix ι ι ℂ) i j +
        (1 : Matrix ι ι ℂ) a j * (1 : Matrix ι ι ℂ) i b) /
          ((Fintype.card ι : ℂ) * (Fintype.card ι + 1)))) =
      (∑ a, ∑ b, R b a * ((1 : Matrix ι ι ℂ) a b * (1 : Matrix ι ι ℂ) i j +
        (1 : Matrix ι ι ℂ) a j * (1 : Matrix ι ι ℂ) i b)) /
          ((Fintype.card ι : ℂ) * (Fintype.card ι + 1)) := by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hf, contraction_second]
  have hk : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hk1 : (Fintype.card ι : ℂ) + 1 ≠ 0 := by
    have h : (0 : ℝ) < Fintype.card ι + 1 := by positivity
    exact_mod_cast ne_of_gt h
  field_simp


abbrev Outcome (ι : Type*) [Fintype ι] := PureFrame ι ⊕ Unit

def successMeasure (μ : Measure (PureFrame ι)) (R : Matrix ι ι ℂ) : Measure (PureFrame ι) :=
  μ.withDensity (fun U => ENNReal.ofReal (likelihood R U))

/-- The failed block projection is retained as a separate actual atom. -/
def outcomeMeasure (μ : Measure (PureFrame ι)) (R : Matrix ι ι ℂ) : Measure (Outcome ι) :=
  Measure.map Sum.inl (successMeasure μ R) +
    ENNReal.ofReal (1 - (Matrix.trace R).re) • Measure.dirac (Sum.inr ())

theorem successMeasure_univ (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef) :
    successMeasure μ R Set.univ = ENNReal.ofReal (Matrix.trace R).re := by
  rw [successMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (likelihood_integrable μ R hR)
      (ae_of_all _ (likelihood_nonneg R hR)), integral_likelihood μ H R hR]

/-- Normalization includes projection failure, hence one sample consumes one
full copy independently of whether the block projection succeeds. -/
theorem outcomeMeasure_univ (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) : outcomeMeasure μ R Set.univ = 1 := by
  rw [outcomeMeasure, Measure.add_apply, Measure.map_apply measurable_inl MeasurableSet.univ]
  simp only [Set.preimage_univ, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [successMeasure_univ μ H R hR, ← ENNReal.ofReal_add]
  · norm_num
  · exact (hR.trace_nonneg).1
  · exact sub_nonneg.mpr hw

/-- An affine actual matrix observation, zero on the failed projection. -/
def affineObservation (a b : ℂ) : Outcome ι → Matrix ι ι ℂ
  | Sum.inl U => a • projector U + b • (1 : Matrix ι ι ℂ)
  | Sum.inr _ => 0

lemma measurable_affine_entry (a b : ℂ) (i j : ι) :
    Measurable (fun z : Outcome ι => affineObservation a b z i j) := by
  apply measurable_fun_sum
  · change Measurable (fun U : PureFrame ι => a * projector U i j + b * (1 : Matrix ι ι ℂ) i j)
    exact ((measurable_projector_entry i j).const_mul a).add measurable_const
  · exact measurable_const

lemma affine_entry_bound (a b : ℂ) (z : Outcome ι) (i j : ι) :
    ‖affineObservation a b z i j‖ ≤ ‖a‖ + ‖b‖ := by
  rcases z with U | u
  · change ‖a * projector U i j + b * (1 : Matrix ι ι ℂ) i j‖ ≤ _
    have hi : ‖(1 : Matrix ι ι ℂ) i j‖ ≤ 1 := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    calc
      _ ≤ ‖a * projector U i j‖ + ‖b * (1 : Matrix ι ι ℂ) i j‖ := norm_add_le _ _
      _ ≤ ‖a‖ + ‖b‖ := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_of_le_one_right (norm_nonneg _) (projector_entry_bound U i j))
          (mul_le_of_le_one_right (norm_nonneg _) hi)
  · change ‖(0 : ℂ)‖ ≤ _
    simpa only [norm_zero] using add_nonneg (norm_nonneg a) (norm_nonneg b)

lemma affine_entry_integrable (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (a b : ℂ) (i j : ι) :
    Integrable (fun z => affineObservation a b z i j) (outcomeMeasure μ R) := by
  letI : IsProbabilityMeasure (outcomeMeasure μ R) := ⟨outcomeMeasure_univ μ H R hR hw⟩
  apply Integrable.of_bound (measurable_affine_entry a b i j).aestronglyMeasurable (‖a‖ + ‖b‖)
  exact ae_of_all _ fun z => affine_entry_bound a b z i j

/-- A generic affine projector test is integrated against the actual success
measure plus failed-projection atom. This is derived from raw Haar moments. -/
theorem integral_affine_entry (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (a b : ℂ) (i j : ι) :
    (∫ z, affineObservation a b z i j ∂outcomeMeasure μ R) =
      a * ((Matrix.trace R * (1 : Matrix ι ι ℂ) i j + R i j) / (Fintype.card ι + 1)) +
        b * Matrix.trace R * (1 : Matrix ι ι ℂ) i j := by
  have hi := affine_entry_integrable μ H R hR hw a b i j
  rw [outcomeMeasure, integrable_add_measure] at hi
  rw [outcomeMeasure, integral_add_measure hi.1 hi.2,
    integral_map measurable_inl.aemeasurable (measurable_affine_entry a b i j).aestronglyMeasurable,
    integral_smul_measure]
  rw [integral_dirac' _ _ (measurable_affine_entry a b i j).stronglyMeasurable]
  simp only [affineObservation, Matrix.zero_apply, smul_zero, add_zero]
  rw [successMeasure, integral_withDensity_eq_integral_toReal_smul
    ((measurable_likelihood R).ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (likelihood_nonneg R hR _), Complex.real_smul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have he : (fun U : PureFrame ι => (likelihood R U : ℂ) *
      (a * projector U i j + b * (1 : Matrix ι ι ℂ) i j)) =
      fun U => a * ((likelihood R U : ℂ) * projector U i j) +
        (b * (1 : Matrix ι ι ℂ) i j) * (likelihood R U : ℂ) := by
    funext U
    ring
  have hC : Integrable (fun U : PureFrame ι => ((likelihood R U : ℝ) : ℂ)) μ :=
    (likelihood_integrable μ R hR).ofReal
  have hA : Integrable (fun U : PureFrame ι => a * ((likelihood R U : ℂ) * projector U i j)) μ :=
    (weighted_projector_integrable μ R hR i j).const_mul a
  have hB : Integrable (fun U : PureFrame ι =>
      (b * (1 : Matrix ι ι ℂ) i j) * (likelihood R U : ℂ)) μ := hC.const_mul _
  rw [he]
  rw [integral_add hA hB, integral_const_mul, integral_const_mul,
    integral_weighted_projector μ H R hR]
  have hc : (∫ U, ((likelihood R U : ℝ) : ℂ) ∂μ) = Matrix.trace R := by
    rw [integral_complex_ofReal (f := likelihood R) (μ := μ), integral_likelihood μ H R hR]
    have he := EnergyReality.trace_hermitian_product_real R (1 : Matrix ι ι ℂ) hR.1.eq (by simp)
    simpa only [Matrix.mul_one] using he
  rw [hc]
  ring

/-- Eq. (41), with zero recorded on every failed projection. -/
def observation : Outcome ι → Matrix ι ι ℂ :=
  affineObservation (Fintype.card ι + 1) (-1)

omit [Nonempty ι] in
lemma observation_hermitian (z : Outcome ι) : (observation z).IsHermitian := by
  rcases z with U | u
  · have hp : (projector U)ᴴ = projector U := U.projector.hermitian.eq
    change (((Fintype.card ι : ℂ) + 1) • projector U + (-1 : ℂ) • (1 : Matrix ι ι ℂ))ᴴ =
      ((Fintype.card ι : ℂ) + 1) • projector U + (-1 : ℂ) • (1 : Matrix ι ι ℂ)
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hp]
  · exact Matrix.isHermitian_zero

omit [Nonempty ι] in
lemma observation_square (z : Outcome ι) :
    observation z * observation z = affineObservation ((Fintype.card ι : ℂ) ^ 2 - 1) 1 z := by
  rcases z with U | u
  · have hP : projector U * projector U = projector U := U.projector.idempotent
    change (((Fintype.card ι : ℂ) + 1) • projector U + (-1 : ℂ) • 1) *
      (((Fintype.card ι : ℂ) + 1) • projector U + (-1 : ℂ) • 1) =
        ((Fintype.card ι : ℂ) ^ 2 - 1) • projector U + (1 : ℂ) • (1 : Matrix ι ι ℂ)
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      hP, Matrix.mul_one, Matrix.one_mul]
    module
  · simp [observation, affineObservation]

/-- First actual unconditional observation moment in Eq. (42). -/
theorem observation_mean (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (i j : ι) :
    (∫ z, observation z i j ∂outcomeMeasure μ R) = R i j := by
  rw [observation, integral_affine_entry μ H R hR hw]
  have hk : (Fintype.card ι : ℂ) + 1 ≠ 0 := by
    have h : (0 : ℝ) < Fintype.card ι + 1 := by positivity
    exact_mod_cast ne_of_gt h
  field_simp
  ring

/-- Second actual unconditional matrix observation moment in Eq. (42). -/
theorem observation_second_moment (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (i j : ι) :
    (∫ z, (observation z * observation z) i j ∂outcomeMeasure μ R) =
      (Fintype.card ι : ℂ) * Matrix.trace R * (1 : Matrix ι ι ℂ) i j +
        (Fintype.card ι - 1 : ℂ) * R i j := by
  simp_rw [observation_square]
  rw [integral_affine_entry μ H R hR hw]
  have hk : (Fintype.card ι : ℂ) + 1 ≠ 0 := by
    have h : (0 : ℝ) < Fintype.card ι + 1 := by positivity
    exact_mod_cast ne_of_gt h
  field_simp
  ring

/-- The norm is explicitly the operator norm on complex Euclidean space. -/
def operatorNorm (A : Matrix ι ι ℂ) : ℝ := ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A‖

open scoped MatrixOrder Matrix.Norms.L2Operator

local instance : CStarAlgebra (Matrix ι ι ℂ) where

omit [Nonempty ι] in
lemma psd_mass_complement (R : Matrix ι ι ℂ) (hR : R.PosSemidef) :
    (((Matrix.trace R).re : ℂ) • (1 : Matrix ι ι ℂ) - R).PosSemidef := by
  let U := hR.1.eigenvectorUnitary
  let a := hR.1.eigenvalues
  have he : R = Normalization.conjugate (U : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix a) := by
    simpa only [U, a, Normalization.conjugate, Normalization.diagonalMatrix,
      Function.comp_def, Matrix.star_eq_conjTranspose] using hR.1.spectral_theorem
  have ht : (Matrix.trace R).re = ∑ i, a i := by
    have h := congrArg Complex.re hR.1.trace_eq_sum_eigenvalues
    simpa only [a, Complex.re_sum, RCLike.ofReal_re] using h
  have ha : ∀ i, a i ≤ (Matrix.trace R).re := by
    intro i
    rw [ht]
    exact Finset.single_le_sum (fun j _ => hR.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hd : (Normalization.diagonalMatrix (fun i => (Matrix.trace R).re - a i)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ (((Matrix.trace R).re - a i : ℝ) : ℂ)
    exact_mod_cast sub_nonneg.mpr (ha i)
  have hdEq : Normalization.diagonalMatrix (fun i => (Matrix.trace R).re - a i) =
      ((Matrix.trace R).re : ℂ) • (1 : Matrix ι ι ℂ) - Normalization.diagonalMatrix a := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Normalization.diagonalMatrix]
    · simp [Normalization.diagonalMatrix, Matrix.diagonal, hij]
  have hi : Normalization.conjugate (U : Matrix ι ι ℂ) 1 = 1 := by
    simpa only [Normalization.conjugate, Matrix.mul_one] using PositiveLossBridge.unitary_right U
  have hp := hd.mul_mul_conjTranspose_same (U : Matrix ι ι ℂ)
  change (Normalization.conjugate (U : Matrix ι ι ℂ) _).PosSemidef at hp
  rw [hdEq, Normalization.conjugate_sub, Normalization.conjugate_smul, hi, ← he] at hp
  exact hp

omit [Nonempty ι] in
lemma operatorNorm_le_of_psd (A : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (c : ℝ) (hc : 0 ≤ c) (hbound : ((c : ℂ) • (1 : Matrix ι ι ℂ) - A).PosSemidef) :
    operatorNorm A ≤ c := by
  change ‖A‖ ≤ c
  have hA' : (0 : Matrix ι ι ℂ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hbound' : A ≤ algebraMap ℝ (Matrix ι ι ℂ) c := by
    change (algebraMap ℝ (Matrix ι ι ℂ) c - A).PosSemidef
    simpa only [Algebra.algebraMap_eq_smul_one, Complex.real_smul] using hbound
  exact (CStarAlgebra.norm_le_iff_le_algebraMap A hc hA').mpr hbound' 

lemma operatorNorm_psd_le_mass (R : Matrix ι ι ℂ) (hR : R.PosSemidef) :
    operatorNorm R ≤ (Matrix.trace R).re :=
  operatorNorm_le_of_psd R hR _ (hR.trace_nonneg).1 (psd_mass_complement R hR)

/-- The observed matrix has eigenvalue k on the sampled line and −1 on its
orthogonal complement; its actual operator norm is at most k. -/
theorem observation_operatorNorm (z : Outcome ι) : operatorNorm (observation z) ≤ Fintype.card ι := by
  rcases z with U | u
  · have hk : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
    have hc : 0 ≤ (Fintype.card ι : ℝ) ^ 2 - 1 := by nlinarith
    have hp := (PureMinimax.complement U.projector).positive.smul (α := ℂ)
      (show (0 : ℂ) ≤ (((Fintype.card ι : ℝ) ^ 2 - 1 : ℝ) : ℂ) by exact_mod_cast hc)
    have he : (((Fintype.card ι : ℝ) ^ 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) -
        observation (Sum.inl U) * observation (Sum.inl U) =
      ((((Fintype.card ι : ℝ) ^ 2 - 1 : ℝ) : ℂ)) • (PureMinimax.complement U.projector).matrix := by
      rw [observation_square]
      change _ - (((Fintype.card ι : ℂ) ^ 2 - 1) • projector U + (1 : ℂ) • 1) =
        _ • (1 - projector U)
      push_cast
      module
    have hs : (observation (Sum.inl U) * observation (Sum.inl U)).PosSemidef := by
      simpa only [(observation_hermitian (Sum.inl U)).eq] using
        Matrix.posSemidef_conjTranspose_mul_self (observation (Sum.inl U))
    have hb := operatorNorm_le_of_psd _ hs ((Fintype.card ι : ℝ)^2) (sq_nonneg _) (he.symm ▸ hp)
    change ‖observation (Sum.inl U) * observation (Sum.inl U)‖ ≤ _ at hb
    have hn := Matrix.l2_opNorm_conjTranspose_mul_self (observation (Sum.inl U))
    rw [(observation_hermitian (Sum.inl U)).eq] at hn
    rw [hn] at hb
    change ‖observation (Sum.inl U)‖ ≤ _
    nlinarith [norm_nonneg (observation (Sum.inl U))]
  · simp [operatorNorm, observation, affineObservation]

/-- The deterministic centered bound used by matrix Bernstein, proved for the
actual success and failure outcomes. -/
theorem centered_operatorNorm (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (z : Outcome ι) :
    operatorNorm (observation z - R) ≤ 2 * Fintype.card ι := by
  have hk : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  calc
    operatorNorm (observation z - R) ≤ operatorNorm (observation z) + operatorNorm R := by
      change ‖observation z - R‖ ≤ ‖observation z‖ + ‖R‖
      exact norm_sub_le _ _
    _ ≤ Fintype.card ι + (Matrix.trace R).re :=
      add_le_add (observation_operatorNorm z) (operatorNorm_psd_le_mass R hR)
    _ ≤ 2 * Fintype.card ι := by linarith

/-- The actual covariance matrix after centering at the true block. -/
def varianceMatrix (R : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (((Fintype.card ι : ℝ) * (Matrix.trace R).re : ℝ) : ℂ) • 1 +
    (((Fintype.card ι : ℝ) - 1 : ℝ) : ℂ) • R - R * R

lemma observation_mul_integrable (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (i j : ι) :
    Integrable (fun z => (observation z * R) i j) (outcomeMeasure μ R) := by
  simp only [Matrix.mul_apply]
  exact integrable_finset_sum Finset.univ (fun a _ =>
    (affine_entry_integrable μ H R hR hw _ _ i a).mul_const (R a j))

lemma mul_observation_integrable (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (i j : ι) :
    Integrable (fun z => (R * observation z) i j) (outcomeMeasure μ R) := by
  simp only [Matrix.mul_apply]
  exact integrable_finset_sum Finset.univ (fun a _ =>
    (affine_entry_integrable μ H R hR hw _ _ a j).const_mul (R i a))

lemma integral_observation_mul (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (i j : ι) :
    (∫ z, (observation z * R) i j ∂outcomeMeasure μ R) = (R * R) i j := by
  simp only [Matrix.mul_apply]
  have hz : ∀ a, Integrable (fun z => observation z i a * R a j) (outcomeMeasure μ R) :=
    fun a => (affine_entry_integrable μ H R hR hw _ _ i a).mul_const (R a j)
  rw [integral_finset_sum Finset.univ (fun a _ => hz a)]
  simp only [integral_mul_const, observation_mean μ H R hR hw]

lemma integral_mul_observation (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (i j : ι) :
    (∫ z, (R * observation z) i j ∂outcomeMeasure μ R) = (R * R) i j := by
  simp only [Matrix.mul_apply]
  have hz : ∀ a, Integrable (fun z => R i a * observation z a j) (outcomeMeasure μ R) :=
    fun a => (affine_entry_integrable μ H R hR hw _ _ a j).const_mul (R i a)
  rw [integral_finset_sum Finset.univ (fun a _ => hz a)]
  simp only [integral_const_mul, observation_mean μ H R hR hw]

omit [Nonempty ι] in
lemma centered_square_identity (R : Matrix ι ι ℂ) (z : Outcome ι) :
    (observation z - R) * (observation z - R) =
      observation z * observation z - observation z * R - R * observation z + R * R := by
  noncomm_ring

/-- The covariance is obtained by integrating the actual centered matrix square. -/
theorem centered_second_moment (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (i j : ι) :
    (∫ z, ((observation z - R) * (observation z - R)) i j ∂outcomeMeasure μ R) =
      varianceMatrix R i j := by
  letI : IsProbabilityMeasure (outcomeMeasure μ R) := ⟨outcomeMeasure_univ μ H R hR hw⟩
  have h₂ : Integrable (fun z => (observation z * observation z) i j) (outcomeMeasure μ R) := by
    simp_rw [observation_square]
    exact affine_entry_integrable μ H R hR hw _ _ i j
  have hl := observation_mul_integrable μ H R hR hw i j
  have hr := mul_observation_integrable μ H R hR hw i j
  simp_rw [centered_square_identity, Matrix.add_apply, Matrix.sub_apply]
  have h₂l : Integrable (fun z => (observation z * observation z) i j -
      (observation z * R) i j) (outcomeMeasure μ R) := h₂.sub hl
  have h₂lr : Integrable (fun z => (observation z * observation z) i j -
      (observation z * R) i j - (R * observation z) i j) (outcomeMeasure μ R) := h₂l.sub hr
  rw [integral_add h₂lr (integrable_const ((R * R) i j)),
    integral_sub h₂l hr, integral_sub h₂ hl,
    observation_second_moment μ H R hR hw, integral_observation_mul μ H R hR hw,
    integral_mul_observation μ H R hR hw]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]
  have ht : ((Matrix.trace R).re : ℂ) = Matrix.trace R := by
    have he := EnergyReality.trace_hermitian_product_real R (1 : Matrix ι ι ℂ) hR.1.eq (by simp)
    simpa only [Matrix.mul_one] using he
  simp only [varianceMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  rw [ht]
  ring

lemma varianceMatrix_posSemidef (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) : (varianceMatrix R).PosSemidef := by
  have hk : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hm := psd_mass_complement R hR
  have hcomp : ((1 : Matrix ι ι ℂ) - R).PosSemidef := by
    have ht := (Matrix.PosSemidef.one (n := ι) (R := ℂ)).smul (α := ℂ)
      (show (0 : ℂ) ≤ ((1 - (Matrix.trace R).re : ℝ) : ℂ) by exact_mod_cast sub_nonneg.mpr hw)
    have he : (((1 - (Matrix.trace R).re : ℝ) : ℂ)) • (1 : Matrix ι ι ℂ) +
      (((Matrix.trace R).re : ℂ) • 1 - R) = 1 - R := by
      push_cast
      module
    exact he ▸ ht.add hm
  have hcomm : Commute R (1 - R) := by change R * (1 - R) = (1 - R) * R; noncomm_ring
  have hprod : (R * (1 - R)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (hcomm.mul_nonneg hR.nonneg hcomp.nonneg)
  have hp := hm.smul (α := ℂ) (show (0 : ℂ) ≤ (Fintype.card ι : ℂ) by exact_mod_cast Nat.zero_le _)
  have hq := hR.smul (α := ℂ)
    (show (0 : ℂ) ≤ (((2 * (Fintype.card ι : ℝ) - 2 : ℝ) : ℂ)) by exact_mod_cast (by linarith : 0 ≤ 2 * (Fintype.card ι : ℝ) - 2))
  have he : (Fintype.card ι : ℂ) • (((Matrix.trace R).re : ℂ) • (1 : Matrix ι ι ℂ) - R) +
      (((2 * (Fintype.card ι : ℝ) - 2 : ℝ) : ℂ)) • R + R * (1 - R) = varianceMatrix R := by
    unfold varianceMatrix
    push_cast
    rw [Matrix.mul_sub, Matrix.mul_one]
    module
  exact he ▸ (hp.add hq).add hprod

/-- The actual covariance operator norm is at most 2 k W whenever the block
mass is bounded by W. No concentration or variance estimate is an input. -/
theorem variance_operatorNorm (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (W : ℝ) (hW : (Matrix.trace R).re ≤ W) :
    operatorNorm (varianceMatrix R) ≤ 2 * Fintype.card ι * W := by
  have hk : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hw₀ : 0 ≤ (Matrix.trace R).re := (hR.trace_nonneg).1
  have hW₀ : 0 ≤ W := hw₀.trans hW
  have hm := (psd_mass_complement R hR).smul (α := ℂ)
    (show (0 : ℂ) ≤ (((Fintype.card ι : ℝ) - 1 : ℝ) : ℂ) by exact_mod_cast sub_nonneg.mpr hk)
  have hc : 0 ≤ 2 * (Fintype.card ι : ℝ) * W -
      (2 * (Fintype.card ι : ℝ) - 1) * (Matrix.trace R).re := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * (Fintype.card ι : ℝ) by positivity) (sub_nonneg.mpr hW)]
  have hi := (Matrix.PosSemidef.one (n := ι) (R := ℂ)).smul (α := ℂ)
    (show (0 : ℂ) ≤ ((2 * (Fintype.card ι : ℝ) * W -
      (2 * (Fintype.card ι : ℝ) - 1) * (Matrix.trace R).re : ℝ) : ℂ) by exact_mod_cast hc)
  have hs : (R * R).PosSemidef := by simpa only [pow_two] using hR.pow 2
  have he : ((2 * (Fintype.card ι : ℝ) * W -
        (2 * (Fintype.card ι : ℝ) - 1) * (Matrix.trace R).re : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) +
      ((((Fintype.card ι : ℝ) - 1 : ℝ) : ℂ)) •
        (((Matrix.trace R).re : ℂ) • 1 - R) + R * R =
      ((2 * (Fintype.card ι : ℝ) * W : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - varianceMatrix R := by
    unfold varianceMatrix
    push_cast
    module
  apply operatorNorm_le_of_psd _ (varianceMatrix_posSemidef R hR hw) _ (by positivity)
  exact he ▸ (hi.add hm).add hs

/-- Entrywise matrix expectation, using the actual outcome measure. -/
def matrixExpectation {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (f : Ω → Matrix ι ι ℂ) : Matrix ι ι ℂ := fun i j => ∫ z, f z i j ∂ν

lemma observation_measurable : Measurable (observation (ι := ι)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact measurable_affine_entry _ _ i j

lemma observation_entry_integrable (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (i j : ι) :
    Integrable (fun z => observation z i j) (outcomeMeasure μ R) :=
  affine_entry_integrable μ H R hR hw _ _ i j

lemma centered_entry_integrable (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (i j : ι) :
    Integrable (fun z => (observation z - R) i j) (outcomeMeasure μ R) := by
  letI : IsProbabilityMeasure (outcomeMeasure μ R) := ⟨outcomeMeasure_univ μ H R hR hw⟩
  exact (observation_entry_integrable μ H R hR hw i j).sub (integrable_const (R i j))

lemma centered_square_entry_integrable (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (i j : ι) :
    Integrable (fun z => ((observation z - R) * (observation z - R)) i j) (outcomeMeasure μ R) := by
  letI : IsProbabilityMeasure (outcomeMeasure μ R) := ⟨outcomeMeasure_univ μ H R hR hw⟩
  have h₂ : Integrable (fun z => (observation z * observation z) i j) (outcomeMeasure μ R) := by
    simp_rw [observation_square]
    exact affine_entry_integrable μ H R hR hw _ _ i j
  have hl := observation_mul_integrable μ H R hR hw i j
  have hr := mul_observation_integrable μ H R hR hw i j
  simp_rw [centered_square_identity, Matrix.add_apply, Matrix.sub_apply]
  exact ((h₂.sub hl).sub hr).add (integrable_const ((R * R) i j))

lemma centered_mean_zero (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) :
    matrixExpectation (outcomeMeasure μ R) (fun z => observation z - R) = 0 := by
  letI : IsProbabilityMeasure (outcomeMeasure μ R) := ⟨outcomeMeasure_univ μ H R hR hw⟩
  ext i j
  change (∫ z, observation z i j - R i j ∂outcomeMeasure μ R) = 0
  rw [integral_sub (observation_entry_integrable μ H R hR hw i j) (integrable_const (R i j)),
    observation_mean μ H R hR hw]
  simp [integral_const, measureReal_univ_eq_one]

/-- Eq. (42) in matrix form, with the full-copy probability law, its actual
observation, and the actual centered second moment. -/
theorem observation_moments (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) :
    IsProbabilityMeasure (outcomeMeasure μ R) ∧
      matrixExpectation (outcomeMeasure μ R) observation = R ∧
      matrixExpectation (outcomeMeasure μ R) (fun z => observation z * observation z) =
        (((Fintype.card ι : ℝ) * (Matrix.trace R).re : ℝ) : ℂ) • 1 +
          (((Fintype.card ι : ℝ) - 1 : ℝ) : ℂ) • R ∧
      matrixExpectation (outcomeMeasure μ R) (fun z =>
        (observation z - R) * (observation z - R)) = varianceMatrix R := by
  refine ⟨⟨outcomeMeasure_univ μ H R hR hw⟩, ?_, ?_, ?_⟩
  · ext i j
    exact observation_mean μ H R hR hw i j
  · ext i j
    rw [matrixExpectation, observation_second_moment μ H R hR hw]
    have ht : ((Matrix.trace R).re : ℂ) = Matrix.trace R := by
      have he := EnergyReality.trace_hermitian_product_real R (1 : Matrix ι ι ℂ) hR.1.eq (by simp)
      simpa only [Matrix.mul_one] using he
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    rw [ht]
  · ext i j
    exact centered_second_moment μ H R hR hw i j

/-- The variance bound directly on the actual matrix integral, ready for a
separate generic matrix concentration theorem. -/
theorem actual_variance_operatorNorm (μ : Measure (PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (W : ℝ) (hW : (Matrix.trace R).re ≤ W) :
    operatorNorm (matrixExpectation (outcomeMeasure μ R) (fun z =>
      (observation z - R) * (observation z - R))) ≤ 2 * Fintype.card ι * W := by
  rw [(observation_moments μ H R hR hw).2.2.2]
  exact variance_operatorNorm R hR hw W hW

end Paper26.OneCopyObservation
