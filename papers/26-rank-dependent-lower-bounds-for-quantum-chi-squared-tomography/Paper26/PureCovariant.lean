import Paper26.PureMinimax
import Paper26.PureTensorSuccess
import Paper26.AdaptiveCollectiveEmbedding
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The actual covariant pure-state experiment

The only new external interface is the classical Haar tensor moment
(Harrow 2013, Proposition 6): its entries integrate to `P_sym / D_n`.
It does not assume a Born law, tail distribution, expected overlap or risk.
The complementary symmetric-space projection is added as a constant effect;
this gives a normalized POVM on the full tensor space and contributes zero
on every actual pure tensor input.
-/
noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.PureCovariant
open QuantumModel HaarFrames SymmetricSupport CollectiveModel ContinuousPOVM
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

/-- The usual dimension of the actual symmetric subspace. -/
def dimension (ι : Type*) [Fintype ι] (n : ℕ) : ℕ :=
  (n + Fintype.card ι - 1).choose n

/-- Exact entrywise standard Haar moment, with every copy number retained. -/
structure HaarTensorMomentInput (μ : Measure (Frame ι (Fin 1))) : Prop where
  moment : ∀ (n : ℕ) (P : SymmetricProjectorInput ι n) (i j : Fin n → ι),
    (∫ U, (TensorCopies.density U.density n).matrix i j ∂μ) =
      ((dimension ι n : ℝ)⁻¹ : ℂ) * P.projector.matrix i j

omit [DecidableEq ι] in
theorem dimension_pos [Nonempty ι] (n : ℕ) : 0 < dimension ι n := by
  unfold dimension
  apply Nat.choose_pos
  have h := Fintype.card_pos (α := ι)
  omega

/-- All actual density entries are bounded by one; this supplies ordinary
Bochner integrability of the Haar tensor moment. -/
theorem density_entry_norm_le_one {η : Type*} [Fintype η] [DecidableEq η]
    (ρ : Density η) (i j : η) : ‖ρ.matrix i j‖ ≤ 1 := by
  have h := AdaptiveCollectiveEmbedding.psd_entry_norm_le_trace ρ.matrix ρ.positive i j
  simpa only [ρ.trace_one, Complex.one_re] using h

theorem tensor_entry_integrable (μ : Measure (Frame ι (Fin 1)))
    [IsProbabilityMeasure μ] (n : ℕ) (i j : Fin n → ι) :
    Integrable (fun U => (TensorCopies.density U.density n).matrix i j) μ := by
  apply Integrable.of_bound (PureTensorSuccess.measurable_frame_tensor_entry n i j).aestronglyMeasurable 1
  exact ae_of_all _ fun U => density_entry_norm_le_one _ i j

/-- The actual full-space effect. The added complementary projection
never changes any pure-input outcome density. -/
def effect {n : ℕ} (P : SymmetricProjectorInput ι n) (U : Frame ι (Fin 1)) :
    Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  (dimension ι n : ℝ) • (TensorCopies.density U.density n).matrix + (1 - P.projector.matrix)

theorem effect_positive {n : ℕ} (P : SymmetricProjectorInput ι n)
    (U : Frame ι (Fin 1)) : (effect P U).PosSemidef := by
  exact ((TensorCopies.density U.density n).positive.smul (Nat.cast_nonneg _)).add
    (PureMinimax.complement P.projector).positive

/-- A genuine normalized collective POVM, including the ambient nonsymmetric
subspace rather than treating its projector as the identity. -/
def measurement [Nonempty ι] (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricProjectorInput ι n) :
    DominatedPOVM (Fin n → ι) (Frame ι (Fin 1)) where
  reference := μ
  reference_finite := inferInstance
  effect := effect P
  entry_measurable i j := by
    change Measurable (fun U : Frame ι (Fin 1) => (dimension ι n : ℝ) •
      (TensorCopies.density U.density n).matrix i j + (1 - P.projector.matrix) i j)
    exact ((PureTensorSuccess.measurable_frame_tensor_entry n i j).const_smul _).add measurable_const
  positive_ae := ae_of_all _ (effect_positive P)
  entry_integrable i j := by
    change Integrable (fun U : Frame ι (Fin 1) => (dimension ι n : ℝ) •
      (TensorCopies.density U.density n).matrix i j + (1 - P.projector.matrix) i j) μ
    exact ((tensor_entry_integrable μ n i j).smul (dimension ι n : ℝ)).add (integrable_const _)
  total i j := by
    change (∫ U : Frame ι (Fin 1), (dimension ι n : ℝ) • (TensorCopies.density U.density n).matrix i j +
      (1 - P.projector.matrix) i j ∂μ) = _
    have hi : Integrable (fun U : Frame ι (Fin 1) => (dimension ι n : ℝ) •
        (TensorCopies.density U.density n).matrix i j) μ :=
      (tensor_entry_integrable μ n i j).fun_smul (dimension ι n : ℝ)
    rw [integral_add hi (integrable_const _), integral_smul, H.moment n P i j]
    simp only [integral_const, measureReal_univ_eq_one, one_smul, Complex.real_smul]
    have hd : (dimension ι n : ℂ) ≠ 0 := by exact_mod_cast (dimension_pos (ι := ι) n).ne'
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
    simp

/-- Actual pure-state overlap, without choosing representatives of rays. -/
def overlap (U V : Frame ι (Fin 1)) : ℝ := (Matrix.trace (U.density.matrix * V.density.matrix)).re

/-- Tensor multiplication and trace give the actual likelihood power. -/
theorem tensor_pairing (U V : Frame ι (Fin 1)) (n : ℕ) :
    Matrix.trace ((TensorCopies.density U.density n).matrix *
      (TensorCopies.density V.density n).matrix) =
      (Matrix.trace (U.density.matrix * V.density.matrix)) ^ n := by
  change Matrix.trace (TensorCopies.matrix U.density.matrix n *
    TensorCopies.matrix V.density.matrix n) = _
  rw [← TensorCopies.matrix_mul, TensorCopies.matrix_trace]
  simp

theorem overlap_complex (U V : Frame ι (Fin 1)) :
    Matrix.trace (U.density.matrix * V.density.matrix) = (overlap U V : ℂ) := by
  apply Complex.ext
  · rfl
  · exact EnergyReality.trace_hermitian_product_im _ _ U.density.hermitian.eq V.density.hermitian.eq

/-- Born's rule gives the usual covariant likelihood exactly; the
nonsymmetric complement has zero Born weight on pure tensor inputs. -/
theorem born_pure [Nonempty ι] (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricProjectorInput ι n)
    (U V : Frame ι (Fin 1)) :
    (measurement μ H P).born (TensorCopies.density U.density n) V =
      (dimension ι n : ℝ) * overlap U V ^ n := by
  have hP : (TensorCopies.density U.density n).matrix * P.projector.matrix =
      (TensorCopies.density U.density n).matrix := by
    have h := congrArg Matrix.conjTranspose (contains_frame_tensor P U)
    simpa only [Matrix.conjTranspose_mul, P.projector.hermitian.eq,
      (TensorCopies.density U.density n).hermitian.eq] using h
  unfold DominatedPOVM.born DominatedPOVM.complexBorn
  change (Matrix.trace ((TensorCopies.density U.density n).matrix * effect P V)).re = _
  rw [effect, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.mul_sub, Matrix.mul_one, hP, sub_self, Matrix.trace_zero, add_zero,
    tensor_pairing, overlap_complex]
  simp only [Complex.real_smul, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

/-- Both overlap and complementary mass are actual probabilities. -/
theorem overlap_mem_unit (U V : Frame ι (Fin 1)) :
    0 ≤ overlap U V ∧ overlap U V ≤ 1 := by
  have h := PureMinimax.tailMass_mem_unit U.density V.projector
  have he : V.projector.matrix = V.density.matrix := by
    simp only [Frame.density_matrix, Fintype.card_fin, Nat.cast_one, inv_one, one_smul,
      Frame.projector_matrix]
  unfold PureMinimax.tailMass at h
  rw [he] at h
  change 0 ≤ 1 - overlap U V ∧ 1 - overlap U V ≤ 1 at h
  constructor <;> linarith

theorem measurable_overlap (U : Frame ι (Fin 1)) : Measurable (overlap U) := by
  change Measurable (fun V : Frame ι (Fin 1) =>
    (∑ i, ∑ j, U.density.matrix i j * V.density.matrix j i).re)
  apply Measurable.re (𝕜 := ℂ)
  apply Finset.measurable_sum Finset.univ
  intro i _
  apply Finset.measurable_sum Finset.univ
  intro j _
  exact (((measurable_pi_apply i).comp ((measurable_pi_apply j).comp
    Frame.measurable_density_matrix)).const_mul _)

theorem overlap_pow_integrable (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (U : Frame ι (Fin 1)) (n : ℕ) : Integrable (fun V => overlap U V ^ n) μ := by
  apply Integrable.of_bound ((measurable_overlap U).pow_const n).aestronglyMeasurable 1
  apply ae_of_all
  intro V
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (overlap_mem_unit U V).1 _)]
  exact pow_le_one₀ (overlap_mem_unit U V).1 (overlap_mem_unit U V).2

/-- Exact scalar Haar moment is derived from actual POVM normalization. -/
theorem overlap_moment [Nonempty ι] (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricProjectorInput ι n)
    (U : Frame ι (Fin 1)) :
    (∫ V, overlap U V ^ n ∂μ) = (dimension ι n : ℝ)⁻¹ := by
  have h := (measurement μ H P).born_integral (TensorCopies.density U.density n)
  simp_rw [born_pure] at h
  rw [integral_const_mul] at h
  have hd : (dimension ι n : ℝ) ≠ 0 := by exact_mod_cast (dimension_pos (ι := ι) n).ne'
  apply (mul_left_cancel₀ hd)
  simpa [hd] using h

omit [DecidableEq ι] in
/-- The binomial recurrence retains the exact dimension normalization. -/
theorem dimension_recurrence [Nonempty ι] (n : ℕ) :
    (dimension ι n : ℝ) * ((n : ℝ) + Fintype.card ι) =
      (dimension ι (n + 1) : ℝ) * (n + 1 : ℝ) := by
  have hd : 0 < Fintype.card ι := Fintype.card_pos
  have h := Nat.succ_mul_choose_eq (n + Fintype.card ι - 1) n
  have htop : (n + Fintype.card ι - 1).succ = n + Fintype.card ι := by omega
  have htop' : n + 1 + Fintype.card ι - 1 = n + Fintype.card ι := by omega
  rw [htop] at h
  simp only [dimension, htop']
  have hh : (dimension ι n) * (n + Fintype.card ι) =
      (n + Fintype.card ι).choose (n + 1) * (n + 1) := by
    simpa only [dimension, Nat.succ_eq_add_one, mul_comm] using h
  exact_mod_cast hh

/-- The actual outcome law has complementary overlap mean `(d-1)/(n+d)`.
No Beta distribution or expected-tail identity is an input. -/
theorem expected_tail [Nonempty ι] (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricProjectorInput ι n)
    (Q : SymmetricProjectorInput ι (n + 1)) (U : Frame ι (Fin 1)) :
    (∫ V, (1 - overlap U V) ∂(measurement μ H P).outcomeMeasure
      (TensorCopies.density U.density n)) =
      ((Fintype.card ι : ℝ) - 1) / ((n : ℝ) + Fintype.card ι) := by
  let M := measurement μ H P
  have hb (V : Frame ι (Fin 1)) :
      0 ≤ M.born (TensorCopies.density U.density n) V :=
    M.born_nonneg _ (effect_positive P V)
  rw [DominatedPOVM.outcomeMeasure, integral_withDensity_eq_integral_toReal_smul
    (M.born_measurable _).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hb _), smul_eq_mul]
  change (∫ V : Frame ι (Fin 1), (measurement μ H P).born
    (TensorCopies.density U.density n) V * (1 - overlap U V) ∂μ) = _
  simp_rw [born_pure]
  have he (V : Frame ι (Fin 1)) :
      (dimension ι n : ℝ) * overlap U V ^ n * (1 - overlap U V) =
      (dimension ι n : ℝ) * (overlap U V ^ n - overlap U V ^ (n + 1)) := by
    rw [pow_succ]; ring
  simp_rw [he]
  rw [integral_const_mul, integral_sub (overlap_pow_integrable μ U n)
    (overlap_pow_integrable μ U (n + 1)), overlap_moment μ H P U, overlap_moment μ H Q U]
  have hn : (dimension ι n : ℝ) ≠ 0 := by exact_mod_cast (dimension_pos (ι := ι) n).ne'
  have hq : (dimension ι (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (dimension_pos (ι := ι) (n + 1)).ne'
  have hd : (n : ℝ) + Fintype.card ι ≠ 0 := by
    have hp : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
    positivity
  have hrec := dimension_recurrence (ι := ι) n
  field_simp
  nlinarith

end Paper26.PureCovariant
