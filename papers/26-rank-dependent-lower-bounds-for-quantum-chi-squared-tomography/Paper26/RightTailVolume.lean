import Paper26.TailLossConstraints
import Paper26.ScalarTailBall
import Mathlib.Analysis.MeanInequalities

/-!
# The right-inverse ellipsoid numerator in Theorem 2.4

`ellipsoidEnergy` is the original matrix trace quadratic form.  It is turned
into the actual Frobenius ball by positive diagonal row scaling.  The sole
new external input is the classical coordinate change-of-variables formula
for an arbitrary set under positive diagonal scaling of its complex entries:
each complex coordinate contributes two equal real scale factors.  This is
the diagonal-coordinate specialization of Mathlib's
`MeasureTheory.Measure.addHaar_image_linearMap` in
`MeasureTheory/Measure/Lebesgue/EqHaar.lean`; the underlying real/imaginary
identification carries the fixed product Lebesgue measure.

No ellipsoid formula, product-of-eigenvalues bound, or final numerator bound
is an input.  Square-root scaling, its Jacobian product simplification,
AM--GM, and the epsilon substitution are proved internally below.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace Paper26.RightTailVolume

open MeasureTheory ShellAccounting TailLossConstraints ScalarTailBall

variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]

/-- Actual row scaling; the factor is the same on real and imaginary coordinates. -/
def rowScale (c : σ → ℝ) (Z : Matrix σ κ ℂ) : Matrix σ κ ℂ :=
  fun i j => (c i : ℂ) * Z i j

/-- This coordinate map is a genuine real linear map. -/
def rowScaleLinear (c : σ → ℝ) : Matrix σ κ ℂ →ₗ[ℝ] Matrix σ κ ℂ where
  toFun := rowScale c
  map_add' := by intro X Y; ext i j; simp [rowScale, mul_add]
  map_smul' := by
    intro t X
    ext i j
    simp [rowScale, Complex.real_smul, mul_assoc, mul_left_comm]

/-- Exact classical diagonal-coordinate Jacobian formula, for every set and
every positive row scale.  It contains no energy or radius parameter. -/
structure PositiveRowScalingInput (σ κ : Type*) [Fintype σ] [Fintype κ] : Prop where
  image_measure : ∀ (c : σ → ℝ), (∀ i, 0 < c i) → ∀ S : Set (Matrix σ κ ℂ),
    TailGeometry.matrixLebesgue ((rowScale c : Matrix σ κ ℂ → Matrix σ κ ℂ) '' S) =
      ENNReal.ofReal (∏ i : σ, ∏ _j : κ, (c i) ^ 2) * TailGeometry.matrixLebesgue S

/-- Every complex matrix entry occurs with the correct right-inverse weight. -/
theorem ellipsoidEnergy_spectral (a : σ → ℝ) (Z : Matrix σ κ ℂ) :
    ellipsoidEnergy a Z = ∑ i, ∑ j, Complex.normSq (Z i j) / a i := by
  rw [← gram_weightedTrace a Z, weightedTrace_spectral]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.mul_conj, Complex.re_sum, Complex.ofReal_re, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Square-root row scaling converts the original trace ellipsoid to a ball. -/
theorem ellipsoidEnergy_scaled (a : σ → ℝ) (ha : ∀ i, 0 < a i)
    (Z : Matrix σ κ ℂ) :
    ellipsoidEnergy a (rowScale (fun i => Real.sqrt (a i)) Z) = frobeniusSq Z := by
  rw [ellipsoidEnergy_spectral]
  simp only [rowScale, Complex.normSq_mul, Complex.normSq_ofReal,
    frobeniusSq, Complex.sq_norm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.mul_self_sqrt (ha i).le]
  field_simp [ne_of_gt (ha i)]

lemma rowScale_sqrt_inverse (a : σ → ℝ) (ha : ∀ i, 0 < a i)
    (Z : Matrix σ κ ℂ) :
    rowScale (fun i => Real.sqrt (a i))
      (rowScale (fun i => (Real.sqrt (a i))⁻¹) Z) = Z := by
  ext i j
  simp only [rowScale, ← mul_assoc, ← Complex.ofReal_mul]
  rw [mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (ha i)))]
  simp

/-- Equality of actual sets, preceding the use of any measure theorem. -/
theorem ellipsoid_eq_scaled_ball (a : σ → ℝ) (ha : ∀ i, 0 < a i) (K : ℝ) :
    {Z : Matrix σ κ ℂ | ellipsoidEnergy a Z ≤ K} =
      rowScale (fun i => Real.sqrt (a i)) '' (frobeniusBall K : Set (Matrix σ κ ℂ)) := by
  ext Z
  constructor
  · intro hZ
    refine ⟨rowScale (fun i => (Real.sqrt (a i))⁻¹) Z, ?_, rowScale_sqrt_inverse a ha Z⟩
    change frobeniusSq (rowScale (fun i => (Real.sqrt (a i))⁻¹) Z) ≤ K
    rw [← ellipsoidEnergy_scaled a ha, rowScale_sqrt_inverse a ha]
    exact hZ
  · rintro ⟨W, hW, rfl⟩
    change ellipsoidEnergy a (rowScale (fun i => Real.sqrt (a i)) W) ≤ K
    rw [ellipsoidEnergy_scaled a ha]
    exact hW

/-- The real-coordinate determinant product is exactly the source's
`(prod a_i)^r`, proved using the two real coordinates of every complex entry. -/
theorem sqrt_row_jacobian (a : σ → ℝ) (ha : ∀ i, 0 < a i) :
    (∏ i : σ, ∏ _j : κ, (Real.sqrt (a i)) ^ 2) =
      (∏ i, a i) ^ Fintype.card κ := by
  simp_rw [Real.sq_sqrt (ha _).le]
  simp only [Finset.prod_const, Finset.card_univ]
  exact Finset.prod_pow _ _ _

/-- Exact ellipsoid volume before the determinant AM--GM estimate. -/
theorem ellipsoid_volume_exact
    (J : PositiveRowScalingInput σ κ) (BV : EuclideanBallVolumeInput σ κ)
    (a : σ → ℝ) (ha : ∀ i, 0 < a i) {K : ℝ} (hK : 0 ≤ K) :
    TailGeometry.matrixLebesgue {Z : Matrix σ κ ℂ | ellipsoidEnergy a Z ≤ K} =
      ENNReal.ofReal ((∏ i, a i) ^ Fintype.card κ) *
        ENNReal.ofReal (euclideanBallVolume (σ := σ) (κ := κ) K) := by
  rw [ellipsoid_eq_scaled_ball a ha K,
    J.image_measure _ (fun i => Real.sqrt_pos.mpr (ha i)),
    sqrt_row_jacobian a ha, BV.squared_ball K hK]

/-- The determinant bound is an internal specialization of Mathlib's AM--GM. -/
theorem product_le_mean_pow [Nonempty σ] (a : σ → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∏ i, a i) ≤ ((∑ i, a i) / (Fintype.card σ : ℝ)) ^ Fintype.card σ := by
  have hs : (0 : ℝ) < Fintype.card σ := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : (0 : ℝ) < ∑ _i : σ, (1 : ℝ) := by simpa using hs
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : σ => (1 : ℝ)) a
    (fun _ _ => by norm_num) hsum (fun i _ => ha i)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at h
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => ha i)) _) h
    (Fintype.card σ)
  simpa only [Real.rpow_inv_natCast_pow (Finset.prod_nonneg (fun i _ => ha i))
    (Nat.ne_of_gt Fintype.card_pos)] using hp

lemma euclideanBallVolume_nonneg {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ euclideanBallVolume (σ := σ) (κ := κ) T := by
  unfold euclideanBallVolume
  positivity

lemma euclideanBallVolume_mono {T S : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S) :
    euclideanBallVolume (σ := σ) (κ := κ) T ≤ euclideanBallVolume (σ := σ) (κ := κ) S := by
  unfold euclideanBallVolume
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT hTS _) (by positivity)

/-- The actual ellipsoid numerator bound, with the determinant estimate proved internally. -/
theorem ellipsoid_volume_le_formula [Nonempty σ]
    (J : PositiveRowScalingInput σ κ) (BV : EuclideanBallVolumeInput σ κ)
    (a : σ → ℝ) (ha : ∀ i, 0 < a i) {K : ℝ} (hK : 0 ≤ K) :
    TailGeometry.matrixLebesgue {Z : Matrix σ κ ℂ | ellipsoidEnergy a Z ≤ K} ≤
      ENNReal.ofReal (euclideanBallVolume (σ := σ) (κ := κ)
        (K * (∑ i, a i) / (Fintype.card σ : ℝ))) := by
  have hprod : 0 ≤ ∏ i, a i := Finset.prod_nonneg (fun i _ => (ha i).le)
  have ham := product_le_mean_pow a (fun i => (ha i).le)
  have hpow := pow_le_pow_left₀ hprod ham (Fintype.card κ)
  rw [← pow_mul] at hpow
  rw [ellipsoid_volume_exact J BV a ha hK,
    ← ENNReal.ofReal_mul (pow_nonneg hprod _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∏ i, a i) ^ Fintype.card κ * euclideanBallVolume (σ := σ) (κ := κ) K ≤
      (((∑ i, a i) / (Fintype.card σ : ℝ)) ^
        (Fintype.card σ * Fintype.card κ)) * euclideanBallVolume (σ := σ) (κ := κ) K :=
      mul_le_mul_of_nonneg_right hpow (euclideanBallVolume_nonneg hK)
    _ = euclideanBallVolume (σ := σ) (κ := κ)
        (K * (∑ i, a i) / (Fintype.card σ : ℝ)) := by
      unfold euclideanBallVolume complexDimension
      rw [show K * (∑ i, a i) / (Fintype.card σ : ℝ) =
        K * ((∑ i, a i) / (Fintype.card σ : ℝ)) by ring, mul_pow]
      ring

/-- The squared radius in the right-inverse part of Theorem 2.4. -/
def rightSquaredRadius (ε : ℝ) : ℝ :=
  9 * (Fintype.card κ : ℝ) ^ 2 * ε ^ 2 / (Fintype.card σ : ℝ)

/-- Substituting the internally obtained tail-mass bound gives the source's
`9 r^2 epsilon^2 / s` squared radius. -/
theorem ellipsoid_volume_epsilon [Nonempty σ]
    (J : PositiveRowScalingInput σ κ) (BV : EuclideanBallVolumeInput σ κ)
    (a : σ → ℝ) (ha : ∀ i, 0 < a i) {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∑ i, a i ≤ ε) :
    TailGeometry.matrixLebesgue {Z : Matrix σ κ ℂ |
      ellipsoidEnergy a Z ≤ 9 * (Fintype.card κ : ℝ) ^ 2 * ε} ≤
      ENNReal.ofReal (euclideanBallVolume (σ := σ) (κ := κ)
        (rightSquaredRadius (σ := σ) (κ := κ) ε)) := by
  have hs : (0 : ℝ) < Fintype.card σ := Nat.cast_pos.mpr Fintype.card_pos
  have hK : 0 ≤ 9 * (Fintype.card κ : ℝ) ^ 2 * ε := by positivity
  have ht : 0 ≤ (9 * (Fintype.card κ : ℝ) ^ 2 * ε) * (∑ i, a i) /
      (Fintype.card σ : ℝ) := by
    exact div_nonneg (mul_nonneg hK (Finset.sum_nonneg (fun i _ => (ha i).le))) hs.le
  have hrad : (9 * (Fintype.card κ : ℝ) ^ 2 * ε) * (∑ i, a i) /
      (Fintype.card σ : ℝ) ≤ rightSquaredRadius (σ := σ) (κ := κ) ε := by
    unfold rightSquaredRadius
    apply (div_le_div_iff_of_pos_right hs).mpr
    have hm := mul_le_mul_of_nonneg_left hmass hK
    nlinarith
  exact (ellipsoid_volume_le_formula J BV a ha hK).trans
    (ENNReal.ofReal_le_ofReal (euclideanBallVolume_mono ht hrad))

end Paper26.RightTailVolume

namespace Paper26.RightTailVolume

open MeasureTheory TailLossConstraints ScalarTailBall
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]

/-- The numerator bound applies to any actual successful subset after the
loss-to-ellipsoid inclusion has been proved. -/
theorem subset_volume_epsilon [Nonempty σ]
    (J : PositiveRowScalingInput σ κ) (BV : EuclideanBallVolumeInput σ κ)
    (a : σ → ℝ) (ha : ∀ i, 0 < a i) {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∑ i, a i ≤ ε) (S : Set (Matrix σ κ ℂ))
    (hS : S ⊆ {Z : Matrix σ κ ℂ |
      ellipsoidEnergy a Z ≤ 9 * (Fintype.card κ : ℝ) ^ 2 * ε}) :
    TailGeometry.matrixLebesgue S ≤
      ENNReal.ofReal (euclideanBallVolume (σ := σ) (κ := κ)
        (rightSquaredRadius (σ := σ) (κ := κ) ε)) :=
  (measure_mono hS).trans (ellipsoid_volume_epsilon J BV a ha hε hmass)

end Paper26.RightTailVolume
