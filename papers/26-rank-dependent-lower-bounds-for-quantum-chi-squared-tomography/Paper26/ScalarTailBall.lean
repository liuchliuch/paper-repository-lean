import Paper26.TailGeometry
import Mathlib.Data.Real.Sqrt

/-!
# Scalar tail bodies and the Frobenius ball in Theorem 2.4

The scalar matrix and every energy are actual complex matrix objects. The
inverse-Jordan formula follows from its uniquely solved matrix equation;
no scalar-tail energy identity or radius bound is assumed.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace Paper26.ScalarTailBall

open ShellAccounting

variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]

/-- The uniform tail spectrum with total mass `a`. -/
def scalarA (a : ℝ) : Matrix σ σ ℂ :=
  (((a / (Fintype.card σ : ℝ) : ℝ) : ℂ)) • 1

/-- Positive tail mass gives a genuinely positive-definite scalar matrix. -/
theorem scalarA_posDef [Nonempty σ] {a : ℝ} (ha : 0 < a) :
    (scalarA (σ := σ) a).PosDef := by
  have hs : (0 : ℝ) < Fintype.card σ := Nat.cast_pos.mpr Fintype.card_pos
  exact Matrix.PosDef.one.smul (RCLike.ofReal_pos.mpr (div_pos ha hs))

/-- The inverse Jordan operator for `(a/s)I` is multiplication by `s/a`.
The proof verifies the actual matrix equation and invokes its uniqueness. -/
theorem scalar_jordanInverse [Nonempty σ] {a : ℝ} (ha : 0 < a)
    (Y : Matrix σ σ ℂ) :
    Normalization.jordanInverse (scalarA a) Y =
      (((Fintype.card σ : ℝ) / a : ℝ) : ℂ) • Y := by
  have hs : (0 : ℝ) < Fintype.card σ := Nat.cast_pos.mpr Fintype.card_pos
  let c : ℂ := ((a / (Fintype.card σ : ℝ) : ℝ) : ℂ)
  let d : ℂ := (((Fintype.card σ : ℝ) / a : ℝ) : ℂ)
  have hreal : (a / (Fintype.card σ : ℝ)) * ((Fintype.card σ : ℝ) / a) = 1 := by
    field_simp [ne_of_gt ha, ne_of_gt hs]
  have hcd : c * d = 1 := by
    dsimp [c, d]
    exact_mod_cast hreal
  have hdc : d * c = 1 := by rw [mul_comm, hcd]
  apply (Normalization.jordanInverse_unique_posDef (scalarA a) Y (d • Y)
    (scalarA_posDef ha) ?_).symm
  change (c • (1 : Matrix σ σ ℂ)) * (d • Y) +
    (d • Y) * (c • (1 : Matrix σ σ ℂ)) = (2 : ℂ) • Y
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_smul, hcd, hdc, one_smul, two_smul]

/-- The exact scalar-tail identity from Theorem 2.4. -/
theorem H_scalar [Nonempty σ] {a : ℝ} (ha : 0 < a) (Z : Matrix σ κ ℂ) :
    TailConvexity.H (scalarA a) Z =
      ((Fintype.card σ : ℝ) / a) * frobeniusSq (Z * Zᴴ) := by
  unfold TailConvexity.H TailConvexity.Q TailConvexity.pairing
  rw [scalar_jordanInverse ha, Matrix.mul_smul, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [frobeniusSq_eq_trace]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Squared Frobenius radius forced by a scalar tail-energy sublevel. -/
theorem scalar_sublevel_sq_bound [Nonempty σ] {a K : ℝ} (ha : 0 < a)
    (Z : Matrix σ κ ℂ) (hH : TailConvexity.H (scalarA a) Z ≤ K) :
    (frobeniusSq Z) ^ 2 ≤
      (Fintype.card κ : ℝ) * a * K / (Fintype.card σ : ℝ) := by
  have hs : (0 : ℝ) < Fintype.card σ := Nat.cast_pos.mpr Fintype.card_pos
  rw [H_scalar ha] at hH
  have hg : frobeniusSq (Z * Zᴴ) ≤ K / ((Fintype.card σ : ℝ) / a) := by
    apply (le_div_iff₀ (div_pos hs ha)).mpr
    simpa only [mul_comm] using hH
  calc
    (frobeniusSq Z) ^ 2 ≤ (Fintype.card κ : ℝ) * frobeniusSq (Z * Zᴴ) :=
      TailGeometry.gram_frobenius_inequality Z
    _ ≤ (Fintype.card κ : ℝ) * (K / ((Fintype.card σ : ℝ) / a)) :=
      mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _)
    _ = _ := by
      field_simp [ne_of_gt ha, ne_of_gt hs]

/-- The scalar tail sublevel is contained in its stated Frobenius ball. -/
theorem scalar_sublevel_radius [Nonempty σ] {a K : ℝ} (ha : 0 < a)
    (Z : Matrix σ κ ℂ) (hH : TailConvexity.H (scalarA a) Z ≤ K) :
    frobeniusSq Z ≤ Real.sqrt
      ((Fintype.card κ : ℝ) * a * K / (Fintype.card σ : ℝ)) :=
  Real.le_sqrt_of_sq_le (scalar_sublevel_sq_bound ha Z hH)

/-- The original paper's `T = 3 r^(3/2) ε / sqrt s`, with `r^(3/2)` written
as the exact real expression `r * sqrt r`. -/
def buresSquaredRadius (ε : ℝ) : ℝ :=
  3 * (Fintype.card κ : ℝ) * Real.sqrt (Fintype.card κ : ℝ) * ε /
    Real.sqrt (Fintype.card σ : ℝ)

/-- The precise scalar-tail radius after Equation (21). -/
theorem scalar_sublevel_epsilon_radius [Nonempty σ] {a ε : ℝ}
    (ha : 0 < a) (haε : a ≤ ε) (Z : Matrix σ κ ℂ)
    (hH : TailConvexity.H (scalarA a) Z ≤
      9 * (Fintype.card κ : ℝ) ^ 2 * ε) :
    frobeniusSq Z ≤ buresSquaredRadius (σ := σ) (κ := κ) ε := by
  have hs : (0 : ℝ) < Fintype.card σ := Nat.cast_pos.mpr Fintype.card_pos
  have hr : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
  have hε : 0 < ε := ha.trans_le haε
  have hsq := scalar_sublevel_sq_bound ha Z hH
  have hmul := mul_le_mul_of_nonneg_right haε
    (show 0 ≤ 9 * (Fintype.card κ : ℝ) ^ 3 * ε by positivity)
  have hb : (Fintype.card κ : ℝ) * a *
      (9 * (Fintype.card κ : ℝ) ^ 2 * ε) / (Fintype.card σ : ℝ) ≤
      9 * (Fintype.card κ : ℝ) ^ 3 * ε ^ 2 / (Fintype.card σ : ℝ) := by
    apply (div_le_div_iff_of_pos_right hs).mpr
    nlinarith
  have ht : 0 ≤ buresSquaredRadius (σ := σ) (κ := κ) ε := by
    unfold buresSquaredRadius
    positivity
  have hrootr := Real.sq_sqrt hr
  have hroots := Real.sq_sqrt hs.le
  have htsq : (buresSquaredRadius (σ := σ) (κ := κ) ε) ^ 2 =
      9 * (Fintype.card κ : ℝ) ^ 3 * ε ^ 2 / (Fintype.card σ : ℝ) := by
    unfold buresSquaredRadius
    rw [div_pow]
    simp only [mul_pow, hrootr, hroots]
    ring
  apply (sq_le_sq₀ (frobeniusSq_nonneg Z) ht).mp
  rw [htsq]
  exact hsq.trans hb

/-- An actual Frobenius ball specified by its squared radius. -/
def frobeniusBall (T : ℝ) : Set (Matrix σ κ ℂ) := {Z | frobeniusSq Z ≤ T}

/-- The source's deterministic scalar-body-to-ball inclusion. -/
theorem scalar_body_subset_frobeniusBall [Nonempty σ] {a ε : ℝ}
    (ha : 0 < a) (haε : a ≤ ε) :
    {Z : Matrix σ κ ℂ | TailConvexity.H (scalarA a) Z ≤
        9 * (Fintype.card κ : ℝ) ^ 2 * ε} ⊆
      frobeniusBall (buresSquaredRadius (σ := σ) (κ := κ) ε) := by
  intro Z hZ
  exact scalar_sublevel_epsilon_radius ha haε Z hZ


/-- The complex dimension `q = s*r`, half the underlying real dimension. -/
def complexDimension : ℕ := Fintype.card σ * Fintype.card κ

/-- The classical squared-radius Euclidean-ball volume formula. -/
def euclideanBallVolume (T : ℝ) : ℝ :=
  Real.pi ^ (complexDimension (σ := σ) (κ := κ)) *
    T ^ (complexDimension (σ := σ) (κ := κ)) /
      (Nat.factorial (complexDimension (σ := σ) (κ := κ)) : ℝ)

/-- Exact classical input for an ordinary Euclidean ball in the real and
imaginary matrix coordinates, of real dimension `2*s*r`. It is the standard
formula `π^q T^q/q!` for squared radius `T`, with `q=s*r`.

The general real-inner-product-space statement is
`InnerProductSpace.volume_closedBall_of_dim_even` in Mathlib's
`MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`. The remaining input here
is its specialization under the standard real/imaginary coordinate
identification and the fixed product measure `matrixLebesgue`. The field
quantifies over every nonnegative radius and contains no tail-energy or
quantum-loss condition. -/
structure EuclideanBallVolumeInput (σ κ : Type*) [Fintype σ] [Fintype κ] : Prop where
  squared_ball : ∀ T : ℝ, 0 ≤ T →
    TailGeometry.matrixLebesgue (frobeniusBall T : Set (Matrix σ κ ℂ)) =
      ENNReal.ofReal (euclideanBallVolume (σ := σ) (κ := κ) T)

/-- Monotonicity of the actual standard Lebesgue measure turns the internally
proved scalar-body inclusion into a numerator-volume bound. -/
theorem scalar_body_volume_le_ball [Nonempty σ] {a ε : ℝ}
    (ha : 0 < a) (haε : a ≤ ε) :
    TailGeometry.matrixLebesgue {Z : Matrix σ κ ℂ |
        TailConvexity.H (scalarA a) Z ≤ 9 * (Fintype.card κ : ℝ) ^ 2 * ε} ≤
      TailGeometry.matrixLebesgue
        (frobeniusBall (buresSquaredRadius (σ := σ) (κ := κ) ε) : Set (Matrix σ κ ℂ)) := by
  exact MeasureTheory.measure_mono (scalar_body_subset_frobeniusBall ha haε)

/-- The exact classical ball formula can be applied after all loss-specific
scalar geometry has been proved internally. -/
theorem scalar_body_volume_le_formula [Nonempty σ]
    (BV : EuclideanBallVolumeInput σ κ) {a ε : ℝ} (ha : 0 < a) (haε : a ≤ ε) :
    TailGeometry.matrixLebesgue {Z : Matrix σ κ ℂ |
        TailConvexity.H (scalarA a) Z ≤ 9 * (Fintype.card κ : ℝ) ^ 2 * ε} ≤
      ENNReal.ofReal (euclideanBallVolume (σ := σ) (κ := κ)
        (buresSquaredRadius (σ := σ) (κ := κ) ε)) := by
  have hε : 0 < ε := ha.trans_le haε
  have ht : 0 ≤ buresSquaredRadius (σ := σ) (κ := κ) ε := by
    unfold buresSquaredRadius
    positivity
  calc
    _ ≤ TailGeometry.matrixLebesgue
        (frobeniusBall (buresSquaredRadius (σ := σ) (κ := κ) ε) : Set (Matrix σ κ ℂ)) :=
      scalar_body_volume_le_ball ha haε
    _ = _ := BV.squared_ball _ ht

/-- Composition interface for the separately proved symmetrization theorem.
`hcomparison` is an ordinary local theorem hypothesis to be discharged by
Lemma 2.3; it is not introduced as an external input or as an axiom. -/
theorem body_volume_le_formula_of_scalar_comparison [Nonempty σ]
    (BV : EuclideanBallVolumeInput σ κ) (A : Matrix σ σ ℂ)
    {a ε : ℝ} (ha : 0 < a) (haε : a ≤ ε)
    (hcomparison : TailGeometry.matrixLebesgue {Z : Matrix σ κ ℂ |
        TailConvexity.H A Z ≤ 9 * (Fintype.card κ : ℝ) ^ 2 * ε} ≤
      TailGeometry.matrixLebesgue {Z : Matrix σ κ ℂ |
        TailConvexity.H (scalarA a) Z ≤ 9 * (Fintype.card κ : ℝ) ^ 2 * ε}) :
    TailGeometry.matrixLebesgue {Z : Matrix σ κ ℂ |
        TailConvexity.H A Z ≤ 9 * (Fintype.card κ : ℝ) ^ 2 * ε} ≤
      ENNReal.ofReal (euclideanBallVolume (σ := σ) (κ := κ)
        (buresSquaredRadius (σ := σ) (κ := κ) ε)) := by
  exact hcomparison.trans (scalar_body_volume_le_formula BV ha haε)

end Paper26.ScalarTailBall
