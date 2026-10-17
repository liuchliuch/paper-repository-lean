import Paper26.Normalization
import Paper26.EnergyReality
import Mathlib.Tactic.Module

/-!
# The loss-specific convexity step of Lemma 2.3

All objects are finite complex matrices.  `Q A Y` is precisely
`Re Tr[Y J_A^{-1}(Y)]`, with the actual inverse-Jordan operator from
`Normalization`; `H A Z = Q A (Z Zᴴ)` for rectangular complex `Z`.

The matrix-fractional variational identity and joint convexity of `Q` are
proved here by completing the square.  The sole external input is the
classical Lyapunov positivity theorem, in its fully quantified equation
form: if `A > 0`, `B >= 0`, and `A X + X A = B`, then `X >= 0`.
This follows from `X = integral_0^infinity exp(-tA) B exp(-tA) dt`.
Reference: S. Boyd, EE363, Lecture 11, "Linear quadratic Lyapunov theory",
section "The Lyapunov operator and integral", slide 11–9 (Stanford course notes):
https://web.stanford.edu/class/ee363/lectures/allslides.pdf .
The cited slide states the real stable-matrix formula
`P = integral_0^infinity exp(t Mᵀ) B exp(t M) dt`, solving
`Mᵀ P + P M = -B`.  The exact field below is the standard complex
Hermitian specialization `M = -A`; the integral uses adjoints and every
integrand is PSD.  Its complete finite-dimensional hypotheses and
quantifiers are retained explicitly in `solution_psd`.
No convexity of `H`, no loss-specific volume bound, and no conclusion of
Lemma 2.3 is included in the external field.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace Paper26.TailConvexity

open Normalization

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Real convex mixing, with the same convention for square and rectangular matrices. -/
def mix {m n : Type*} (t : ℝ) (X Y : Matrix m n ℂ) : Matrix m n ℂ :=
  (1 - t) • X + t • Y

/-- Real trace pairing; Hermitian inputs recover the full (real) complex trace. -/
def pairing (X Y : Matrix ι ι ℂ) : ℝ := (Matrix.trace (X * Y)).re

/-- The quadratic form in Equation (18). -/
def Q (A Y : Matrix ι ι ℂ) : ℝ := pairing Y (jordanInverse A Y)

/-- The tail quartic form from Lemma 2.3. -/
def H (A : Matrix ι ι ℂ) (Z : Matrix ι κ ℂ) : ℝ := Q A (Z * Zᴴ)

/-- Exact generic Lyapunov positivity input.  This is a parameter, not an axiom. -/
structure LyapunovPositivityInput (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop where
  solution_psd : ∀ (A B X : Matrix ι ι ℂ), A.PosDef → B.PosSemidef →
    A * X + X * A = B → X.PosSemidef

lemma pairing_add_left (X Y Z : Matrix ι ι ℂ) :
    pairing (X + Y) Z = pairing X Z + pairing Y Z := by
  simp [pairing, Matrix.add_mul, Matrix.trace_add]

lemma pairing_add_right (X Y Z : Matrix ι ι ℂ) :
    pairing X (Y + Z) = pairing X Y + pairing X Z := by
  simp [pairing, Matrix.mul_add, Matrix.trace_add]

lemma pairing_sub_right (X Y Z : Matrix ι ι ℂ) :
    pairing X (Y - Z) = pairing X Y - pairing X Z := by
  simp [pairing, Matrix.mul_sub, Matrix.trace_sub]

lemma pairing_smul_left (c : ℝ) (X Y : Matrix ι ι ℂ) :
    pairing (c • X) Y = c * pairing X Y := by
  simp [pairing, Matrix.smul_mul, Matrix.trace_smul]

lemma pairing_mix_left (t : ℝ) (X Y Z : Matrix ι ι ℂ) :
    pairing (mix t X Y) Z = (1 - t) * pairing X Z + t * pairing Y Z := by
  simp only [mix, pairing_add_left, pairing_smul_left]

lemma pairing_mul_assoc (X Y Z : Matrix ι ι ℂ) :
    pairing (X * Y) Z = pairing X (Y * Z) := by
  simp only [pairing, Matrix.mul_assoc]

lemma pairing_cycle (X Y Z : Matrix ι ι ℂ) :
    pairing (X * Y) Z = pairing Y (Z * X) := by
  unfold pairing
  congr 1
  calc
    Matrix.trace (X * Y * Z) = Matrix.trace (Z * X * Y) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (Y * Z * X) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (Y * (Z * X)) := by rw [Matrix.mul_assoc]

/-- The real trace of a product of two PSD complex matrices is nonnegative. -/
theorem pairing_nonneg_psd (X Y : Matrix ι ι ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : 0 ≤ pairing X Y := by
  let U : Matrix ι ι ℂ := hX.1.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (hX.1.eigenvalues i : ℂ))
  let F := Uᴴ * Y * U
  have hF : F.PosSemidef := hY.conjTranspose_mul_mul_same U
  have hdiag (i : ι) : 0 ≤ (F i i).re := by
    simpa only [← Pi.single_star, star_one, Matrix.mulVec_single_one,
      single_dotProduct, one_mul, Matrix.col_apply] using
      hF.re_dotProduct_nonneg (Pi.single i 1)
  have hdecomp : X = U * D * Uᴴ := by
    simpa only [U, D, Function.comp_def, Matrix.star_eq_conjTranspose] using
      hX.1.spectral_theorem
  have htrace : Matrix.trace (X * Y) = Matrix.trace (D * F) := by
    calc
      _ = Matrix.trace (U * D * (Uᴴ * Y)) := by
        rw [hdecomp]; simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Uᴴ * Y * U * D) := Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace (D * F) := Matrix.trace_mul_comm _ _
  unfold pairing
  rw [htrace]
  simp only [D, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hX.eigenvalues_nonneg i) (hdiag i)

/-- `Tr[A K²]` is nonnegative whenever `A >= 0` and `K` is Hermitian. -/
lemma quadratic_nonneg (A K : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hK : K.IsHermitian) : 0 ≤ pairing A (K * K) := by
  have hKK : (K * K).PosSemidef := by
    simpa only [hK.eq] using Matrix.posSemidef_conjTranspose_mul_self K
  exact pairing_nonneg_psd A _ hA hKK

/-- Linear structure follows from the unique inverse-Jordan equation. -/
lemma jordanInverse_add (A X Y : Matrix ι ι ℂ) (hA : A.PosDef) :
    jordanInverse A (X + Y) = jordanInverse A X + jordanInverse A Y := by
  symm
  apply jordanInverse_unique_posDef A (X + Y) _ hA
  calc
    A * (jordanInverse A X + jordanInverse A Y) +
        (jordanInverse A X + jordanInverse A Y) * A =
      (A * jordanInverse A X + jordanInverse A X * A) +
        (A * jordanInverse A Y + jordanInverse A Y * A) := by
      simp only [Matrix.mul_add, Matrix.add_mul]; module
    _ = (2 : ℂ) • (X + Y) := by
      rw [jordanInverse_equation_posDef A X hA, jordanInverse_equation_posDef A Y hA]
      module

/-- The cross term obtained from the actual Lyapunov equation. -/
lemma jordan_pairing_identity (A Y K : Matrix ι ι ℂ) (hA : A.PosDef) :
    2 * pairing Y K =
      pairing A (jordanInverse A Y * K) + pairing A (K * jordanInverse A Y) := by
  have h := congrArg (fun M : Matrix ι ι ℂ => pairing M K)
    (jordanInverse_equation_posDef A Y hA)
  dsimp only at h
  rw [pairing_add_left, pairing_mul_assoc, pairing_cycle] at h
  simpa [pairing, Matrix.smul_mul, Matrix.trace_smul] using h.symm

lemma Q_eq_quadratic (A Y : Matrix ι ι ℂ) (hA : A.PosDef) :
    Q A Y = pairing A (jordanInverse A Y * jordanInverse A Y) := by
  have h := jordan_pairing_identity A Y (jordanInverse A Y) hA
  unfold Q
  linarith

lemma quadratic_sub (A X Y : Matrix ι ι ℂ) :
    pairing A ((X - Y) * (X - Y)) =
      pairing A (X * X) + pairing A (Y * Y) -
        pairing A (X * Y) - pairing A (Y * X) := by
  simp [Matrix.sub_mul, Matrix.mul_sub, pairing_sub_right]
  ring

/-- Completion of the square underlying the paper's variational identity (18). -/
lemma variational_defect (A Y K : Matrix ι ι ℂ) (hA : A.PosDef) :
    pairing A ((jordanInverse A Y - K) * (jordanInverse A Y - K)) =
      Q A Y - (2 * pairing Y K - pairing A (K * K)) := by
  rw [quadratic_sub, ← Q_eq_quadratic A Y hA]
  have h := jordan_pairing_identity A Y K hA
  linarith

/-- Every Hermitian test matrix gives the upper bound in Equation (18). -/
theorem variational_upper (A Y K : Matrix ι ι ℂ) (hA : A.PosDef)
    (hY : Y.IsHermitian) (hK : K.IsHermitian) :
    2 * pairing Y K - pairing A (K * K) ≤ Q A Y := by
  have hJ : (jordanInverse A Y).IsHermitian :=
    EnergyReality.jordanInverse_hermitian A Y hA hY.eq
  have hn := quadratic_nonneg A (jordanInverse A Y - K) hA.posSemidef (hJ.sub hK)
  rw [variational_defect A Y K hA] at hn
  linarith

/-- The test matrix `J_A^{-1}(Y)` attains the variational upper bound. -/
theorem variational_attained (A Y : Matrix ι ι ℂ) (hA : A.PosDef) :
    2 * pairing Y (jordanInverse A Y) -
      pairing A (jordanInverse A Y * jordanInverse A Y) = Q A Y := by
  rw [← Q_eq_quadratic A Y hA]
  unfold Q
  ring

lemma mix_posDef (A B : Matrix ι ι ℂ) (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : (mix t A B).PosDef := by
  by_cases h0 : t = 0
  · simpa [mix, h0] using hA
  by_cases h1 : t = 1
  · simpa [mix, h1] using hB
  have htl : t < 1 := lt_of_le_of_ne ht1 h1
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm h0)
  exact (hA.smul (sub_pos.mpr htl)).add (hB.smul htp)

lemma mix_hermitian (X Y : Matrix ι ι ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (t : ℝ) : (mix t X Y).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [mix, Matrix.smul_apply, hX.apply i j, hY.apply i j]

/-- Joint convexity of the matrix-fractional form is proved, rather than supplied
as a loss-specific external assumption. -/
theorem Q_jointConvex (A B X Y : Matrix ι ι ℂ)
    (hA : A.PosDef) (hB : B.PosDef) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Q (mix t A B) (mix t X Y) ≤ (1 - t) * Q A X + t * Q B Y := by
  let K := jordanInverse (mix t A B) (mix t X Y)
  have hAB := mix_posDef A B hA hB ht ht1
  have hK : K.IsHermitian := EnergyReality.jordanInverse_hermitian _ _ hAB
    (mix_hermitian X Y hX hY t).eq
  have h₀ := variational_upper A X K hA hX hK
  have h₁ := variational_upper B Y K hB hY hK
  calc
    Q (mix t A B) (mix t X Y) =
      2 * pairing (mix t X Y) K - pairing (mix t A B) (K * K) :=
        (variational_attained _ _ hAB).symm
    _ = (1 - t) * (2 * pairing X K - pairing A (K * K)) +
        t * (2 * pairing Y K - pairing B (K * K)) := by
      rw [pairing_mix_left, pairing_mix_left]; ring
    _ ≤ (1 - t) * Q A X + t * Q B Y :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ (by linarith))
        (mul_le_mul_of_nonneg_left h₁ ht)

/-- Positivity of the Jordan inverse is the exact specialization of the generic
external Lyapunov theorem to right-hand side `2Y`. -/
theorem jordanInverse_psd (L : LyapunovPositivityInput ι)
    (A Y : Matrix ι ι ℂ) (hA : A.PosDef) (hY : Y.PosSemidef) :
    (jordanInverse A Y).PosSemidef := by
  apply L.solution_psd A ((2 : ℂ) • Y) (jordanInverse A Y) hA
  · exact hY.smul (by norm_num : (0 : ℂ) ≤ 2)
  · exact jordanInverse_equation_posDef A Y hA

lemma Q_add_expansion (A Y D : Matrix ι ι ℂ) (hA : A.PosDef) :
    Q A (Y + D) = Q A Y + Q A D +
      pairing Y (jordanInverse A D) + pairing D (jordanInverse A Y) := by
  unfold Q
  rw [jordanInverse_add A Y D hA, pairing_add_left,
    pairing_add_right, pairing_add_right]
  ring

/-- The required PSD-order monotonicity follows from quadratic expansion and
positivity of the inverse, without assuming the desired quartic convexity. -/
theorem Q_mono_psd (L : LyapunovPositivityInput ι)
    (A Y D : Matrix ι ι ℂ) (hA : A.PosDef)
    (hY : Y.PosSemidef) (hD : D.PosSemidef) : Q A Y ≤ Q A (Y + D) := by
  have hJY := jordanInverse_psd L A Y hA hY
  have hJD := jordanInverse_psd L A D hA hD
  have hq : 0 ≤ Q A D := pairing_nonneg_psd D _ hD hJD
  have hcross₀ := pairing_nonneg_psd Y _ hY hJD
  have hcross₁ := pairing_nonneg_psd D _ hD hJY
  rw [Q_add_expansion A Y D hA]
  linarith

/-- The exact Loewner Jensen defect of the rectangular matrix Gram map. -/
theorem gram_mix_defect (Z W : Matrix ι κ ℂ) (t : ℝ) :
    mix t (Z * Zᴴ) (W * Wᴴ) - mix t Z W * (mix t Z W)ᴴ =
      (t * (1 - t)) • ((Z - W) * (Z - W)ᴴ) := by
  simp only [mix, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, star_trivial, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  module

/-- `Z ↦ ZZᴴ` is convex in PSD order, including both endpoints of `[0,1]`. -/
theorem gram_mix_psd (Z W : Matrix ι κ ℂ) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (mix t (Z * Zᴴ) (W * Wᴴ) - mix t Z W * (mix t Z W)ᴴ).PosSemidef := by
  rw [gram_mix_defect]
  exact (Matrix.posSemidef_self_mul_conjTranspose (Z - W)).smul
    (mul_nonneg ht (by linarith) : 0 ≤ t * (1 - t))

/-- The loss-specific core of Lemma 2.3: genuine joint convexity in `(A,Z)`. -/
theorem H_jointConvex (L : LyapunovPositivityInput ι)
    (A B : Matrix ι ι ℂ) (Z W : Matrix ι κ ℂ)
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    H (mix t A B) (mix t Z W) ≤ (1 - t) * H A Z + t * H B W := by
  let Y := mix t Z W * (mix t Z W)ᴴ
  let D := mix t (Z * Zᴴ) (W * Wᴴ) - Y
  have hY : Y.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose _
  have hD : D.PosSemidef := gram_mix_psd Z W ht ht1
  have hm := Q_mono_psd L (mix t A B) Y D (mix_posDef A B hA hB ht ht1) hY hD
  have he : Y + D = mix t (Z * Zᴴ) (W * Wᴴ) := by dsimp [D]; module
  rw [he] at hm
  exact hm.trans (Q_jointConvex A B _ _ hA hB
    (Matrix.posSemidef_self_mul_conjTranspose Z).1
    (Matrix.posSemidef_self_mul_conjTranspose W).1 ht ht1)

end Paper26.TailConvexity

namespace Paper26.TailConvexity

open Normalization
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- A unitary change of basis preserves positive definiteness. -/
theorem conjugate_posDef (U A : Matrix ι ι ℂ) (hU : U * Uᴴ = 1)
    (hA : A.PosDef) : (conjugate U A).PosDef := by
  apply hA.mul_mul_conjTranspose_same
  intro x y hxy
  have h := congrArg (fun v => Matrix.vecMul v Uᴴ) hxy
  simpa only [Matrix.vecMul_vecMul, hU, Matrix.vecMul_one] using h

/-- The intrinsic inverse-Jordan operator is equivariant under unitary conjugation. -/
theorem jordanInverse_conjugate (U A X : Matrix ι ι ℂ)
    (hU₁ : Uᴴ * U = 1) (hU₂ : U * Uᴴ = 1) (hA : A.PosDef) :
    jordanInverse (conjugate U A) (conjugate U X) = conjugate U (jordanInverse A X) := by
  symm
  apply jordanInverse_unique_posDef (conjugate U A) (conjugate U X) _
    (conjugate_posDef U A hU₂ hA)
  have h := congrArg (conjugate U) (jordanInverse_equation_posDef A X hA)
  rw [conjugate_add, conjugate_mul U _ _ hU₁, conjugate_mul U _ _ hU₁,
    conjugate_smul] at h
  exact h

/-- Unitary invariance of the actual matrix-fractional quadratic form. -/
theorem Q_conjugate (U A Y : Matrix ι ι ℂ)
    (hU₁ : Uᴴ * U = 1) (hU₂ : U * Uᴴ = 1) (hA : A.PosDef) :
    Q (conjugate U A) (conjugate U Y) = Q A Y := by
  unfold Q pairing
  rw [jordanInverse_conjugate U A Y hU₁ hU₂ hA,
    ← conjugate_mul U _ _ hU₁, trace_conjugate U _ hU₁]

/-- The quartic tail form is unchanged by rotating both `A` and the rows of `Z`. -/
theorem H_unitary (U A : Matrix ι ι ℂ) (Z : Matrix ι κ ℂ)
    (hU₁ : Uᴴ * U = 1) (hU₂ : U * Uᴴ = 1) (hA : A.PosDef) :
    H (conjugate U A) (U * Z) = H A Z := by
  have he : U * Z * (U * Z)ᴴ = conjugate U (Z * Zᴴ) := by
    simp only [Matrix.conjTranspose_mul, conjugate, Matrix.mul_assoc]
  unfold H
  rw [he, Q_conjugate U A _ hU₁ hU₂ hA]

end Paper26.TailConvexity
