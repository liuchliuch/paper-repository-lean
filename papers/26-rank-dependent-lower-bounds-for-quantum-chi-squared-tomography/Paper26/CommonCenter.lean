import Paper26.PositiveLossBridge
import Paper26.Variational
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Data.ENNReal.Inv
import Mathlib.Analysis.Matrix.Order

/-!
# Actual principal-angle blocks for Proposition B.1

The canonical projectors below are genuine self-adjoint idempotent complex
matrices on `Fin 2 × ι`. Their sum has the principal-angle spectrum `1 ± cᵢ`.
All square-root and center calculations refer to these matrices.

The square-root trace and trace-norm identities allow zero angles. The attained
minimax and arithmetic-mean results cover strictly positive angles on the full
`2r`-dimensional space and all density outputs, including singular outputs.
`StrictPrincipalAngleForm` transports them using only raw unitary block data.
The support-compression step needed for zero angles or an ambient orthogonal
complement is not asserted in this module.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal MatrixOrder

namespace Paper26.CommonCenter

open QuantumModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A rank-one principal-angle block in the bisector basis. -/
def angleBlock (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1 + c) / 2 : ℝ), (s / 2 : ℝ); (s / 2 : ℝ), ((1 - c) / 2 : ℝ)]

lemma angleBlock_hermitian (c s : ℝ) : (angleBlock c s).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [angleBlock, Matrix.conjTranspose_apply]

lemma angleBlock_idempotent {c s : ℝ} (hcircle : c ^ 2 + s ^ 2 = 1) :
    angleBlock c s * angleBlock c s = angleBlock c s := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [angleBlock, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] <;> nlinarith [hcircle]

@[simp] lemma angleBlock_trace (c s : ℝ) : Matrix.trace (angleBlock c s) = 1 := by
  simp [Matrix.trace, Fin.sum_univ_two, angleBlock]
  ring

/-- The first actual rank-r projector in canonical principal-angle coordinates. -/
def canonicalP (c s : ι → ℝ) (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1) :
    OrthogonalProjector (Fin 2 × ι) where
  matrix := Matrix.blockDiagonal fun i => angleBlock (c i) (s i)
  hermitian := by
    rw [Matrix.IsHermitian, Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext i
    exact (angleBlock_hermitian (c i) (s i)).eq
  idempotent := by
    rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext i
    exact angleBlock_idempotent (hcircle i)

/-- The second projector changes only the signs of the two cross entries. -/
def canonicalQ (c s : ι → ℝ) (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1) :
    OrthogonalProjector (Fin 2 × ι) :=
  canonicalP c (fun i => -s i) (fun i => by nlinarith [hcircle i])

@[simp] theorem canonicalP_trace (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1) :
    Matrix.trace (canonicalP c s hcircle).matrix = (Fintype.card ι : ℂ) := by
  simp [canonicalP, Matrix.trace_blockDiagonal]

@[simp] theorem canonicalP_rank (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1) :
    (canonicalP c s hcircle).matrix.rank = Fintype.card ι := by
  have h := (canonicalP c s hcircle).trace_eq_rank
  rw [canonicalP_trace] at h
  exact_mod_cast h.symm

@[simp] theorem canonicalQ_rank (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1) :
    (canonicalQ c s hcircle).matrix.rank = Fintype.card ι := by
  exact canonicalP_rank _ _ _

/-- The two eigenvalues of `P+Q` in each actual two-dimensional block. -/
def pairSpectrum (c : ι → ℝ) (p : Fin 2 × ι) : ℝ :=
  (![1 + c p.2, 1 - c p.2] : Fin 2 → ℝ) p.1

lemma angleBlock_add_flip (c s : ℝ) :
    angleBlock c s + angleBlock c (-s) =
      Matrix.diagonal (fun k => ((![1 + c, 1 - c] : Fin 2 → ℝ) k : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [angleBlock, Matrix.diagonal] <;>
    ring

/-- The actual sum, rather than an asserted eigenvalue list, is diagonal. -/
theorem canonical_sum_diagonal (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1) :
    (canonicalP c s hcircle).matrix + (canonicalQ c s hcircle).matrix =
      Normalization.diagonalMatrix (pairSpectrum c) := by
  change Matrix.blockDiagonal (fun i => angleBlock (c i) (s i)) +
    Matrix.blockDiagonal (fun i => angleBlock (c i) (-s i)) = _
  rw [← Matrix.blockDiagonal_add]
  change Matrix.blockDiagonal (fun i => angleBlock (c i) (s i) +
    angleBlock (c i) (-s i)) = _
  have hb : (fun i => angleBlock (c i) (s i) + angleBlock (c i) (-s i)) =
      fun i => Matrix.diagonal
        (fun k => ((![1 + c i, 1 - c i] : Fin 2 → ℝ) k : ℂ)) := by
    funext i
    exact angleBlock_add_flip _ _
  rw [hb, Matrix.blockDiagonal_diagonal]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma pairSpectrum_nonneg (c : ι → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (p : Fin 2 × ι) : 0 ≤ pairSpectrum c p := by
  rcases p with ⟨k, i⟩
  fin_cases k <;> simp [pairSpectrum] <;> linarith [hc0 i, hc1 i]

omit [Fintype ι] [DecidableEq ι] in
lemma pairSpectrum_pos (c : ι → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1)
    (p : Fin 2 × ι) : 0 < pairSpectrum c p := by
  rcases p with ⟨k, i⟩
  fin_cases k <;> simp [pairSpectrum] <;> linarith [hc0 i, hc1 i]

/-- An explicit positive-semidefinite square-root matrix of `P+Q`. -/
def sqrtSum (c : ι → ℝ) : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ :=
  Normalization.diagonalMatrix fun p => Real.sqrt (pairSpectrum c p)

theorem sqrtSum_posSemidef (c : ι → ℝ) : (sqrtSum c).PosSemidef :=
  Matrix.PosSemidef.diagonal (fun _p => RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _))

theorem sqrtSum_square (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) :
    sqrtSum c * sqrtSum c =
      (canonicalP c s hcircle).matrix + (canonicalQ c s hcircle).matrix := by
  rw [canonical_sum_diagonal]
  unfold sqrtSum Normalization.diagonalMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  have h := Real.mul_self_sqrt (pairSpectrum_nonneg c hc0 hc1 p)
  exact_mod_cast h

/-- The principal-angle square-root identity, including zero angles. -/
lemma root_pair_identity {c s : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hs0 : 0 ≤ s) (hcircle : c ^ 2 + s ^ 2 = 1) :
    Real.sqrt (1 + c) + Real.sqrt (1 - c) =
      Real.sqrt 2 * Real.sqrt (1 + s) := by
  have hp := Real.sqrt_nonneg (1 + c)
  have hm := Real.sqrt_nonneg (1 - c)
  have hp2 := Real.sq_sqrt (show 0 ≤ 1 + c by linarith)
  have hm2 := Real.sq_sqrt (show 0 ≤ 1 - c by linarith)
  have hprod : Real.sqrt (1 + c) * Real.sqrt (1 - c) = s := by
    have hsquare : (Real.sqrt (1 + c) * Real.sqrt (1 - c)) ^ 2 = s ^ 2 := by
      rw [mul_pow, hp2, hm2]
      nlinarith [hcircle]
    exact (sq_eq_sq₀ (mul_nonneg hp hm) hs0).mp hsquare
  have htwo := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsroot := Real.sq_sqrt (show 0 ≤ 1 + s by linarith)
  apply (sq_eq_sq₀ (add_nonneg hp hm) (by positivity :
    0 ≤ Real.sqrt 2 * Real.sqrt (1 + s))).mp
  rw [mul_pow, htwo, hsroot]
  nlinarith

/-- The true trace of the positive square-root matrix equals the source's
principal-angle expression. -/
theorem sqrtSum_trace (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) (hs0 : ∀ i, 0 ≤ s i) :
    (Matrix.trace (sqrtSum c)).re =
      Real.sqrt 2 * ∑ i, Real.sqrt (1 + s i) := by
  simp only [sqrtSum, Normalization.diagonalMatrix, Matrix.trace_diagonal, Fintype.sum_prod_type, Fin.sum_univ_two, pairSpectrum,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Complex.re_sum, Complex.add_re, Complex.ofReal_re]
  apply Finset.sum_congr rfl
  intro i _
  exact root_pair_identity (hc0 i) (hc1 i) (hs0 i) (hcircle i)

omit [DecidableEq ι] in
/-- The chord estimate is retained in its principal-angle scalar form, ready
to combine with the actual trace-norm computation. -/
theorem principal_radius_chord (s : ι → ℝ) (hs0 : ∀ i, 0 ≤ s i)
    (hs1 : ∀ i, s i ≤ 1) (hr : 0 < (Fintype.card ι : ℝ)) :
    (2 * (Real.sqrt 2 - 1)) * ((∑ i, s i) / Fintype.card ι) ≤
      ((∑ i, Real.sqrt (1 + s i)) / Fintype.card ι) ^ 2 - 1 :=
  Variational.common_center_scalar_lower s hs0 hs1 hr


/-- Actual inverse-weighted linear matrix risk. -/
def inverseRisk (M A : Matrix ι ι ℂ) : ℝ := (Matrix.trace (M * A⁻¹)).re

lemma inverseRisk_add (M N A : Matrix ι ι ℂ) :
    inverseRisk (M + N) A = inverseRisk M A + inverseRisk N A := by
  simp [inverseRisk, Matrix.add_mul, Matrix.trace_add]

lemma inverseRisk_real_smul (b : ℝ) (M A : Matrix ι ι ℂ) :
    inverseRisk (b • M) A = b * inverseRisk M A := by
  simp [inverseRisk, Matrix.trace_smul, Complex.real_smul,
    Complex.mul_re]

/-- Nonnegativity of the actual inverse-weighted Hermitian square. -/
lemma inverseRisk_square_nonneg (X A : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hA : A.PosDef) : 0 ≤ inverseRisk (X * X) A := by
  obtain ⟨U, a, hU₁, hU₂, ha, heq⟩ :=
    Normalization.exists_positive_spectral_representation A hA
  have hh : (X + A).IsHermitian := hX.add hA.1
  have hs := PositiveLossBridge.standardRightEnergy_spectral U (X + A) a hU₁ hU₂ hh ha
  rw [← heq] at hs
  have hn : 0 ≤ Normalization.standardRightEnergy (X + A) A := by
    rw [hs]
    exact SpectralLoss.rightInverse_nonneg ha _
  simpa only [Normalization.standardRightEnergy, inverseRisk,
    add_sub_cancel_right] using hn

/-- Completing the matrix square before taking the actual trace. The matrix
`S` need not commute with the density estimate `A`. -/
lemma inverseRisk_square_expansion (S A : Matrix ι ι ℂ)
    (hA : A.PosDef) (htrace : Matrix.trace A = 1) (t : ℝ) :
    inverseRisk ((S - (t : ℂ) • A) * (S - (t : ℂ) • A)) A =
      inverseRisk (S * S) A - 2 * t * (Matrix.trace S).re + t ^ 2 := by
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hright : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hd
  have hleft : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hd
  have hc1 : Matrix.trace (S * A * A⁻¹) = Matrix.trace S := by
    rw [Matrix.mul_assoc, hright, Matrix.mul_one]
  have hc2 : Matrix.trace (A * S * A⁻¹) = Matrix.trace S := by
    rw [Matrix.trace_mul_cycle, hleft, Matrix.one_mul]
  have hc3 : Matrix.trace (A * A * A⁻¹) = 1 := by
    rw [Matrix.mul_assoc, hright, Matrix.mul_one, htrace]
  have he : (S - (t : ℂ) • A) * (S - (t : ℂ) • A) * A⁻¹ =
      S * S * A⁻¹ - (S * ((t : ℂ) • A)) * A⁻¹ -
        (((t : ℂ) • A) * S) * A⁻¹ +
          (((t : ℂ) • A) * ((t : ℂ) • A)) * A⁻¹ := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  unfold inverseRisk
  rw [he]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, hc1, hc2, hc3, smul_eq_mul,
    Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    mul_zero, zero_mul, sub_zero]
  ring

/-- Matrix Cauchy--Schwarz for the common-center problem, proved internally by
completing the inverse-weighted square. It covers arbitrary noncommuting
positive density outputs. -/
theorem inverseRisk_lower (S A : Matrix ι ι ℂ) (hS : S.IsHermitian)
    (hA : A.PosDef) (htrace : Matrix.trace A = 1) :
    (Matrix.trace S).re ^ 2 ≤ inverseRisk (S * S) A := by
  let t := (Matrix.trace S).re
  have hX : (S - (t : ℂ) • A).IsHermitian := by
    change (S - (t : ℂ) • A)ᴴ = S - (t : ℂ) • A
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hS.eq, hA.1.eq]
  have hn := inverseRisk_square_nonneg (S - (t : ℂ) • A) A hX hA
  rw [inverseRisk_square_expansion S A hA htrace t] at hn
  dsimp [t] at hn
  nlinarith

/-- Expansion of the actual right-inverse error for two normalized density
matrices. The output inverse is the actual nonsingular matrix inverse. -/
theorem standardRightEnergy_expansion (ρ σ : Density ι) (hσ : σ.matrix.PosDef) :
    Normalization.standardRightEnergy ρ.matrix σ.matrix =
      inverseRisk (ρ.matrix * ρ.matrix) σ.matrix - 1 := by
  have h := inverseRisk_square_expansion ρ.matrix σ.matrix hσ σ.trace_one 1
  simp [inverseRisk, ρ.trace_one] at h
  unfold Normalization.standardRightEnergy inverseRisk
  linarith


omit [DecidableEq ι] in
lemma posDef_trace_re_pos [Nonempty ι] (S : Matrix ι ι ℂ) (hS : S.PosDef) :
    0 < (Matrix.trace S).re :=
  (Complex.pos_iff.mp hS.trace_pos).1

/-- Normalizing an actual positive square-root matrix constructs a genuine
positive density matrix, without an optimality hypothesis. -/
def squareRootCenter [Nonempty ι] (S : Matrix ι ι ℂ) (hS : S.PosDef) : Density ι where
  matrix := (((1 / (Matrix.trace S).re : ℝ) : ℂ)) • S
  positive := hS.posSemidef.smul (RCLike.ofReal_nonneg.mpr
    (one_div_pos.mpr (posDef_trace_re_pos S hS)).le)
  trace_one := by
    rw [Matrix.trace_smul]
    change (((1 / (Matrix.trace S).re : ℝ) : ℂ)) * Matrix.trace S = 1
    rw [← Normalization.posDef_trace_real S hS, Complex.ofReal_re, ← Complex.ofReal_mul,
      one_div_mul_cancel (ne_of_gt (posDef_trace_re_pos S hS)), Complex.ofReal_one]

lemma squareRootCenter_posDef [Nonempty ι] (S : Matrix ι ι ℂ) (hS : S.PosDef) :
    (squareRootCenter S hS).matrix.PosDef :=
  hS.smul (RCLike.ofReal_pos.mpr (one_div_pos.mpr (posDef_trace_re_pos S hS)))

lemma squareRootCenter_inverse [Nonempty ι] (S : Matrix ι ι ℂ) (hS : S.PosDef) :
    (squareRootCenter S hS).matrix⁻¹ = ((Matrix.trace S).re : ℂ) • S⁻¹ := by
  have hd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have ht := posDef_trace_re_pos S hS
  apply Matrix.inv_eq_right_inv
  change ((((1 / (Matrix.trace S).re : ℝ) : ℂ)) • S) *
    (((Matrix.trace S).re : ℂ) • S⁻¹) = 1
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv S hd]
  have hc : (((1 / (Matrix.trace S).re : ℝ) : ℂ)) * ((Matrix.trace S).re : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, one_div_mul_cancel (ne_of_gt ht), Complex.ofReal_one]
  rw [hc, one_smul]

/-- The normalized square root attains the matrix Cauchy lower bound. -/
theorem inverseRisk_center [Nonempty ι] (S : Matrix ι ι ℂ) (hS : S.PosDef) :
    inverseRisk (S * S) (squareRootCenter S hS).matrix = (Matrix.trace S).re ^ 2 := by
  have hd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  unfold inverseRisk
  rw [squareRootCenter_inverse, Matrix.mul_smul, Matrix.trace_smul]
  have hs : S * S * S⁻¹ = S := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv S hd, Matrix.mul_one]
  rw [hs]
  simp [smul_eq_mul, Complex.mul_re, pow_two]

/-- Full matrix minimization among arbitrary positive density outputs. -/
theorem inverseRisk_center_minimizer [Nonempty ι] (S : Matrix ι ι ℂ) (hS : S.PosDef) :
    (squareRootCenter S hS).matrix.PosDef ∧
      inverseRisk (S * S) (squareRootCenter S hS).matrix = (Matrix.trace S).re ^ 2 ∧
      ∀ A : Density ι, A.matrix.PosDef →
        inverseRisk (S * S) (squareRootCenter S hS).matrix ≤
          inverseRisk (S * S) A.matrix := by
  refine ⟨squareRootCenter_posDef S hS, inverseRisk_center S hS, ?_⟩
  intro A hA
  rw [inverseRisk_center]
  exact inverseRisk_lower S A.matrix hS.1 hA A.trace_one

lemma flat_square (P : OrthogonalProjector ι) (hr : 0 < P.matrix.rank) :
    (P.flat hr).matrix * (P.flat hr).matrix =
      (((P.matrix.rank : ℝ)⁻¹) ^ 2) • P.matrix := by
  change (((P.matrix.rank : ℝ)⁻¹) • P.matrix) *
      (((P.matrix.rank : ℝ)⁻¹) • P.matrix) = _
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, P.idempotent, pow_two]

lemma flat_loss_formula (P : OrthogonalProjector ι) (hr : 0 < P.matrix.rank)
    (A : Density ι) (hA : A.matrix.PosDef) :
    Normalization.standardRightEnergy (P.flat hr).matrix A.matrix =
      (((P.matrix.rank : ℝ)⁻¹) ^ 2) * inverseRisk P.matrix A.matrix - 1 := by
  rw [standardRightEnergy_expansion (P.flat hr) A hA, flat_square,
    inverseRisk_real_smul]

def stateP [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1) : Density (Fin 2 × ι) :=
  (canonicalP c s hcircle).flat (by rw [canonicalP_rank]; exact Fintype.card_pos)

def stateQ [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1) : Density (Fin 2 × ι) :=
  (canonicalQ c s hcircle).flat (by rw [canonicalQ_rank]; exact Fintype.card_pos)

/-- The actual average right-inverse loss has the source's linear matrix form. -/
theorem canonical_average_formula [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (A : Density (Fin 2 × ι)) (hA : A.matrix.PosDef) :
    ((chiR (stateP c s hcircle) A).toReal + (chiR (stateQ c s hcircle) A).toReal) / 2 =
      (((Fintype.card ι : ℝ)⁻¹) ^ 2 / 2) *
        inverseRisk ((canonicalP c s hcircle).matrix + (canonicalQ c s hcircle).matrix)
          A.matrix - 1 := by
  rw [PositiveLossBridge.chiR_toReal_standard _ _ hA,
    PositiveLossBridge.chiR_toReal_standard _ _ hA]
  unfold stateP stateQ
  rw [flat_loss_formula _ _ A hA, flat_loss_formula _ _ A hA, canonicalP_rank, canonicalQ_rank,
    inverseRisk_add]
  ring

/-- The radius in Equation (52). -/
def principalRadius (s : ι → ℝ) : ℝ :=
  ((∑ i, Real.sqrt (1 + s i)) / Fintype.card ι) ^ 2 - 1

lemma principalRadius_trace_formula [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) (hs0 : ∀ i, 0 ≤ s i) :
    (((Fintype.card ι : ℝ)⁻¹) ^ 2 / 2) * (Matrix.trace (sqrtSum c)).re ^ 2 - 1 =
      principalRadius s := by
  rw [sqrtSum_trace c s hcircle hc0 hc1 hs0, mul_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  unfold principalRadius
  ring

/-- All arbitrary noncommuting positive outputs obey the principal-angle
average-loss lower bound. -/
theorem canonical_average_lower [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) (hs0 : ∀ i, 0 ≤ s i)
    (A : Density (Fin 2 × ι)) (hA : A.matrix.PosDef) :
    principalRadius s ≤
      ((chiR (stateP c s hcircle) A).toReal + (chiR (stateQ c s hcircle) A).toReal) / 2 := by
  have hc := inverseRisk_lower (sqrtSum c) A.matrix (sqrtSum_posSemidef c).1 hA A.trace_one
  rw [sqrtSum_square c s hcircle hc0 hc1] at hc
  have hm := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ ((Fintype.card ι : ℝ)⁻¹) ^ 2 / 2 by positivity)
  rw [canonical_average_formula c s hcircle A hA,
    ← principalRadius_trace_formula c s hcircle hc0 hc1 hs0]
  linarith

/-- Strictly positive principal angles make the canonical square-root matrix
positive definite on the entire `2r`-dimensional space. -/
theorem sqrtSum_posDef (c : ι → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1) :
    (sqrtSum c).PosDef :=
  Matrix.PosDef.diagonal (fun p => RCLike.ofReal_pos.mpr
    (Real.sqrt_pos.mpr (pairSpectrum_pos c hc0 hc1 p)))

def canonicalCenter [Nonempty ι] (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1) : Density (Fin 2 × ι) :=
  squareRootCenter (sqrtSum c) (sqrtSum_posDef c hc0 hc1)

/-- The actual normalized square-root center attains the average lower bound. -/
theorem canonical_center_average [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1) (hs0 : ∀ i, 0 ≤ s i) :
    ((chiR (stateP c s hcircle) (canonicalCenter c hc0 hc1)).toReal +
      (chiR (stateQ c s hcircle) (canonicalCenter c hc0 hc1)).toReal) / 2 =
        principalRadius s := by
  unfold canonicalCenter
  have hA := squareRootCenter_posDef (sqrtSum c) (sqrtSum_posDef c hc0 hc1)
  rw [canonical_average_formula c s hcircle _ hA,
    ← sqrtSum_square c s hcircle hc0 (fun i => (hc1 i).le)]
  rw [inverseRisk_center]
  exact principalRadius_trace_formula c s hcircle hc0 (fun i => (hc1 i).le) hs0

lemma canonical_diagonal_equal (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1) (p : Fin 2 × ι) :
    (canonicalP c s hcircle).matrix p p = (canonicalQ c s hcircle).matrix p p := by
  rcases p with ⟨k, i⟩
  fin_cases k <;> simp [canonicalP, canonicalQ, angleBlock, Matrix.blockDiagonal_apply]

lemma canonical_inverseRisk_equal_of_diagonal (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (A : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (v : Fin 2 × ι → ℂ)
    (hinv : A⁻¹ = Matrix.diagonal v) :
    inverseRisk (canonicalP c s hcircle).matrix A =
      inverseRisk (canonicalQ c s hcircle).matrix A := by
  unfold inverseRisk
  rw [hinv]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [canonical_diagonal_equal c s hcircle p]

lemma canonicalCenter_inverse_diagonal [Nonempty ι] (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1) :
    ∃ v : Fin 2 × ι → ℂ, (canonicalCenter c hc0 hc1).matrix⁻¹ = Matrix.diagonal v := by
  let q : Fin 2 × ι → ℝ := fun p => Real.sqrt (pairSpectrum c p)
  have hq : ∀ p, 0 < q p := fun p => Real.sqrt_pos.mpr (pairSpectrum_pos c hc0 hc1 p)
  have hi := Normalization.conjugate_diagonal_inverse (1 : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ)
    q (by simp) (by simp) hq
  simp only [Normalization.conjugate, Matrix.conjTranspose_one, Matrix.one_mul,
    Matrix.mul_one] at hi
  change (sqrtSum c)⁻¹ = Normalization.diagonalMatrix (fun p => 1 / q p) at hi
  refine ⟨fun p => ((Matrix.trace (sqrtSum c)).re : ℂ) * ((1 / q p : ℝ) : ℂ), ?_⟩
  unfold canonicalCenter
  rw [squareRootCenter_inverse, hi]
  unfold Normalization.diagonalMatrix
  rw [← Matrix.diagonal_smul]
  rfl

/-- At the actual square-root center the two actual quantum losses are equal
and both attain the source's principal-angle value. -/
theorem canonical_center_losses [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1) (hs0 : ∀ i, 0 ≤ s i) :
    chiR (stateP c s hcircle) (canonicalCenter c hc0 hc1) = ENNReal.ofReal (principalRadius s) ∧
      chiR (stateQ c s hcircle) (canonicalCenter c hc0 hc1) = ENNReal.ofReal (principalRadius s) := by
  let A := canonicalCenter c hc0 hc1
  have hA : A.matrix.PosDef := squareRootCenter_posDef _ _
  obtain ⟨v, hv⟩ := canonicalCenter_inverse_diagonal c hc0 hc1
  have heq := canonical_inverseRisk_equal_of_diagonal c s hcircle A.matrix v hv
  have hreal : Normalization.standardRightEnergy (stateP c s hcircle).matrix A.matrix =
      Normalization.standardRightEnergy (stateQ c s hcircle).matrix A.matrix := by
    unfold stateP stateQ
    rw [flat_loss_formula _ _ A hA, flat_loss_formula _ _ A hA, canonicalP_rank, canonicalQ_rank, heq]
  have havg := canonical_center_average c s hcircle hc0 hc1 hs0
  change ((chiR (stateP c s hcircle) A).toReal + (chiR (stateQ c s hcircle) A).toReal) / 2 = _ at havg
  rw [PositiveLossBridge.chiR_toReal_standard _ _ hA,
    PositiveLossBridge.chiR_toReal_standard _ _ hA] at havg
  have hp : Normalization.standardRightEnergy (stateP c s hcircle).matrix A.matrix =
      principalRadius s := by linarith
  have hq : Normalization.standardRightEnergy (stateQ c s hcircle).matrix A.matrix =
      principalRadius s := by linarith
  exact ⟨(PositiveLossBridge.chiR_eq_standardRightEnergy _ _ hA).trans (congrArg ENNReal.ofReal hp),
    (PositiveLossBridge.chiR_eq_standardRightEnergy _ _ hA).trans (congrArg ENNReal.ofReal hq)⟩


/-- A PSD matrix with trivial kernel is strictly positive; proved through its
actual spectral decomposition and nonzero determinant. -/
lemma posDef_of_posSemidef_isUnit (A : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (hu : IsUnit A) : A.PosDef := by
  apply hA.1.posDef_iff_eigenvalues_pos.mpr
  intro i
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hu
  have hp : (∏ j, (hA.1.eigenvalues j : ℂ)) ≠ 0 := by
    have hn := hd.ne_zero
    rw [hA.1.det_eq_prod_eigenvalues] at hn
    exact hn
  have hi : (hA.1.eigenvalues i : ℂ) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  have hir : hA.1.eigenvalues i ≠ 0 := by
    intro hz
    exact hi (by simp [hz])
  exact lt_of_le_of_ne (hA.eigenvalues_nonneg i) hir.symm

lemma flat_kernel (P : OrthogonalProjector ι) (hr : 0 < P.matrix.rank) (v : ι → ℂ) :
    (P.flat hr).matrix *ᵥ v = 0 ↔ P.matrix *ᵥ v = 0 := by
  have hc : ((P.matrix.rank : ℝ)⁻¹) ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt hr))
  change (((P.matrix.rank : ℝ)⁻¹) • P.matrix) *ᵥ v = 0 ↔ _
  rw [Matrix.smul_mulVec]
  simp only [smul_eq_zero, hc, false_or]

/-- If the two projector supports span the full space, a finite common output
must be positive definite. This proves the relevant singular-output exclusion
from the actual support convention, rather than discarding singular outputs. -/
theorem supports_flat_pair_force_posDef (P Q : OrthogonalProjector ι)
    (hrP : 0 < P.matrix.rank) (hrQ : 0 < Q.matrix.rank)
    (hsum : (P.matrix + Q.matrix).PosDef) (A : Density ι)
    (hP : SupportContained (P.flat hrP) A) (hQ : SupportContained (Q.flat hrQ) A) :
    A.matrix.PosDef := by
  apply posDef_of_posSemidef_isUnit A.matrix A.positive
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hz : A.matrix *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  have hp := (flat_kernel P hrP (v - w)).mp (hP (v - w) hz)
  have hq := (flat_kernel Q hrQ (v - w)).mp (hQ (v - w) hz)
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr hsum.isUnit
  have hzero : v - w = 0 := hi (by simp [Matrix.add_mulVec, hp, hq])
  exact sub_eq_zero.mp hzero

lemma canonical_sum_posDef (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1) :
    ((canonicalP c s hcircle).matrix + (canonicalQ c s hcircle).matrix).PosDef := by
  rw [canonical_sum_diagonal]
  exact Matrix.PosDef.diagonal (fun p =>
    RCLike.ofReal_pos.mpr (pairSpectrum_pos c hc0 hc1 p))

/-- For the strictly positive-angle canonical pair every singular output has
an infinite actual loss for at least one of the two states. -/
theorem canonical_singular_one_loss_top [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1)
    (A : Density (Fin 2 × ι)) (hA : ¬ A.matrix.PosDef) :
    chiR (stateP c s hcircle) A = ∞ ∨ chiR (stateQ c s hcircle) A = ∞ := by
  by_cases hp : chiR (stateP c s hcircle) A = ∞
  · exact Or.inl hp
  right
  by_contra hq
  apply hA
  apply supports_flat_pair_force_posDef (canonicalP c s hcircle) (canonicalQ c s hcircle)
    _ _ (canonical_sum_posDef c s hcircle hc0 hc1) A
  · exact (chiR_ne_top_iff _ _).mp hp
  · exact (chiR_ne_top_iff _ _).mp hq

/-- The maximum actual loss lower bound now includes every density output,
including singular outputs with their exact infinite-loss convention. -/
theorem canonical_max_lower [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1) (hs0 : ∀ i, 0 ≤ s i)
    (A : Density (Fin 2 × ι)) :
    ENNReal.ofReal (principalRadius s) ≤
      max (chiR (stateP c s hcircle) A) (chiR (stateQ c s hcircle) A) := by
  by_cases hA : A.matrix.PosDef
  · have havg := canonical_average_lower c s hcircle hc0 (fun i => (hc1 i).le) hs0 A hA
    rw [PositiveLossBridge.chiR_toReal_standard _ _ hA,
      PositiveLossBridge.chiR_toReal_standard _ _ hA] at havg
    rw [PositiveLossBridge.chiR_eq_standardRightEnergy _ _ hA,
      PositiveLossBridge.chiR_eq_standardRightEnergy _ _ hA]
    by_cases hle : Normalization.standardRightEnergy (stateP c s hcircle).matrix A.matrix ≤
        Normalization.standardRightEnergy (stateQ c s hcircle).matrix A.matrix
    · rw [max_eq_right (ENNReal.ofReal_le_ofReal hle)]
      apply ENNReal.ofReal_le_ofReal
      linarith
    · rw [max_eq_left (ENNReal.ofReal_le_ofReal (le_of_not_ge hle))]
      apply ENNReal.ofReal_le_ofReal
      linarith
  · obtain hp | hq := canonical_singular_one_loss_top c s hcircle hc0 hc1 A hA
    · simp [hp]
    · simp [hq]

/-- The principal-angle expression is the attained infimum of the maximum
actual right-inverse losses, over all density matrices, for the strict-angle
canonical pair on the full `2r`-dimensional space. -/
theorem canonical_common_center_minimax [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1) (hs0 : ∀ i, 0 ≤ s i) :
    (⨅ A : Density (Fin 2 × ι),
      max (chiR (stateP c s hcircle) A) (chiR (stateQ c s hcircle) A)) =
        ENNReal.ofReal (principalRadius s) := by
  apply le_antisymm
  · apply iInf_le_of_le (canonicalCenter c hc0 hc1)
    obtain ⟨hp, hq⟩ := canonical_center_losses c s hcircle hc0 hc1 hs0
    rw [hp, hq, max_self]
  · exact le_iInf (canonical_max_lower c s hcircle hc0 hc1 hs0)

lemma ofReal_average (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (ENNReal.ofReal x + ENNReal.ofReal y) / 2 = ENNReal.ofReal ((x + y) / 2) := by
  rw [← ENNReal.ofReal_add hx hy, ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- The analogous lower bound for the actual arithmetic mean, with infinite
losses retained for singular outputs. -/
theorem canonical_mean_lower [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1) (hs0 : ∀ i, 0 ≤ s i)
    (A : Density (Fin 2 × ι)) :
    ENNReal.ofReal (principalRadius s) ≤
      (chiR (stateP c s hcircle) A + chiR (stateQ c s hcircle) A) / 2 := by
  by_cases hA : A.matrix.PosDef
  · have havg := canonical_average_lower c s hcircle hc0 (fun i => (hc1 i).le) hs0 A hA
    rw [PositiveLossBridge.chiR_toReal_standard _ _ hA,
      PositiveLossBridge.chiR_toReal_standard _ _ hA] at havg
    rw [PositiveLossBridge.chiR_eq_standardRightEnergy _ _ hA,
      PositiveLossBridge.chiR_eq_standardRightEnergy _ _ hA,
      ofReal_average _ _ (PositiveLossBridge.standardRightEnergy_nonneg _ _ hA)
        (PositiveLossBridge.standardRightEnergy_nonneg _ _ hA)]
    exact ENNReal.ofReal_le_ofReal havg
  · obtain hp | hq := canonical_singular_one_loss_top c s hcircle hc0 hc1 A hA
    · rw [hp, top_add, ENNReal.top_div_of_ne_top (by norm_num)]
      exact le_top
    · rw [hq, add_top, ENNReal.top_div_of_ne_top (by norm_num)]
      exact le_top

/-- Replacing the maximum by the arithmetic mean gives the same attained
minimum for this actual full-support canonical pair. -/
theorem canonical_common_center_mean [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1) (hs0 : ∀ i, 0 ≤ s i) :
    (⨅ A : Density (Fin 2 × ι),
      (chiR (stateP c s hcircle) A + chiR (stateQ c s hcircle) A) / 2) =
        ENNReal.ofReal (principalRadius s) := by
  apply le_antisymm
  · apply iInf_le_of_le (canonicalCenter c hc0 hc1)
    obtain ⟨hp, hq⟩ := canonical_center_losses c s hcircle hc0 hc1 hs0
    have hr : 0 ≤ principalRadius s := by
      rw [← canonical_center_average c s hcircle hc0 hc1 hs0]
      positivity
    rw [hp, hq, ofReal_average _ _ hr hr]
    have he : (principalRadius s + principalRadius s) / 2 = principalRadius s := by ring
    rw [he]
  · exact le_iInf (canonical_mean_lower c s hcircle hc0 hc1 hs0)


/-- The explicit matrix is the continuous-functional-calculus positive square
root of the actual projector sum, including zero principal angles. -/
theorem cfc_sqrt_sum (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) :
    CFC.sqrt ((canonicalP c s hcircle).matrix + (canonicalQ c s hcircle).matrix) =
      sqrtSum c :=
  CFC.sqrt_unique (sqrtSum_square c s hcircle hc0 hc1) (sqrtSum_posSemidef c).nonneg

theorem cfc_sqrt_sum_trace (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) (hs0 : ∀ i, 0 ≤ s i) :
    (Matrix.trace (CFC.sqrt ((canonicalP c s hcircle).matrix +
      (canonicalQ c s hcircle).matrix))).re =
      Real.sqrt 2 * ∑ i, Real.sqrt (1 + s i) := by
  rw [cfc_sqrt_sum c s hcircle hc0 hc1]
  exact sqrtSum_trace c s hcircle hc0 hc1 hs0

/-- The trace norm is defined on the actual matrix through its positive
absolute value, rather than through an asserted eigenvalue list. -/
def traceNorm (X : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (CFC.sqrt (Xᴴ * X))).re

def differenceBlock (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, (s : ℂ); (s : ℂ), 0]

lemma angleBlock_sub_flip (c s : ℝ) :
    angleBlock c s - angleBlock c (-s) = differenceBlock s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [angleBlock, differenceBlock] <;> ring

lemma differenceBlock_hermitian (s : ℝ) : (differenceBlock s).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [differenceBlock, Matrix.conjTranspose_apply]

lemma differenceBlock_square (s : ℝ) :
    differenceBlock s * differenceBlock s = Matrix.diagonal (fun _ : Fin 2 => ((s ^ 2 : ℝ) : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [differenceBlock, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] <;> ring

theorem canonical_difference_block (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1) :
    (canonicalP c s hcircle).matrix - (canonicalQ c s hcircle).matrix =
      Matrix.blockDiagonal (fun i => differenceBlock (s i)) := by
  change Matrix.blockDiagonal (fun i => angleBlock (c i) (s i)) -
    Matrix.blockDiagonal (fun i => angleBlock (c i) (-s i)) = _
  rw [← Matrix.blockDiagonal_sub]
  change Matrix.blockDiagonal (fun i => angleBlock (c i) (s i) -
    angleBlock (c i) (-s i)) = _
  congr 1
  funext i
  exact angleBlock_sub_flip _ _

def absoluteDifference (s : ι → ℝ) : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ :=
  Normalization.diagonalMatrix (fun p => s p.2)

lemma absoluteDifference_posSemidef (s : ι → ℝ) (hs0 : ∀ i, 0 ≤ s i) :
    (absoluteDifference s).PosSemidef :=
  Matrix.PosSemidef.diagonal (fun p => RCLike.ofReal_nonneg.mpr (hs0 p.2))

theorem absoluteDifference_square (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1) :
    absoluteDifference s * absoluteDifference s =
      ((canonicalP c s hcircle).matrix - (canonicalQ c s hcircle).matrix)ᴴ *
        ((canonicalP c s hcircle).matrix - (canonicalQ c s hcircle).matrix) := by
  rw [((canonicalP c s hcircle).hermitian.sub (canonicalQ c s hcircle).hermitian).eq,
    canonical_difference_block, ← Matrix.blockDiagonal_mul]
  change absoluteDifference s * absoluteDifference s =
    Matrix.blockDiagonal (fun i => differenceBlock (s i) * differenceBlock (s i))
  have hb : (fun i => differenceBlock (s i) * differenceBlock (s i)) =
      fun i => Matrix.diagonal (fun _ : Fin 2 => ((s i ^ 2 : ℝ) : ℂ)) := by
    funext i
    exact differenceBlock_square _
  rw [hb, Matrix.blockDiagonal_diagonal]
  unfold absoluteDifference Normalization.diagonalMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  simp [sq, Complex.ofReal_mul]

theorem canonical_traceNorm (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1) (hs0 : ∀ i, 0 ≤ s i) :
    traceNorm ((canonicalP c s hcircle).matrix - (canonicalQ c s hcircle).matrix) =
      2 * ∑ i, s i := by
  have habs := CFC.sqrt_unique (absoluteDifference_square c s hcircle)
    (absoluteDifference_posSemidef s hs0).nonneg
  unfold traceNorm
  rw [habs]
  simp [absoluteDifference, Normalization.diagonalMatrix, Matrix.trace_diagonal,
    Fintype.sum_prod_type, two_mul]

/-- The source chord lower bound, now in terms of the trace norm of the two
actual projectors. It also holds at zero principal angles. -/
theorem principalRadius_traceNorm_lower [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1) (hs0 : ∀ i, 0 ≤ s i) :
    (Real.sqrt 2 - 1) *
      traceNorm ((canonicalP c s hcircle).matrix - (canonicalQ c s hcircle).matrix) /
        Fintype.card ι ≤ principalRadius s := by
  have hs1 : ∀ i, s i ≤ 1 := fun i => by nlinarith [hcircle i, sq_nonneg (c i)]
  have hr : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := principal_radius_chord s hs0 hs1 hr
  rw [canonical_traceNorm c s hcircle hs0]
  unfold principalRadius
  convert h using 1
  ring


omit [DecidableEq ι] in
lemma density_eq_of_matrix {ρ σ : Density ι} (h : ρ.matrix = σ.matrix) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

lemma projector_rank_conjugate (U : Matrix.unitaryGroup ι ℂ)
    (P Q : OrthogonalProjector ι)
    (h : P.matrix = Normalization.conjugate (U : Matrix ι ι ℂ) Q.matrix) :
    P.matrix.rank = Q.matrix.rank := by
  have ht : (P.matrix.rank : ℂ) = (Q.matrix.rank : ℂ) := by
    rw [← P.trace_eq_rank, h,
      Normalization.trace_conjugate _ _ (PositiveLossBridge.unitary_left U), Q.trace_eq_rank]
  exact_mod_cast ht

lemma flat_conjugate (U : Matrix.unitaryGroup ι ℂ) (P Q : OrthogonalProjector ι)
    (h : P.matrix = Normalization.conjugate (U : Matrix ι ι ℂ) Q.matrix)
    (hrP : 0 < P.matrix.rank) (hrQ : 0 < Q.matrix.rank) :
    P.flat hrP = PositiveLossBridge.conjugateDensity U (Q.flat hrQ) := by
  apply density_eq_of_matrix
  have hr := projector_rank_conjugate U P Q h
  change ((P.matrix.rank : ℝ)⁻¹) • P.matrix =
    Normalization.conjugate (U : Matrix ι ι ℂ) (((Q.matrix.rank : ℝ)⁻¹) • Q.matrix)
  rw [hr, h]
  simp only [Normalization.conjugate, Matrix.mul_smul, Matrix.smul_mul]

lemma conjugateDensity_star_cancel (U : Matrix.unitaryGroup ι ℂ) (A : Density ι) :
    PositiveLossBridge.conjugateDensity U
      (PositiveLossBridge.conjugateDensity (star U) A) = A := by
  apply density_eq_of_matrix
  change Normalization.conjugate (U : Matrix ι ι ℂ)
    (Normalization.conjugate ((star U : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)
      A.matrix) = A.matrix
  simpa only [unitary.coe_star, Matrix.star_eq_conjTranspose,
    Normalization.conjugate, Normalization.coordinates, Matrix.conjTranspose_conjTranspose] using
    Normalization.conjugate_coordinates (U : Matrix ι ι ℂ) A.matrix
      (PositiveLossBridge.unitary_right U)

/-- An arbitrary positive output can be pulled back through the actual unitary;
this statement is about `QuantumModel.chiR` rather than a scalar surrogate. -/
lemma chiR_conjugate_pullback (U : Matrix.unitaryGroup ι ℂ) (ρ A : Density ι)
    (hA : A.matrix.PosDef) :
    chiR (PositiveLossBridge.conjugateDensity U ρ) A =
      chiR ρ (PositiveLossBridge.conjugateDensity (star U) A) := by
  have h := PositiveLossBridge.chiR_unitary U ρ
    (PositiveLossBridge.conjugateDensity (star U) A)
    (PositiveLossBridge.conjugateDensity_posDef (star U) A hA)
  rw [conjugateDensity_star_cancel] at h
  exact h

/-- Raw principal-angle data for a full-span pair. These are only actual
unitary matrix equalities and circle/interval conditions; no loss, fidelity,
minimum, or common-center statement is included in the data. -/
structure StrictPrincipalAngleForm (P Q : OrthogonalProjector (Fin 2 × ι)) where
  c : ι → ℝ
  s : ι → ℝ
  circle : ∀ i, c i ^ 2 + s i ^ 2 = 1
  cosine_nonneg : ∀ i, 0 ≤ c i
  cosine_lt_one : ∀ i, c i < 1
  sine_nonneg : ∀ i, 0 ≤ s i
  unitary : Matrix.unitaryGroup (Fin 2 × ι) ℂ
  first : P.matrix = Normalization.conjugate
    (unitary : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (canonicalP c s circle).matrix
  second : Q.matrix = Normalization.conjugate
    (unitary : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (canonicalQ c s circle).matrix


lemma cfc_sqrt_conjugate (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ)
    (hX : X.PosSemidef) :
    CFC.sqrt (Normalization.conjugate (U : Matrix ι ι ℂ) X) =
      Normalization.conjugate (U : Matrix ι ι ℂ) (CFC.sqrt X) := by
  apply CFC.sqrt_unique
  · rw [← Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U),
      CFC.sqrt_mul_sqrt_self X hX.nonneg]
  · exact ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X)).mul_mul_conjTranspose_same
      (U : Matrix ι ι ℂ)).nonneg

lemma traceNorm_conjugate (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    traceNorm (Normalization.conjugate (U : Matrix ι ι ℂ) X) = traceNorm X := by
  have hg : (Normalization.conjugate (U : Matrix ι ι ℂ) X)ᴴ *
      Normalization.conjugate (U : Matrix ι ι ℂ) X =
        Normalization.conjugate (U : Matrix ι ι ℂ) (Xᴴ * X) := by
    simp only [Normalization.conjugate, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc
      ((U : Matrix ι ι ℂ) * (Xᴴ * (U : Matrix ι ι ℂ)ᴴ)) *
          ((U : Matrix ι ι ℂ) * X * (U : Matrix ι ι ℂ)ᴴ) =
        (U : Matrix ι ι ℂ) * Xᴴ * ((U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ)) *
          X * (U : Matrix ι ι ℂ)ᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [PositiveLossBridge.unitary_left U]; simp only [Matrix.mul_one,
          Matrix.mul_assoc]
  unfold traceNorm
  rw [hg, cfc_sqrt_conjugate U _ (Matrix.posSemidef_conjTranspose_mul_self X),
    Normalization.trace_conjugate _ _ (PositiveLossBridge.unitary_left U)]

namespace StrictPrincipalAngleForm

variable {P Q : OrthogonalProjector (Fin 2 × ι)}

lemma rankP (D : StrictPrincipalAngleForm P Q) : P.matrix.rank = Fintype.card ι := by
  rw [projector_rank_conjugate D.unitary P _ D.first, canonicalP_rank]

lemma rankQ (D : StrictPrincipalAngleForm P Q) : Q.matrix.rank = Fintype.card ι := by
  rw [projector_rank_conjugate D.unitary Q _ D.second, canonicalQ_rank]

lemma sum_posDef (D : StrictPrincipalAngleForm P Q) : (P.matrix + Q.matrix).PosDef := by
  rw [D.first, D.second, ← Normalization.conjugate_add]
  exact TailConvexity.conjugate_posDef _ _ (PositiveLossBridge.unitary_right D.unitary)
    (canonical_sum_posDef D.c D.s D.circle D.cosine_nonneg D.cosine_lt_one)

variable [Nonempty ι]

lemma rankP_pos (D : StrictPrincipalAngleForm P Q) : 0 < P.matrix.rank := by
  rw [D.rankP]
  exact Fintype.card_pos

lemma rankQ_pos (D : StrictPrincipalAngleForm P Q) : 0 < Q.matrix.rank := by
  rw [D.rankQ]
  exact Fintype.card_pos

lemma flatP (D : StrictPrincipalAngleForm P Q) :
    P.flat D.rankP_pos = PositiveLossBridge.conjugateDensity D.unitary
      (stateP D.c D.s D.circle) :=
  flat_conjugate D.unitary P _ D.first _ _

lemma flatQ (D : StrictPrincipalAngleForm P Q) :
    Q.flat D.rankQ_pos = PositiveLossBridge.conjugateDensity D.unitary
      (stateQ D.c D.s D.circle) :=
  flat_conjugate D.unitary Q _ D.second _ _

/-- The actual square-root center, transported by the raw unitary data. -/
def center (D : StrictPrincipalAngleForm P Q) : Density (Fin 2 × ι) :=
  PositiveLossBridge.conjugateDensity D.unitary
    (canonicalCenter D.c D.cosine_nonneg D.cosine_lt_one)

lemma center_losses (D : StrictPrincipalAngleForm P Q) :
    chiR (P.flat D.rankP_pos) D.center = ENNReal.ofReal (principalRadius D.s) ∧
    chiR (Q.flat D.rankQ_pos) D.center = ENNReal.ofReal (principalRadius D.s) := by
  rw [D.flatP, D.flatQ]
  unfold center canonicalCenter
  rw [PositiveLossBridge.chiR_unitary D.unitary _ _
      (squareRootCenter_posDef _ _),
    PositiveLossBridge.chiR_unitary D.unitary _ _ (squareRootCenter_posDef _ _)]
  exact canonical_center_losses D.c D.s D.circle D.cosine_nonneg D.cosine_lt_one D.sine_nonneg

lemma max_lower (D : StrictPrincipalAngleForm P Q) (A : Density (Fin 2 × ι)) :
    ENNReal.ofReal (principalRadius D.s) ≤
      max (chiR (P.flat D.rankP_pos) A) (chiR (Q.flat D.rankQ_pos) A) := by
  by_cases hA : A.matrix.PosDef
  · rw [D.flatP, D.flatQ, chiR_conjugate_pullback D.unitary _ A hA,
      chiR_conjugate_pullback D.unitary _ A hA]
    exact canonical_max_lower D.c D.s D.circle D.cosine_nonneg D.cosine_lt_one
      D.sine_nonneg _
  · by_cases hp : chiR (P.flat D.rankP_pos) A = ∞
    · simp [hp]
    have hq : chiR (Q.flat D.rankQ_pos) A = ∞ := by
      by_contra hq
      exact hA (supports_flat_pair_force_posDef P Q _ _ D.sum_posDef A
        ((chiR_ne_top_iff _ _).mp hp) ((chiR_ne_top_iff _ _).mp hq))
    simp [hq]

/-- Actual Proposition B.1 for arbitrary full-span, strictly positive-angle
projector pairs, conditional only on the raw unitary block decomposition. The
infimum ranges over every density, with the singular support convention. -/
theorem minimax (D : StrictPrincipalAngleForm P Q) :
    (⨅ A : Density (Fin 2 × ι),
      max (chiR (P.flat D.rankP_pos) A) (chiR (Q.flat D.rankQ_pos) A)) =
      ENNReal.ofReal (principalRadius D.s) := by
  apply le_antisymm
  · apply iInf_le_of_le D.center
    obtain ⟨hp, hq⟩ := D.center_losses
    rw [hp, hq, max_self]
  · exact le_iInf D.max_lower


omit [Nonempty ι] in
lemma sqrt_sum (D : StrictPrincipalAngleForm P Q) :
    CFC.sqrt (P.matrix + Q.matrix) =
      Normalization.conjugate (D.unitary : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ)
        (sqrtSum D.c) := by
  rw [D.first, D.second, ← Normalization.conjugate_add,
    cfc_sqrt_conjugate D.unitary _
      ((canonicalP D.c D.s D.circle).positive.add (canonicalQ D.c D.s D.circle).positive),
    cfc_sqrt_sum D.c D.s D.circle D.cosine_nonneg (fun i => (D.cosine_lt_one i).le)]

omit [Nonempty ι] in
lemma sqrt_sum_trace (D : StrictPrincipalAngleForm P Q) :
    (Matrix.trace (CFC.sqrt (P.matrix + Q.matrix))).re =
      Real.sqrt 2 * ∑ i, Real.sqrt (1 + D.s i) := by
  rw [D.sqrt_sum, Normalization.trace_conjugate _ _
    (PositiveLossBridge.unitary_left D.unitary)]
  exact sqrtSum_trace D.c D.s D.circle D.cosine_nonneg
    (fun i => (D.cosine_lt_one i).le) D.sine_nonneg

/-- The transported center is exactly the normalized positive square root of
`P+Q` in the original matrix basis. -/
lemma center_matrix (D : StrictPrincipalAngleForm P Q) :
    D.center.matrix =
      (((1 / (Matrix.trace (CFC.sqrt (P.matrix + Q.matrix))).re : ℝ) : ℂ) •
        CFC.sqrt (P.matrix + Q.matrix)) := by
  rw [D.sqrt_sum, Normalization.trace_conjugate _ _
    (PositiveLossBridge.unitary_left D.unitary)]
  unfold center PositiveLossBridge.conjugateDensity canonicalCenter squareRootCenter
  exact Normalization.conjugate_smul _ _ _

omit [Nonempty ι] in
lemma traceNorm_difference (D : StrictPrincipalAngleForm P Q) :
    traceNorm (P.matrix - Q.matrix) = 2 * ∑ i, D.s i := by
  rw [D.first, D.second, ← Normalization.conjugate_sub,
    traceNorm_conjugate, canonical_traceNorm D.c D.s D.circle D.sine_nonneg]

lemma chord (D : StrictPrincipalAngleForm P Q) :
    (Real.sqrt 2 - 1) * traceNorm (P.matrix - Q.matrix) / Fintype.card ι ≤
      principalRadius D.s := by
  have h := principalRadius_traceNorm_lower D.c D.s D.circle D.sine_nonneg
  rw [canonical_traceNorm D.c D.s D.circle D.sine_nonneg] at h
  rwa [D.traceNorm_difference]

lemma mean_lower (D : StrictPrincipalAngleForm P Q) (A : Density (Fin 2 × ι)) :
    ENNReal.ofReal (principalRadius D.s) ≤
      (chiR (P.flat D.rankP_pos) A + chiR (Q.flat D.rankQ_pos) A) / 2 := by
  by_cases hA : A.matrix.PosDef
  · rw [D.flatP, D.flatQ, chiR_conjugate_pullback D.unitary _ A hA,
      chiR_conjugate_pullback D.unitary _ A hA]
    exact canonical_mean_lower D.c D.s D.circle D.cosine_nonneg D.cosine_lt_one
      D.sine_nonneg _
  · by_cases hp : chiR (P.flat D.rankP_pos) A = ∞
    · rw [hp, top_add, ENNReal.top_div_of_ne_top (by norm_num)]
      exact le_top
    have hq : chiR (Q.flat D.rankQ_pos) A = ∞ := by
      by_contra hq
      exact hA (supports_flat_pair_force_posDef P Q _ _ D.sum_posDef A
        ((chiR_ne_top_iff _ _).mp hp) ((chiR_ne_top_iff _ _).mp hq))
    rw [hq, add_top, ENNReal.top_div_of_ne_top (by norm_num)]
    exact le_top

/-- The same center attains the minimum arithmetic mean, with actual `∞`
losses on unsupported singular outputs. -/
theorem mean (D : StrictPrincipalAngleForm P Q) :
    (⨅ A : Density (Fin 2 × ι),
      (chiR (P.flat D.rankP_pos) A + chiR (Q.flat D.rankQ_pos) A) / 2) =
      ENNReal.ofReal (principalRadius D.s) := by
  apply le_antisymm
  · apply iInf_le_of_le D.center
    obtain ⟨hp, hq⟩ := D.center_losses
    have hr : 0 ≤ principalRadius D.s := by
      rw [← canonical_center_average D.c D.s D.circle D.cosine_nonneg
        D.cosine_lt_one D.sine_nonneg]
      positivity
    rw [hp, hq, ofReal_average _ _ hr hr]
    have he : (principalRadius D.s + principalRadius D.s) / 2 = principalRadius D.s := by ring
    rw [he]
  · exact le_iInf D.mean_lower


/-- Proposition B.1's trace-norm lower bound for the actual minimax value. -/
theorem minimax_chord (D : StrictPrincipalAngleForm P Q) :
    ENNReal.ofReal ((Real.sqrt 2 - 1) * traceNorm (P.matrix - Q.matrix) /
      Fintype.card ι) ≤
      ⨅ A : Density (Fin 2 × ι),
        max (chiR (P.flat D.rankP_pos) A) (chiR (Q.flat D.rankQ_pos) A) := by
  rw [D.minimax]
  exact ENNReal.ofReal_le_ofReal D.chord

/-- The same chord bound holds for the minimum actual arithmetic mean. -/
theorem mean_chord (D : StrictPrincipalAngleForm P Q) :
    ENNReal.ofReal ((Real.sqrt 2 - 1) * traceNorm (P.matrix - Q.matrix) /
      Fintype.card ι) ≤
      ⨅ A : Density (Fin 2 × ι),
        (chiR (P.flat D.rankP_pos) A + chiR (Q.flat D.rankQ_pos) A) / 2 := by
  rw [D.mean]
  exact ENNReal.ofReal_le_ofReal D.chord

end StrictPrincipalAngleForm

end Paper26.CommonCenter
