import Paper25.BlockEncoding
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Rational functional calculus and compression (equation 15)

The filter respects an intertwining isometry.  In particular the real part of
the compression walk intertwines the original Hermitian compression, so that
its filter has precisely the desired compressed block.  All inverses below
are justified by positivity of H² + δ²I.
-/

noncomputable section
open scoped ComplexOrder

namespace Paper25

section RationalCalculus

variable {N n : Type*} [Fintype N] [DecidableEq N] [Fintype n] [DecidableEq n]

lemma isUnit_hermitian_regularized (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (δ : ℝ) (hδ : 0 < δ) :
    IsUnit (H * H + ((δ ^ 2 : ℝ) : ℂ) • 1) := by
  have hgram : (H * H).PosSemidef := by
    simpa only [hH.eq] using Matrix.posSemidef_self_mul_conjTranspose H
  have hpos : (((δ ^ 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast (sq_pos_of_ne_zero hδ.ne'))
  have hsum := hpos.add_posSemidef hgram
  rw [add_comm] at hsum
  exact hsum.isUnit

/-- Rational functional calculus respects a rectangular intertwiner. -/
theorem filterRat_intertwine (S : Matrix N N ℂ) (H : Matrix n n ℂ)
    (C : Matrix N n ℂ) (hS : S.IsHermitian) (hH : H.IsHermitian)
    (hSC : S * C = C * H) (δ : ℝ) (hδ : 0 < δ) :
    filterRat S δ * C = C * filterRat H δ := by
  let GS := S * S + ((δ ^ 2 : ℝ) : ℂ) • (1 : Matrix N N ℂ)
  let GH := H * H + ((δ ^ 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)
  have hGS : IsUnit GS.det := (Matrix.isUnit_iff_isUnit_det GS).mp
    (isUnit_hermitian_regularized S hS δ hδ)
  have hGH : IsUnit GH.det := (Matrix.isUnit_iff_isUnit_det GH).mp
    (isUnit_hermitian_regularized H hH δ hδ)
  have hinter : GS * C = C * GH := by
    dsimp [GS, GH]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    congr 1
    calc
      (S * S) * C = S * (S * C) := Matrix.mul_assoc _ _ _
      _ = S * (C * H) := by rw [hSC]
      _ = (S * C) * H := (Matrix.mul_assoc _ _ _).symm
      _ = (C * H) * H := by rw [hSC]
      _ = C * (H * H) := Matrix.mul_assoc _ _ _
  have hinv : GS⁻¹ * C = C * GH⁻¹ := by
    calc
      GS⁻¹ * C = (GS⁻¹ * C) * (GH * GH⁻¹) := by rw [Matrix.mul_nonsing_inv GH hGH, Matrix.mul_one]
      _ = GS⁻¹ * (C * GH) * GH⁻¹ := by simp only [Matrix.mul_assoc]
      _ = GS⁻¹ * (GS * C) * GH⁻¹ := by rw [hinter]
      _ = C * GH⁻¹ := by rw [Matrix.nonsing_inv_mul_cancel_left GS C hGS]
  change ((δ : ℂ) • S * GS⁻¹) * C = C * ((δ : ℂ) • H * GH⁻¹)
  calc
    _ = (δ : ℂ) • (S * (GS⁻¹ * C)) := by simp only [Matrix.smul_mul, Matrix.mul_assoc]
    _ = (δ : ℂ) • (S * (C * GH⁻¹)) := by rw [hinv]
    _ = (δ : ℂ) • ((C * H) * GH⁻¹) := by rw [← Matrix.mul_assoc, hSC]
    _ = _ := by simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- Compression along an isometry commutes with the filter whenever the
Hermitian operator preserves that isometry's image. -/
theorem filterRat_isometry_compression (S : Matrix N N ℂ) (H : Matrix n n ℂ)
    (E : Matrix N n ℂ) (hE : E.conjTranspose * E = 1)
    (hS : S.IsHermitian) (hH : H.IsHermitian) (hSE : S * E = E * H)
    (δ : ℝ) (hδ : 0 < δ) :
    E.conjTranspose * filterRat S δ * E = filterRat H δ := by
  rw [Matrix.mul_assoc, filterRat_intertwine S H E hS hH hSE δ hδ,
    ← Matrix.mul_assoc, hE, Matrix.one_mul]

end RationalCalculus

section WalkCompression

variable {N n : Type*} [Fintype N] [DecidableEq N] [Fintype n] [DecidableEq n]

/-- Orthogonal projection onto the image of the zero-ancilla embedding. -/
def isometryProjector (E : Matrix N n ℂ) : Matrix N N ℂ := E * E.conjTranspose

lemma isometryProjector_hermitian (E : Matrix N n ℂ) : (isometryProjector E).IsHermitian := by
  change (E * E.conjTranspose).conjTranspose = E * E.conjTranspose
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

lemma isometryProjector_sq (E : Matrix N n ℂ) (hE : E.conjTranspose * E = 1) :
    isometryProjector E * isometryProjector E = isometryProjector E := by
  unfold isometryProjector
  calc
    _ = E * (E.conjTranspose * E) * E.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hE, Matrix.mul_one]

/-- Hermitian compression U ↦ E†UE. -/
def isometryCompression (E : Matrix N n ℂ) (U : Matrix N N ℂ) : Matrix n n ℂ :=
  E.conjTranspose * U * E

lemma isometryCompression_hermitian (E : Matrix N n ℂ) (U : Matrix N N ℂ)
    (hU : U.IsHermitian) : (isometryCompression E U).IsHermitian := by
  change (E.conjTranspose * U * E).conjTranspose = E.conjTranspose * U * E
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hU.eq,
    Matrix.mul_assoc]

/-- The Hermitian real part of any matrix. -/
def walkRealPart (V : Matrix N N ℂ) : Matrix N N ℂ := (1 / 2 : ℂ) • (V + star V)

lemma walkRealPart_hermitian (V : Matrix N N ℂ) : (walkRealPart V).IsHermitian := by
  show star (walkRealPart V) = _
  simp [walkRealPart, star_smul, star_add, add_comm]

/-- Equation (14) implies invariance of the all-zero ancilla subspace.
This is the intertwiner needed by functional calculus, not an assumed block identity. -/
lemma compressionWalk_intertwine (U : Matrix N N ℂ) (E : Matrix N n ℂ)
    (hU : U.IsHermitian) (hE : E.conjTranspose * E = 1) :
    walkRealPart (compressionWalk (isometryProjector E) U) * E =
      E * isometryCompression E U := by
  have hPE : isometryProjector E * E = E := by
    unfold isometryProjector
    rw [Matrix.mul_assoc, hE, Matrix.mul_one]
  have hz : (1 - isometryProjector E) * E = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPE, sub_self]
  unfold walkRealPart
  rw [compressionWalk_realPart _ _ (isometryProjector_hermitian E) hU,
    Matrix.sub_mul]
  rw [Matrix.mul_assoc ((1 - isometryProjector E) * U) (1 - isometryProjector E) E,
    hz, Matrix.mul_zero, sub_zero]
  rw [Matrix.mul_assoc (isometryProjector E * U) (isometryProjector E) E, hPE]
  unfold isometryProjector isometryCompression
  simp only [Matrix.mul_assoc]

/-- The concrete matrix embedding of a computational-basis subspace. -/
def basisEmbedding (f : n → N) : Matrix N n ℂ :=
  fun p i => if p = f i then 1 else 0

lemma basisEmbedding_isometry (f : n → N) (hf : Function.Injective f) :
    (basisEmbedding f).conjTranspose * basisEmbedding f = 1 := by
  ext i j
  by_cases hij : i = j <;>
    simp [basisEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite,
      Matrix.one_apply, hf.eq_iff, hij, eq_comm]

/-- Isometry compression specializes exactly to extraction of the selected matrix block. -/
lemma basisEmbedding_compression (f : n → N) (U : Matrix N N ℂ) :
    isometryCompression (basisEmbedding f) U = U.submatrix f f := by
  ext i j
  simp [isometryCompression, basisEmbedding, Matrix.mul_apply,
    Matrix.conjTranspose_apply, apply_ite]

/-- The all-zero ancilla embedding, leaving the data register unrestricted. -/
def zeroAncillaEmbedding {s : Type*} [DecidableEq s] (q : s) : Matrix (s × n) n ℂ :=
  basisEmbedding (fun i => (q, i))

lemma zeroAncillaEmbedding_isometry {s : Type*} [Fintype s] [DecidableEq s] (q : s) :
    (zeroAncillaEmbedding (n := n) q).conjTranspose * zeroAncillaEmbedding (n := n) q =
      (1 : Matrix n n ℂ) := by
  apply basisEmbedding_isometry
  intro i j h
  exact (Prod.mk.inj h).2

/-- Equation (15), using the rational functional calculus for cos(eigenphase).
The actual projection is E E† and the compressed Hermitian matrix is E† U E. -/
theorem compressionWalk_filter (U : Matrix N N ℂ) (E : Matrix N n ℂ)
    (hU : U.IsHermitian) (hE : E.conjTranspose * E = 1) (δ : ℝ) (hδ : 0 < δ) :
    E.conjTranspose *
      filterRat (walkRealPart (compressionWalk (isometryProjector E) U)) δ * E =
      filterRat (isometryCompression E U) δ := by
  exact filterRat_isometry_compression _ _ E hE (walkRealPart_hermitian _)
    (isometryCompression_hermitian E U hU) (compressionWalk_intertwine U E hU hE) δ hδ

/-- Equation (15) also holds for the filter defined directly by spectral decomposition. -/
theorem compressionWalk_spectral_filter (U : Matrix N N ℂ) (E : Matrix N n ℂ)
    (hU : U.IsHermitian) (hE : E.conjTranspose * E = 1) (δ : ℝ) (hδ : 0 < δ) :
    E.conjTranspose *
      filterMat (walkRealPart (compressionWalk (isometryProjector E) U))
        (walkRealPart_hermitian _) δ * E =
      filterMat (isometryCompression E U) (isometryCompression_hermitian E U hU) δ := by
  simp only [filterMat_eq_filterRat _ _ δ hδ]
  exact compressionWalk_filter U E hU hE δ hδ

end WalkCompression

section OperatorNorm

open scoped Matrix.Norms.L2Operator

variable {N n : Type*} [Fintype N] [DecidableEq N] [Fintype n] [DecidableEq n]

lemma matrix_opNorm_one_le (n : Type*) [Fintype n] [DecidableEq n] :
    ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  classical
  by_cases hn : Nonempty n
  · letI := hn
    rw [norm_one]
  · haveI : IsEmpty n := ⟨fun a => hn ⟨a⟩⟩
    have hz : (1 : Matrix n n ℂ) = 0 := by ext i j; exact isEmptyElim i
    rw [hz, norm_zero]
    norm_num

lemma isometry_opNorm_le_one (E : Matrix N n ℂ) (hE : E.conjTranspose * E = 1) :
    ‖E‖ ≤ 1 := by
  have he : ‖E‖ * ‖E‖ = ‖(1 : Matrix n n ℂ)‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hE]
  have h1 := matrix_opNorm_one_le n
  nlinarith [norm_nonneg E]

/-- Compression cannot increase operator norm, including approximation errors. -/
theorem isometryCompression_opNorm_le (E : Matrix N n ℂ)
    (hE : E.conjTranspose * E = 1) (M : Matrix N N ℂ) :
    ‖isometryCompression E M‖ ≤ ‖M‖ := by
  have he := isometry_opNorm_le_one E hE
  unfold isometryCompression
  calc
    _ ≤ (‖E.conjTranspose‖ * ‖M‖) * ‖E‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg E))
    _ = (‖E‖ * ‖M‖) * ‖E‖ := by rw [Matrix.l2_opNorm_conjTranspose]
    _ ≤ (1 * ‖M‖) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right he (norm_nonneg M)) he
        (norm_nonneg E) (by positivity)
    _ = ‖M‖ := by ring

/-- The Hermitian compression of the constructed unitary is a contraction,
as required immediately after equation (13). -/
theorem isometryCompression_opNorm_le_one (E : Matrix N n ℂ)
    (hE : E.conjTranspose * E = 1) (U : Matrix N N ℂ)
    (hU : U ∈ Matrix.unitaryGroup N ℂ) :
    ‖isometryCompression E U‖ ≤ 1 := by
  apply (isometryCompression_opNorm_le E hE U).trans
  have hu : ‖U‖ * ‖U‖ = ‖(1 : Matrix N N ℂ)‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self,
      show U.conjTranspose * U = 1 from hU.1]
  have h1 := matrix_opNorm_one_le N
  nlinarith [norm_nonneg U]

end OperatorNorm

end Paper25
