import Paper25.Filter
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/-!
# Matrix spectral filter and equation (17)

Spectral filter `f_δ(H) = U diag(f_δ(λᵢ)) Uᴴ` of a Hermitian matrix, its rational
form `δ H (H² + δ² I)⁻¹`, and the block identity (17) for the dilation
`H = (1/3) [[0, A], [Aᴴ, 0]]`:

  `⟨1| f_{λ/3}(H) |0⟩ = λ Aᴴ (A Aᴴ + λ² I)⁻¹ = λ B_λ`.
-/

set_option maxHeartbeats 800000

noncomputable section

open scoped ComplexOrder ComplexConjugate

namespace Paper25

variable {m : ℕ}

/-- Square complex matrices indexed by a sum type (2-block form). -/
abbrev Block2 (m : ℕ) := Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) ℂ

/-! ## Spectral filter -/

/-- Spectral filter of a Hermitian matrix `H`:
`f_δ(H) = U diag(f_δ(λᵢ)) Uᴴ` where `H = U diag(λᵢ) Uᴴ`. -/
noncomputable def filterMat {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (δ : ℝ) :
    Matrix n n ℂ :=
  ((hH.eigenvectorUnitary : Matrix n n ℂ)
    * Matrix.diagonal (fun i => ((filterFn δ (hH.eigenvalues i) : ℝ) : ℂ))
    * star (hH.eigenvectorUnitary : Matrix n n ℂ))

/-- The spectral representation `f_δ(H) = U diag(f_δ(λᵢ)) Uᴴ`. -/
theorem filterMat_eq_spectral {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (δ : ℝ) :
    filterMat H hH δ =
      (hH.eigenvectorUnitary : Matrix n n ℂ)
        * Matrix.diagonal (fun i => ((filterFn δ (hH.eigenvalues i) : ℝ) : ℂ))
        * star (hH.eigenvectorUnitary : Matrix n n ℂ) :=
  rfl

/-- Spectral theorem for a Hermitian matrix. -/
theorem spectral_of_isHermitian {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    H =
      (hH.eigenvectorUnitary : Matrix n n ℂ)
        * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)
        * star (hH.eigenvectorUnitary : Matrix n n ℂ) :=
  hH.spectral_theorem

/-- Rational form of the spectral filter `f_δ(H) = δ H (H² + δ² I)⁻¹`. -/
noncomputable def filterRat {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (δ : ℝ) : Matrix n n ℂ :=
  ((δ : ℝ) : ℂ) • H * (H * H + (((δ ^ 2 : ℝ)) : ℂ) • (1 : Matrix n n ℂ))⁻¹

/-! ## Agreement of the spectral and rational definitions -/

lemma unitary_conjugate_mul {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (X Y : Matrix n n ℂ) :
    (U * X * star U) * (U * Y * star U) = U * (X * Y) * star U := by
  calc
    _ = U * X * (star U * U) * Y * star U := by noncomm_ring
    _ = _ := by rw [hU.1]; simp only [mul_one, mul_assoc]

lemma unitary_conjugate_inv {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (D : Matrix n n ℂ) (hD : IsUnit D.det) :
    (U * D * star U)⁻¹ = U * D⁻¹ * star U := by
  apply Matrix.inv_eq_right_inv
  rw [unitary_conjugate_mul U hU, Matrix.mul_nonsing_inv D hD]
  simpa only [mul_one] using hU.2

/-- The filter defined by the spectral theorem is the rational expression in Lemma 5.
The positivity of δ supplies invertibility, rather than assuming the inverse identity. -/
theorem filterMat_eq_filterRat {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (δ : ℝ) (hδ : 0 < δ) :
    filterMat H hH δ = filterRat H δ := by
  classical
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  let e : n → ℝ := hH.eigenvalues
  have hU : U ∈ Matrix.unitaryGroup n ℂ := hH.eigenvectorUnitary.property
  have hs : H = U * Matrix.diagonal (fun i => (e i : ℂ)) * star U :=
    hH.spectral_theorem
  have hd (i : n) : (e i : ℂ) ^ 2 + (δ : ℂ) ^ 2 ≠ 0 := by
    have hr : (e i) ^ 2 + δ ^ 2 ≠ 0 := by
      positivity
    exact_mod_cast hr
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (e i : ℂ) ^ 2 + (δ : ℂ) ^ 2)
  have hD : IsUnit D.det := by
    rw [isUnit_iff_ne_zero, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  have hden : H * H + ((δ ^ 2 : ℝ) : ℂ) • 1 = U * D * star U := by
    rw [hs, unitary_conjugate_mul U hU]
    have hid : (1 : Matrix n n ℂ) = U * 1 * star U := by
      simpa only [mul_one] using hU.2.symm
    calc
      _ = U * (Matrix.diagonal (fun i => (e i : ℂ)) *
          Matrix.diagonal (fun i => (e i : ℂ))) * star U +
          ((δ ^ 2 : ℝ) : ℂ) • (U * 1 * star U) := by rw [← hid]
      _ = U * (Matrix.diagonal (fun i => (e i : ℂ)) *
          Matrix.diagonal (fun i => (e i : ℂ)) + ((δ ^ 2 : ℝ) : ℂ) • 1) * star U := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul]
      _ = U * D * star U := by
        congr 2
        ext i j
        by_cases hij : i = j
        · subst j; simp [D, Matrix.diagonal_mul_diagonal, Matrix.one_apply, pow_two]
        · simp [D, Matrix.diagonal_mul_diagonal, Matrix.one_apply, hij]
  have hnum : (δ : ℂ) • H =
      U * Matrix.diagonal (fun i => (δ : ℂ) * (e i : ℂ)) * star U := by
    rw [hs]
    change (δ : ℂ) • (U * Matrix.diagonal (fun i => (e i : ℂ)) * star U) =
      U * Matrix.diagonal ((δ : ℂ) • (fun i => (e i : ℂ))) * star U
    rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  unfold filterRat
  rw [hden, hnum, unitary_conjugate_inv U hU D hD,
    unitary_conjugate_mul U hU]
  unfold filterMat
  change U * Matrix.diagonal (fun i => ((filterFn δ (e i) : ℝ) : ℂ)) * star U = _
  congr 2
  rw [Matrix.inv_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have hfun : IsUnit (fun i => (e i : ℂ) ^ 2 + (δ : ℂ) ^ 2) :=
    Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (hd i))
  have hinv : Ring.inverse (fun i => (e i : ℂ) ^ 2 + (δ : ℂ) ^ 2) =
      (fun i => (e i : ℂ) ^ 2 + (δ : ℂ) ^ 2)⁻¹ := by
    rw [← hfun.unit_spec, Ring.inverse_unit, Units.val_inv_eq_inv_val]
  rw [hinv]
  simp only [Pi.inv_apply, filterFn,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.ofReal_inv, div_eq_mul_inv]

/-! ## The dilation `[[0, A], [Aᴴ, 0]]` -/

/-- Off-diagonal dilation `[[0, A], [Aᴴ, 0]]` on `Fin m ⊕ Fin m`. -/
def dilation (A : Matrix (Fin m) (Fin m) ℂ) : Block2 m :=
  Matrix.fromBlocks 0 A A.conjTranspose 0

lemma dilation_mul_self (A : Matrix (Fin m) (Fin m) ℂ) :
    dilation A * dilation A
      = Matrix.fromBlocks (A * A.conjTranspose) 0 0 (A.conjTranspose * A) := by
  unfold dilation
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

lemma dilation_isHermitian (A : Matrix (Fin m) (Fin m) ℂ) :
    (dilation A).IsHermitian := by
  show (dilation A).conjTranspose = dilation A
  unfold dilation
  rw [Matrix.fromBlocks_conjTranspose]
  simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_conjTranspose]

/-! ## Block-diagonal inverses -/

lemma fromBlocks_one :
    Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin m) (Fin m) ℂ)
      (0 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) = (1 : Block2 m) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

/-- Inverse of a block-diagonal matrix is the block diagonal of inverses. -/
lemma inv_fromBlocks_diagonal (P Q : Matrix (Fin m) (Fin m) ℂ)
    (hP : IsUnit P) (hQ : IsUnit Q) :
    (Matrix.fromBlocks P (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q : Block2 m)⁻¹
      = Matrix.fromBlocks P⁻¹ (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q⁻¹ := by
  classical
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hQdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have hdetM : IsUnit (Matrix.fromBlocks P (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q : Block2 m).det := by
    rw [Matrix.det_fromBlocks_zero₁₂]
    exact hPdet.mul hQdet
  have hmul : (Matrix.fromBlocks P (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q : Block2 m)
      * Matrix.fromBlocks P⁻¹ (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q⁻¹ = 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [Matrix.mul_nonsing_inv P hPdet, Matrix.mul_nonsing_inv Q hQdet]
    exact fromBlocks_one
  have hinv : (Matrix.fromBlocks P (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q : Block2 m)⁻¹
      * (Matrix.fromBlocks P (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q : Block2 m) = 1 :=
    Matrix.nonsing_inv_mul _ hdetM
  have hN : (Matrix.fromBlocks P⁻¹ (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q⁻¹)
      = (Matrix.fromBlocks P (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q : Block2 m)⁻¹ := by
    calc (Matrix.fromBlocks P⁻¹ (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q⁻¹)
        = 1 * (Matrix.fromBlocks P⁻¹ (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q⁻¹) :=
          (one_mul _).symm
      _ = ((Matrix.fromBlocks P (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q : Block2 m)⁻¹
          * (Matrix.fromBlocks P (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q : Block2 m))
          * (Matrix.fromBlocks P⁻¹ (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q⁻¹) := by
          rw [hinv]
      _ = (Matrix.fromBlocks P (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q : Block2 m)⁻¹
          * ((Matrix.fromBlocks P (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q : Block2 m)
            * (Matrix.fromBlocks P⁻¹ (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q⁻¹)) := by
          rw [mul_assoc]
      _ = (Matrix.fromBlocks P (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q : Block2 m)⁻¹ * 1 := by
          rw [hmul]
      _ = (Matrix.fromBlocks P (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q : Block2 m)⁻¹ := by
          rw [mul_one]
  exact hN.symm

/-- Scalar rescaling of a matrix inverse: `(c • A)⁻¹ = c⁻¹ • A⁻¹` when `c ≠ 0`. -/
lemma inv_smul_eq (c : ℂ) (A : Matrix (Fin m) (Fin m) ℂ) (hc : c ≠ 0)
    (hA : IsUnit A) : (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hInv : Invertible c := invertibleOfNonzero hc
  rw [Matrix.inv_smul A c hAdet]
  congr 1
  exact invOf_eq_inv c

/-! ## Equation (17) -/

/-- Regularized inverse `B_λ = Aᴴ (A Aᴴ + λ² I)⁻¹`. -/
noncomputable def bLam (A : Matrix (Fin m) (Fin m) ℂ) (lam : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  A.conjTranspose
    * (A * A.conjTranspose + (((lam ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹

/-- Helper: `(1/9) • (A Aᴴ) + (λ/3)² • I = (1/9) • (A Aᴴ + λ² I)`. -/
lemma smul_gram_add_sq (A : Matrix (Fin m) (Fin m) ℂ) (lam : ℝ) :
    (((1 / 9 : ℝ) : ℂ) • (A * A.conjTranspose)
      + (((lam / 3 : ℝ) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ))
      = ((1 / 9 : ℝ) : ℂ) • (A * A.conjTranspose
        + (((lam ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) := by
  rw [smul_add, smul_smul]
  have hδsq : (((lam / 3 : ℝ) ^ 2 : ℝ) : ℂ) = ((1 / 9 : ℝ) : ℂ) * (((lam ^ 2 : ℝ)) : ℂ) := by
    push_cast
    rw [div_pow]
    field_simp
    ring
  rw [hδsq]

/-- Helper: `(1/9) • (A ᴴ A) + (λ/3)² • I = (1/9) • (A ᴴ A + λ² I)`. -/
lemma smul_gram_add_sq' (A : Matrix (Fin m) (Fin m) ℂ) (lam : ℝ) :
    (((1 / 9 : ℝ) : ℂ) • (A.conjTranspose * A)
      + (((lam / 3 : ℝ) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ))
      = ((1 / 9 : ℝ) : ℂ) • (A.conjTranspose * A
        + (((lam ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) := by
  rw [smul_add, smul_smul]
  have hδsq : (((lam / 3 : ℝ) ^ 2 : ℝ) : ℂ) = ((1 / 9 : ℝ) : ℂ) * (((lam ^ 2 : ℝ)) : ℂ) := by
    push_cast
    rw [div_pow]
    field_simp
    ring
  rw [hδsq]

/-- Helper: a nonzero scalar times a unit matrix is a unit. -/
lemma isUnit_smul_of_isUnit (c : ℂ) (M : Matrix (Fin m) (Fin m) ℂ) (hc : c ≠ 0)
    (hM : IsUnit M) : IsUnit (c • M) := by
  have hAdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have h : (c • M) * (c⁻¹ • M⁻¹) = 1 := by
    have h1 : (c • M) * (c⁻¹ • M⁻¹) = (c * c⁻¹) • (M * M⁻¹) := by
      rw [smul_mul_smul]
    rw [h1, Matrix.mul_nonsing_inv M hAdet, mul_inv_cancel₀ hc, one_smul]
  have h2 : (c⁻¹ • M⁻¹) * (c • M) = 1 := by
    have h3 : (c⁻¹ • M⁻¹) * (c • M) = (c⁻¹ * c) • (M⁻¹ * M) := by
      rw [smul_mul_smul]
    rw [h3, Matrix.nonsing_inv_mul M hAdet, inv_mul_cancel₀ hc, one_smul]
  exact ⟨⟨c • M, c⁻¹ • M⁻¹, h, h2⟩, rfl⟩

/-- Helper: Gram + positive scalar is invertible. -/
lemma isUnit_gram_add (A : Matrix (Fin m) (Fin m) ℂ) (lam : ℝ) (hlam : 0 < lam) :
    IsUnit (A * A.conjTranspose
      + (((lam ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) := by
  have hAAsd : (A * A.conjTranspose).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  have hIdef : (((((lam ^ 2 : ℝ) : ℂ)) • (1 : Matrix (Fin m) (Fin m) ℂ))).PosDef := by
    have hpos : (0 : ℝ) < lam ^ 2 := sq_pos_of_ne_zero hlam.ne'
    exact Matrix.PosDef.one.smul (by exact_mod_cast hpos)
  have hsum : (A * A.conjTranspose
      + (((lam ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)).PosDef := by
    have h1 : (((((lam ^ 2 : ℝ) : ℂ)) • (1 : Matrix (Fin m) (Fin m) ℂ))
        + A * A.conjTranspose).PosDef := hIdef.add_posSemidef hAAsd
    rw [add_comm] at h1
    exact h1
  exact hsum.isUnit

/-- Helper: `A ᴴ A + λ² I` is invertible. -/
lemma isUnit_gram_add' (A : Matrix (Fin m) (Fin m) ℂ) (lam : ℝ) (hlam : 0 < lam) :
    IsUnit (A.conjTranspose * A
      + (((lam ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) := by
  have hAAHsd : (A.conjTranspose * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have hIdef : (((((lam ^ 2 : ℝ) : ℂ)) • (1 : Matrix (Fin m) (Fin m) ℂ))).PosDef := by
    have hpos : (0 : ℝ) < lam ^ 2 := sq_pos_of_ne_zero hlam.ne'
    exact Matrix.PosDef.one.smul (by exact_mod_cast hpos)
  have hsum : (A.conjTranspose * A
      + (((lam ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)).PosDef := by
    have h1 : (((((lam ^ 2 : ℝ) : ℂ)) • (1 : Matrix (Fin m) (Fin m) ℂ))
        + A.conjTranspose * A).PosDef := hIdef.add_posSemidef hAAHsd
    rw [add_comm] at h1
    exact h1
  exact hsum.isUnit

/-- Regularized inverse agrees with `bLam`. -/
theorem bLam_eq_regInv (A : Matrix (Fin m) (Fin m) ℂ) (lam : ℝ) :
    bLam A lam = A.conjTranspose
      * (A * A.conjTranspose
        + (((lam ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ :=
  rfl

/-- Invertibility of `A Aᴴ + λ² I` used by the filter. -/
theorem isUnit_filter_gram (A : Matrix (Fin m) (Fin m) ℂ) (lam : ℝ) (hlam : 0 < lam) :
    IsUnit (A * A.conjTranspose
      + (((lam ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) :=
  isUnit_gram_add A lam hlam

/-- Invertibility of `A ᴴ A + λ² I` used by the filter. -/
theorem isUnit_filter_gram' (A : Matrix (Fin m) (Fin m) ℂ) (lam : ℝ) (hlam : 0 < lam) :
    IsUnit (A.conjTranspose * A
      + (((lam ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) :=
  isUnit_gram_add' A lam hlam

/-- Scaled dilation identity underlying equation (17). -/
theorem smul_dilation_scale (A : Matrix (Fin m) (Fin m) ℂ) :
    ((1 / 3 : ℝ) : ℂ) • dilation A
      = Matrix.fromBlocks 0 (((1 / 3 : ℝ) : ℂ) • A)
          (((1 / 3 : ℝ) : ℂ) • A.conjTranspose) 0 := by
  unfold dilation
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.smul_apply]

/-- Equation (17): the lower-left block of the filter of the dilation equals `lam • B_λ`. -/
theorem filter_dilation_block (A : Matrix (Fin m) (Fin m) ℂ) (lam : ℝ) (hlam : 0 < lam) :
    (filterRat (((1 / 3 : ℝ) : ℂ) • dilation A) (lam / 3)).toBlocks₂₁
      = (((lam : ℝ)) : ℂ) • bLam A lam := by
  classical
  -- Unfold the rational filter
  have hFR : filterRat (((1 / 3 : ℝ) : ℂ) • dilation A) (lam / 3)
      = (((lam / 3 : ℝ)) : ℂ) • (((1 / 3 : ℝ) : ℂ) • dilation A)
          * (((((1 / 3 : ℝ) : ℂ) • dilation A) * (((1 / 3 : ℝ) : ℂ) • dilation A)
              + (((((lam / 3 : ℝ) ^ 2 : ℝ)) : ℂ) • (1 : Block2 m))))⁻¹ := by
    unfold filterRat
    rfl
  rw [hFR]
  -- Squaring the scaled dilation
  have hsq : ((((1 / 3 : ℝ) : ℂ) • dilation A)
      * (((1 / 3 : ℝ) : ℂ) • dilation A))
      = (((1 / 9 : ℝ) : ℂ) •
        Matrix.fromBlocks (A * A.conjTranspose) 0 0 (A.conjTranspose * A)) := by
    rw [smul_mul_smul, dilation_mul_self]
    have h33 : ((1 / 3 : ℝ) : ℂ) * ((1 / 3 : ℝ) : ℂ) = ((1 / 9 : ℝ) : ℂ) := by
      norm_num
    rw [h33, Matrix.fromBlocks_smul]
  -- H² + δ² I is block diagonal
  have hHH : ((((1 / 3 : ℝ) : ℂ) • dilation A)
      * (((1 / 3 : ℝ) : ℂ) • dilation A)
      + (((((lam / 3 : ℝ) ^ 2 : ℝ)) : ℂ) • (1 : Block2 m)))
      = Matrix.fromBlocks
          (((1 / 9 : ℝ) : ℂ) • (A * A.conjTranspose)
            + (((lam / 3 : ℝ) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ))
          0 0
          (((1 / 9 : ℝ) : ℂ) • (A.conjTranspose * A)
            + (((lam / 3 : ℝ) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) := by
    rw [hsq]
    have hI : (((((lam / 3 : ℝ) ^ 2 : ℝ)) : ℂ) • (1 : Block2 m))
        = Matrix.fromBlocks
            (((((lam / 3 : ℝ) ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ))
            0 0
            (((((lam / 3 : ℝ) ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.smul_apply]
    -- Expand the scaled block and combine
    have hsmul : (((1 / 9 : ℝ) : ℂ) • Matrix.fromBlocks (A * A.conjTranspose) 0 0
          (A.conjTranspose * A))
        = Matrix.fromBlocks (((1 / 9 : ℝ) : ℂ) • (A * A.conjTranspose)) 0 0
          (((1 / 9 : ℝ) : ℂ) • (A.conjTranspose * A)) :=
      by simpa only [Matrix.fromBlocks_smul, smul_zero]
    rw [hI, hsmul, Matrix.fromBlocks_add]
    simp only [zero_add]
  rw [hHH]
  -- Invertibility of the two diagonal blocks
  have hGAA := isUnit_gram_add A lam hlam
  have hGAH := isUnit_gram_add' A lam hlam
  have hPform := smul_gram_add_sq A lam
  have hQform := smul_gram_add_sq' A lam
  set P : Matrix (Fin m) (Fin m) ℂ
      := ((1 / 9 : ℝ) : ℂ) • (A * A.conjTranspose)
          + (((lam / 3 : ℝ) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) with hPeq
  set Q : Matrix (Fin m) (Fin m) ℂ
      := ((1 / 9 : ℝ) : ℂ) • (A.conjTranspose * A)
          + (((lam / 3 : ℝ) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) with hQeq
  have hPunit : IsUnit P := by
    rw [hPform]
    exact isUnit_smul_of_isUnit _ _ (by norm_num) hGAA
  have hQunit : IsUnit Q := by
    rw [hQform]
    exact isUnit_smul_of_isUnit _ _ (by norm_num) hGAH
  rw [inv_fromBlocks_diagonal _ _ hPunit hQunit]
  -- Multiply and extract the lower-left block
  have hprod : (((lam / 3 : ℝ)) : ℂ) • (((1 / 3 : ℝ) : ℂ) • dilation A)
        * Matrix.fromBlocks P⁻¹ (0 : Matrix (Fin m) (Fin m) ℂ) 0 Q⁻¹
      = (((lam / 9 : ℝ)) : ℂ) •
          Matrix.fromBlocks 0 (A * Q⁻¹) (A.conjTranspose * P⁻¹) 0 := by
    have h1 : (((lam / 3 : ℝ)) : ℂ) • (((1 / 3 : ℝ) : ℂ) • dilation A)
        = (((lam / 9 : ℝ)) : ℂ) • dilation A := by
      rw [smul_smul]
      congr 1
      push_cast
      ring
    rw [h1]
    unfold dilation
    rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    simp only [Matrix.fromBlocks_smul, smul_zero, Matrix.smul_mul, Matrix.zero_mul]
  rw [hprod]
  have hblocks : (Matrix.fromBlocks 0 (A * Q⁻¹) (A.conjTranspose * P⁻¹) 0).toBlocks₂₁
      = A.conjTranspose * P⁻¹ := by
    simp [Matrix.toBlocks_fromBlocks₂₁]
  change (((lam / 9 : ℝ)) : ℂ) •
    (Matrix.fromBlocks 0 (A * Q⁻¹) (A.conjTranspose * P⁻¹) 0).toBlocks₂₁ = _
  rw [hblocks]
  -- Express P⁻¹ via the unscaled Gram matrix
  have hPinv : P⁻¹ = ((9 : ℝ) : ℂ) • (A * A.conjTranspose
      + (((lam ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ := by
    rw [hPform, inv_smul_eq _ _ (by norm_num) hGAA]
    norm_num
  rw [hPinv]
  -- Final scalar arithmetic: (λ/9) • (Aᴴ * (9 • G⁻¹)) = λ • (Aᴴ * G⁻¹)
  have hcalc : (((lam / 9 : ℝ)) : ℂ) • (A.conjTranspose
        * (((9 : ℝ) : ℂ) • (A * A.conjTranspose
            + (((lam ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹))
      = (((lam : ℝ)) : ℂ) • (A.conjTranspose
        * (A * A.conjTranspose
            + (((lam ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹) := by
    rw [Matrix.mul_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [hcalc]
  show (((lam : ℝ)) : ℂ) • (A.conjTranspose
      * (A * A.conjTranspose + (((lam ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹)
    = (((lam : ℝ)) : ℂ) • bLam A lam
  rfl

/-- The history dilation in equation (13) is Hermitian. -/
lemma scaled_dilation_isHermitian (A : Matrix (Fin m) (Fin m) ℂ) :
    (((1 / 3 : ℝ) : ℂ) • dilation A).IsHermitian := by
  show (((1 / 3 : ℝ) : ℂ) • dilation A).conjTranspose = _
  rw [Matrix.conjTranspose_smul, dilation_isHermitian]
  norm_num

/-- Equation (17) for the spectral filter itself, linked to the rational
matrix expression by the proved spectral theorem calculation above. -/
theorem filter_dilation_spectral_block (A : Matrix (Fin m) (Fin m) ℂ)
    (lam : ℝ) (hlam : 0 < lam) :
    (filterMat (((1 / 3 : ℝ) : ℂ) • dilation A)
      (scaled_dilation_isHermitian A) (lam / 3)).toBlocks₂₁ =
      (lam : ℂ) • bLam A lam := by
  rw [filterMat_eq_filterRat _ _ _ (by positivity)]
  exact filter_dilation_block A lam hlam

end Paper25
