import Paper25.Norms
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Lemma 4: Nuclear-norm regularization

For invertible `A` and `lam > 0`, with `B_λ = A† (A A† + lam² I)⁻¹`,

  `‖A⁻¹ - B_λ‖_1 ≤ (lam / 2) ‖A⁻¹‖_F²`.

The proof diagonalizes the Gram matrix `A A†` via the spectral theorem, writes
`A⁻¹ - B_λ = A† G` with `G` a function of `A A†`, and evaluates the nuclear
norm through the eigenvalues of the Gram matrix of `A⁻¹ - B_λ`.
-/

noncomputable section

open scoped ComplexOrder ComplexConjugate

open Polynomial

namespace Paper25

variable {m : ℕ}

/-! ## Regularized inverse -/

/-- Regularized inverse `B_λ = A† (A A† + λ² I)⁻¹`. -/
def regInv (A : Matrix (Fin m) (Fin m) ℂ) (lam : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  A.conjTranspose * (A * A.conjTranspose + lam ^ 2 • 1)⁻¹

/-- Difference `A⁻¹ - B_λ`. -/
def regDiff (A : Matrix (Fin m) (Fin m) ℂ) (lam : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  A⁻¹ - regInv A lam

lemma regInv_eq (A : Matrix (Fin m) (Fin m) ℂ) (lam : ℝ) :
    regInv A lam = A.conjTranspose * (A * A.conjTranspose + lam ^ 2 • 1)⁻¹ :=
  rfl

lemma regDiff_eq (A : Matrix (Fin m) (Fin m) ℂ) (lam : ℝ) :
    regDiff A lam = A⁻¹ - A.conjTranspose * (A * A.conjTranspose + lam ^ 2 • 1)⁻¹ := by
  rfl

/-! ## Scalar form of Lemma 4 -/

/-- Singular-value form of Lemma 4. -/
theorem lemma_4_singular_value_form (σ : Fin m → ℝ) (hσ : ∀ i, 0 < σ i) (lam : ℝ)
    (hlam : 0 < lam) :
    (∑ i, |1 / σ i - σ i / (σ i ^ 2 + lam ^ 2)|) ≤ (lam / 2) * ∑ i, 1 / (σ i ^ 2) := by
  have hsum : (∑ i, |1 / σ i - σ i / (σ i ^ 2 + lam ^ 2)|)
      = ∑ i, (lam ^ 2 / (σ i * (σ i ^ 2 + lam ^ 2))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inv_sub_regularized (σ i) lam (hσ i) hlam]
    have hnn : 0 ≤ lam ^ 2 / (σ i * (σ i ^ 2 + lam ^ 2)) := by
      have hprod : 0 < σ i * (σ i ^ 2 + lam ^ 2) := by
        have hs : 0 < σ i := hσ i
        have hsq : 0 < σ i ^ 2 + lam ^ 2 := by positivity
        positivity
      positivity
    rw [abs_of_nonneg hnn]
  rw [hsum]
  exact nuclear_reg_sum_bound σ hσ lam hlam

/-! ## Hermitian real diagonals and their eigenvalues -/

lemma isSelfAdjoint_ofReal (r : ℝ) : IsSelfAdjoint (r : ℂ) := by
  simp [IsSelfAdjoint, Complex.conj_ofReal]

lemma isHermitian_ofReal_diagonal (d : Fin m → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ)) : Matrix (Fin m) (Fin m) ℂ).IsHermitian := by
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  exact isSelfAdjoint_ofReal _

/-- Roots of the characteristic polynomial of a real diagonal. -/
lemma roots_charpoly_ofReal_diagonal (d : Fin m → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ)) : Matrix (Fin m) (Fin m) ℂ).charpoly.roots
      = Multiset.map Complex.ofReal (Multiset.map d Finset.univ.val) := by
  have hchar := Matrix.charpoly_diagonal (fun i : Fin m => (d i : ℂ))
  rw [hchar]
  have hprod : (∏ i : Fin m, (X - C (d i : ℂ) : ℂ[X]))
      = (Multiset.map (fun i : Fin m => (X - C (d i : ℂ) : ℂ[X])) Finset.univ.val).prod := by
    rw [Finset.prod_eq_multiset_prod]
  rw [hprod]
  have hmap : Multiset.map (fun i : Fin m => (X - C (d i : ℂ) : ℂ[X])) Finset.univ.val
      = Multiset.map (fun a : ℂ => X - C a)
          (Multiset.map Complex.ofReal (Multiset.map d Finset.univ.val)) := by
    simp only [Multiset.map_map, Function.comp_apply]
  rw [hmap, Polynomial.roots_multiset_prod_X_sub_C]

/-- Multiset of eigenvalues of a real diagonal equals the diagonal entries. -/
lemma map_eigenvalues_ofReal_diagonal (d : Fin m → ℝ) :
    Multiset.map (isHermitian_ofReal_diagonal d).eigenvalues Finset.univ.val
      = Multiset.map d Finset.univ.val := by
  have hroots : (Matrix.diagonal (fun i => (d i : ℂ)) : Matrix (Fin m) (Fin m) ℂ).charpoly.roots
      = Multiset.map ((↑) ∘ (isHermitian_ofReal_diagonal d).eigenvalues) Finset.univ.val :=
    (isHermitian_ofReal_diagonal d).roots_charpoly_eq_eigenvalues
  have hdiag := roots_charpoly_ofReal_diagonal d
  have hcomp : Multiset.map (Complex.ofReal ∘ (isHermitian_ofReal_diagonal d).eigenvalues)
        Finset.univ.val
      = Multiset.map Complex.ofReal (Multiset.map d Finset.univ.val) := by
    rw [← hroots, ← hdiag]
  have hcomp2 : Multiset.map Complex.ofReal
        (Multiset.map (isHermitian_ofReal_diagonal d).eigenvalues Finset.univ.val)
      = Multiset.map Complex.ofReal (Multiset.map d Finset.univ.val) := by
    simpa [Multiset.map_map] using hcomp
  have hre : ∀ (s t : Multiset ℝ),
      Multiset.map Complex.ofReal s = Multiset.map Complex.ofReal t → s = t := by
    intro s t h
    have := congr_arg (Multiset.map Complex.re) h
    simpa [Complex.ofReal_re] using this
  exact hre _ _ hcomp2

/-- Sum of a function of eigenvalues of a real diagonal. -/
lemma sum_f_eigenvalues_ofReal_diagonal (d : Fin m → ℝ) (f : ℝ → ℝ) :
    (∑ i, f ((isHermitian_ofReal_diagonal d).eigenvalues i)) = ∑ i, f (d i) := by
  have hm := map_eigenvalues_ofReal_diagonal d
  have h1 : (∑ i, f ((isHermitian_ofReal_diagonal d).eigenvalues i))
      = (Multiset.map (fun i => f ((isHermitian_ofReal_diagonal d).eigenvalues i))
          Finset.univ.val).sum := by
    simp only [Finset.sum_eq_multiset_sum]
  have h2 : (∑ i, f (d i))
      = (Multiset.map (fun i => f (d i)) Finset.univ.val).sum := by
    simp only [Finset.sum_eq_multiset_sum]
  rw [h1, h2]
  have h3 : Multiset.map (fun i => f ((isHermitian_ofReal_diagonal d).eigenvalues i))
        Finset.univ.val
      = Multiset.map (fun i => f (d i)) Finset.univ.val := by
    have := congr_arg (Multiset.map f) hm
    simpa [Multiset.map_map] using this
  rw [h3]

/-! ## Unitary conjugation -/

/-- Characteristic polynomial is invariant under unitary conjugation. -/
lemma charpoly_unitary_conj (U N : Matrix (Fin m) (Fin m) ℂ) (hU : U * U.conjTranspose = 1) :
    (U * N * U.conjTranspose).charpoly = N.charpoly := by
  let u : Matrix.unitaryGroup (Fin m) ℂ := ⟨U, Matrix.mem_unitaryGroup_iff.mpr (by
    simpa using hU)⟩
  have hval : (unitary.toUnits u).val = U := rfl
  have hinv : ((unitary.toUnits u)⁻¹ : (Matrix (Fin m) (Fin m) ℂ)ˣ).val = U.conjTranspose := by
    show star (u : Matrix (Fin m) (Fin m) ℂ) = U.conjTranspose
    rfl
  have := Matrix.charpoly_units_conj (unitary.toUnits u) N
  -- this : ((toUnits u).val * N * (toUnits u)⁻¹.val).charpoly = N.charpoly
  simpa [hval, hinv, Matrix.mul_assoc] using this

/-- Hermitian matrix `U D U†` for a real diagonal `D` and unitary `U`. -/
lemma isHermitian_unitary_conj_diagonal (U : Matrix (Fin m) (Fin m) ℂ) (hU : U * U.conjTranspose = 1)
    (d : Fin m → ℝ) :
    (U * Matrix.diagonal (fun i => (d i : ℂ)) * U.conjTranspose).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose U (isHermitian_ofReal_diagonal d)

/-- Eigenvalue sums of a unitary conjugate of a real diagonal. -/
lemma sum_f_eigenvalues_unitary_conj_diagonal (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U * U.conjTranspose = 1) (d : Fin m → ℝ) (f : ℝ → ℝ) :
    (∑ i, f ((isHermitian_unitary_conj_diagonal U hU d).eigenvalues i)) = ∑ i, f (d i) := by
  have hchar := charpoly_unitary_conj U (Matrix.diagonal (fun i => (d i : ℂ))) hU
  have heq := Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
    (isHermitian_unitary_conj_diagonal U hU d) (isHermitian_ofReal_diagonal d)
  have hfun : (isHermitian_unitary_conj_diagonal U hU d).eigenvalues
      = (isHermitian_ofReal_diagonal d).eigenvalues :=
    heq.mpr hchar
  rw [hfun]
  exact sum_f_eigenvalues_ofReal_diagonal d f

/-! ## Nuclear norm of a Gram matrix -/

lemma nuclearNorm_eq_sum_sqrt (X : Matrix (Fin m) (Fin m) ℂ) :
    nuclearNorm X = ∑ i, Real.sqrt (singValsSq X i) :=
  rfl

lemma singValsSq_eq_eigenvalues_gram (X : Matrix (Fin m) (Fin m) ℂ) :
    singValsSq X = (gram_isHermitian X).eigenvalues :=
  rfl

/-! ## Inverse identity `A⁻¹ = A† (A A†)⁻¹` -/

lemma isUnit_conjTranspose {A : Matrix (Fin m) (Fin m) ℂ} (hA : IsUnit A) :
    IsUnit A.conjTranspose :=
  (Matrix.isUnit_conjTranspose A).mpr hA

lemma isUnit_self_mul_conjTranspose {A : Matrix (Fin m) (Fin m) ℂ} (hA : IsUnit A) :
    IsUnit (A * A.conjTranspose) :=
  hA.mul (isUnit_conjTranspose hA)

/-- For invertible `A`, one has `A⁻¹ = A† (A A†)⁻¹`. -/
lemma inv_eq_adjoint_mul {A : Matrix (Fin m) (Fin m) ℂ} (hA : IsUnit A) :
    A⁻¹ = A.conjTranspose * (A * A.conjTranspose)⁻¹ := by
  have hAT : IsUnit A.conjTranspose := isUnit_conjTranspose hA
  have hH : IsUnit (A * A.conjTranspose) := isUnit_self_mul_conjTranspose hA
  have hAA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hHH : IsUnit (A * A.conjTranspose).det :=
    (Matrix.isUnit_iff_isUnit_det (A * A.conjTranspose)).mp hH
  have hmul : A * A.conjTranspose * (A * A.conjTranspose)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hHH
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hAA
  calc
    A⁻¹ = A⁻¹ * 1 := (mul_one _).symm
    _ = A⁻¹ * (A * A.conjTranspose * (A * A.conjTranspose)⁻¹) := by rw [hmul]
    _ = (A⁻¹ * A) * A.conjTranspose * (A * A.conjTranspose)⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = 1 * A.conjTranspose * (A * A.conjTranspose)⁻¹ := by rw [hinv]
    _ = A.conjTranspose * (A * A.conjTranspose)⁻¹ := by rw [one_mul]


/-! ## Frobenius norm of the inverse and nuclear norm of the difference -/

lemma frobNormSq_eq_trace_gram (X : Matrix (Fin m) (Fin m) ℂ) :
    frobNormSq X = ((gram X).trace).re := by
  classical
  have hentry : ∀ i, ((gram X) i i : ℂ) = ((∑ k, Complex.normSq (X k i) : ℝ) : ℂ) := by
    intro i
    simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have h : ∀ k : Fin m, star (X k i) * X k i = ((Complex.normSq (X k i) : ℝ) : ℂ) := by
      intro k
      show (starRingEnd ℂ) (X k i) * X k i = _
      rw [mul_comm, Complex.mul_conj]
    simp only [h, ← Complex.ofReal_sum]
  have htrace : (gram X).trace = ∑ i, (gram X) i i := by
    simp [Matrix.trace, Matrix.diag]
  rw [htrace]
  have hmap : (∑ i, (gram X) i i).re = ∑ i, ((gram X) i i).re :=
    map_sum (Complex.reAddGroupHom) _ _
  rw [hmap]
  simp only [hentry, Complex.ofReal_re]
  rw [Finset.sum_comm]
  rfl

lemma frobNormSq_eq_sum_singValsSq (X : Matrix (Fin m) (Fin m) ℂ) :
    frobNormSq X = ∑ i, singValsSq X i := by
  classical
  have h1 : frobNormSq X = ((gram X).trace).re := frobNormSq_eq_trace_gram X
  have h2 : ((gram X).trace).re = ∑ i, (gram_isHermitian X).eigenvalues i := by
    have htrace := (gram_isHermitian X).trace_eq_sum_eigenvalues
    have hmap : ((gram X).trace).re
        = ∑ i, (((gram_isHermitian X).eigenvalues i : ℝ) : ℂ).re := by
      rw [htrace]
      exact map_sum (Complex.reAddGroupHom) _ _
    rw [hmap]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Complex.ofReal_re _
  rw [h1, h2, singValsSq_eq_eigenvalues_gram]

/-- For invertible `A`, all singular values are positive. -/
lemma singVals_pos_of_isUnit (A : Matrix (Fin m) (Fin m) ℂ) (hA : IsUnit A) (i : Fin m) :
    0 < singVals A i := by
  have hInj : Function.Injective (Matrix.mulVec A) :=
    (Matrix.mulVec_injective_iff_isUnit).mpr hA
  have hPos : (A.conjTranspose * A).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self A hInj
  have hpos := hPos.eigenvalues_pos i
  have hsq : 0 < singValsSq A i := by
    rw [singValsSq_eq_eigenvalues_gram]
    exact hpos
  exact Real.sqrt_pos.mpr hsq


/-- Gram of a product. -/
lemma gram_mul (X Y : Matrix (Fin m) (Fin m) ℂ) :
    gram (X * Y) = Y.conjTranspose * gram X * Y := by
  simp only [gram, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-! ## Unitary diagonalization of `A A†` -/

/-- Unitary eigenvector matrix of `A A†`. -/
noncomputable def leftSingUnitary (A : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.unitaryGroup (Fin m) ℂ :=
  (Matrix.isHermitian_mul_conjTranspose_self A).eigenvectorUnitary

lemma leftSing_mul_star (A : Matrix (Fin m) (Fin m) ℂ) :
    (leftSingUnitary A : Matrix (Fin m) (Fin m) ℂ)
      * (leftSingUnitary A : Matrix (Fin m) (Fin m) ℂ).conjTranspose = 1 := by
  have h := (leftSingUnitary A).2.2
  exact h

lemma leftSing_star_mul (A : Matrix (Fin m) (Fin m) ℂ) :
    (leftSingUnitary A : Matrix (Fin m) (Fin m) ℂ).conjTranspose
      * (leftSingUnitary A : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  have h := (leftSingUnitary A).2.1
  exact h

/-- Spectral form of `A A†`. -/
lemma self_mul_conjTranspose_spectral (A : Matrix (Fin m) (Fin m) ℂ) :
    A * A.conjTranspose
      = (leftSingUnitary A : Matrix (Fin m) (Fin m) ℂ)
        * Matrix.diagonal
            (fun i => ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues i : ℂ))
        * (leftSingUnitary A : Matrix (Fin m) (Fin m) ℂ).conjTranspose := by
  have h := (Matrix.isHermitian_mul_conjTranspose_self A).spectral_theorem
  simpa [leftSingUnitary] using h

/-- Inverse of a unitary conjugate of an invertible diagonal. -/
lemma inv_unitary_conj_diagonal (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (d : Fin m → ℂ) (hd : ∀ i, d i ≠ 0) :
    (U * Matrix.diagonal d * U.conjTranspose)⁻¹
      = U * Matrix.diagonal (fun i => (d i)⁻¹) * U.conjTranspose := by
  have hdiag : Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply, hd i]
    · simp [Matrix.diagonal_apply, hij]
  have hprod : (U * Matrix.diagonal d * U.conjTranspose)
        * (U * Matrix.diagonal (fun i => (d i)⁻¹) * U.conjTranspose) = 1 := by
    have h1 : (U * Matrix.diagonal d * U.conjTranspose)
          * (U * Matrix.diagonal (fun i => (d i)⁻¹) * U.conjTranspose)
        = U * (Matrix.diagonal d * (U.conjTranspose * U)
            * Matrix.diagonal (fun i => (d i)⁻¹)) * U.conjTranspose := by
      simp only [Matrix.mul_assoc]
    rw [h1, hU', Matrix.mul_one]
    calc U * (Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹)) * U.conjTranspose
        = U * 1 * U.conjTranspose := by rw [hdiag]
      _ = U * U.conjTranspose := by rw [Matrix.mul_one]
      _ = 1 := hU
  have hdet : IsUnit (U * Matrix.diagonal d * U.conjTranspose).det :=
    Matrix.isUnit_det_of_right_inverse hprod
  calc (U * Matrix.diagonal d * U.conjTranspose)⁻¹
      = (U * Matrix.diagonal d * U.conjTranspose)⁻¹ * 1 := (mul_one _).symm
    _ = (U * Matrix.diagonal d * U.conjTranspose)⁻¹
          * ((U * Matrix.diagonal d * U.conjTranspose)
              * (U * Matrix.diagonal (fun i => (d i)⁻¹) * U.conjTranspose)) := by rw [hprod]
    _ = U * Matrix.diagonal (fun i => (d i)⁻¹) * U.conjTranspose := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul]


/-! ## Matrix spectral calculus for the regularization estimate -/

/-- Conjugation of a real diagonal by a unitary matrix. -/
def realSpectral (U : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℂ :=
  U * Matrix.diagonal (fun i => (d i : ℂ)) * U.conjTranspose

lemma realSpectral_hermitian (U : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℝ) :
    (realSpectral U d).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose U (isHermitian_ofReal_diagonal d)

lemma realSpectral_mul (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U.conjTranspose * U = 1) (d e : Fin m → ℝ) :
    realSpectral U d * realSpectral U e = realSpectral U (fun i => d i * e i) := by
  unfold realSpectral
  calc
    _ = U * Matrix.diagonal (fun i => (d i : ℂ)) *
        (U.conjTranspose * U) * Matrix.diagonal (fun i => (e i : ℂ)) * U.conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal (fun i => (d i : ℂ)) *
        Matrix.diagonal (fun i => (e i : ℂ))) * U.conjTranspose := by
      rw [hU, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.diagonal_mul_diagonal]; simp only [Complex.ofReal_mul]

lemma realSpectral_sub (U : Matrix (Fin m) (Fin m) ℂ) (d e : Fin m → ℝ) :
    realSpectral U d - realSpectral U e = realSpectral U (fun i => d i - e i) := by
  unfold realSpectral
  simp only [Complex.ofReal_sub]
  rw [← Matrix.diagonal_sub (fun i => (d i : ℂ)) (fun i => (e i : ℂ)),
    Matrix.mul_sub, Matrix.sub_mul]

lemma nuclearNorm_of_gram_spectral (X U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U * U.conjTranspose = 1) (d : Fin m → ℝ)
    (hgram : gram X = realSpectral U d) :
    nuclearNorm X = ∑ i, Real.sqrt (d i) := by
  have heig : (gram_isHermitian X).eigenvalues =
      (isHermitian_unitary_conj_diagonal U hU d).eigenvalues :=
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr (congrArg Matrix.charpoly hgram)
  rw [nuclearNorm_eq_sum_sqrt, singValsSq_eq_eigenvalues_gram, heig]
  exact sum_f_eigenvalues_unitary_conj_diagonal U hU d Real.sqrt

lemma frobNormSq_of_gram_spectral (X U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U * U.conjTranspose = 1) (d : Fin m → ℝ)
    (hgram : gram X = realSpectral U d) :
    frobNormSq X = ∑ i, d i := by
  have heig : (gram_isHermitian X).eigenvalues =
      (isHermitian_unitary_conj_diagonal U hU d).eigenvalues :=
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr (congrArg Matrix.charpoly hgram)
  rw [frobNormSq_eq_sum_singValsSq, singValsSq_eq_eigenvalues_gram, heig]
  exact sum_f_eigenvalues_unitary_conj_diagonal U hU d id

/-- Gram matrix of a spectral function after multiplication by `A†`. -/
lemma gram_adjoint_spectral (A U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U.conjTranspose * U = 1) (d f : Fin m → ℝ)
    (hA : A * A.conjTranspose = realSpectral U d) :
    gram (A.conjTranspose * realSpectral U f) =
      realSpectral U (fun i => d i * f i ^ 2) := by
  rw [gram_mul]
  have hf := (realSpectral_hermitian U f).eq
  rw [hf]
  have hg : gram A.conjTranspose = A * A.conjTranspose := by
    simp only [gram, Matrix.conjTranspose_conjTranspose]
  rw [hg, hA, realSpectral_mul U hU, realSpectral_mul U hU]
  congr 1
  funext i
  ring

/-- Positive eigenvalues of the left Gram matrix of an invertible matrix. -/
lemma left_eigenvalues_pos (A : Matrix (Fin m) (Fin m) ℂ) (hA : IsUnit A)
    (i : Fin m) : 0 < (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues i := by
  have hInj : Function.Injective (Matrix.mulVec A.conjTranspose) :=
    Matrix.mulVec_injective_iff_isUnit.mpr (isUnit_conjTranspose hA)
  have hPos : (A.conjTranspose.conjTranspose * A.conjTranspose).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self _ hInj
  simpa only [Matrix.conjTranspose_conjTranspose] using hPos.eigenvalues_pos i

lemma realSpectral_add_const (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U * U.conjTranspose = 1) (d : Fin m → ℝ) (c : ℝ) :
    realSpectral U (fun i => d i + c) = realSpectral U d + c • 1 := by
  have hd : Matrix.diagonal (fun _ : Fin m => (c : ℂ)) =
      (c • (1 : Matrix (Fin m) (Fin m) ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  unfold realSpectral
  simp only [Complex.ofReal_add]
  rw [← Matrix.diagonal_add (fun i => (d i : ℂ)) (fun _ => (c : ℂ)),
    Matrix.mul_add, Matrix.add_mul, hd]
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

lemma realSpectral_inv (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1)
    (d : Fin m → ℝ) (hd : ∀ i, d i ≠ 0) :
    (realSpectral U d)⁻¹ = realSpectral U (fun i => (d i)⁻¹) := by
  simpa only [realSpectral, Complex.ofReal_inv] using
    inv_unitary_conj_diagonal U hU hU' (fun i => (d i : ℂ))
      (fun i => Complex.ofReal_ne_zero.mpr (hd i))

/-- The scalar square-root identity that converts the actual Gram spectrum to
    the nonnegative regularization error at a singular value. -/
lemma sqrt_regularization_gram (d lam : ℝ) (hd : 0 < d) (hlam : 0 < lam) :
    Real.sqrt (d * (d⁻¹ - (d + lam ^ 2)⁻¹) ^ 2) =
      |1 / Real.sqrt d - Real.sqrt d / ((Real.sqrt d) ^ 2 + lam ^ 2)| := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hsq : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd.le
  rw [Real.sqrt_mul hd.le, Real.sqrt_sq_eq_abs]
  calc
    Real.sqrt d * |d⁻¹ - (d + lam ^ 2)⁻¹| =
        |Real.sqrt d * (d⁻¹ - (d + lam ^ 2)⁻¹)| := by
      rw [abs_mul, abs_of_pos hs]
    _ = _ := ?_
  congr 1
  rw [hsq]
  have he : Real.sqrt d * d⁻¹ = 1 / Real.sqrt d := by
    apply (eq_div_iff hs.ne').mpr
    rw [mul_assoc, mul_comm (d⁻¹), ← mul_assoc, ← pow_two, hsq]
    exact mul_inv_cancel₀ hd.ne'
  simp only [mul_sub, he, div_eq_mul_inv]

/-- Lemma 4 of the paper, for the actual matrix inverse and regularized
    inverse. No spectral decomposition or norm estimate is assumed. -/
theorem lemma_4 (A : Matrix (Fin m) (Fin m) ℂ) (hA : IsUnit A)
    (lam : ℝ) (hlam : 0 < lam) :
    nuclearNorm (A⁻¹ - regInv A lam) ≤ (lam / 2) * frobNormSq A⁻¹ := by
  let U : Matrix (Fin m) (Fin m) ℂ := leftSingUnitary A
  let d : Fin m → ℝ := (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues
  have hU : U * U.conjTranspose = 1 := leftSing_mul_star A
  have hU' : U.conjTranspose * U = 1 := leftSing_star_mul A
  have hd : ∀ i, 0 < d i := left_eigenvalues_pos A hA
  have hspec : A * A.conjTranspose = realSpectral U d :=
    self_mul_conjTranspose_spectral A
  have hinv : A⁻¹ = A.conjTranspose * realSpectral U (fun i => (d i)⁻¹) := by
    rw [inv_eq_adjoint_mul hA, hspec, realSpectral_inv U hU hU' d
      (fun i => (hd i).ne')]
  have hshift : A * A.conjTranspose + lam ^ 2 • 1 =
      realSpectral U (fun i => d i + lam ^ 2) := by
    rw [realSpectral_add_const U hU, hspec]
  have hreg : regInv A lam =
      A.conjTranspose * realSpectral U (fun i => (d i + lam ^ 2)⁻¹) := by
    rw [regInv, hshift, realSpectral_inv U hU hU' _]
    intro i
    have hdi := hd i
    exact ne_of_gt (by positivity : 0 < d i + lam ^ 2)
  have hdiff : A⁻¹ - regInv A lam = A.conjTranspose *
      realSpectral U (fun i => (d i)⁻¹ - (d i + lam ^ 2)⁻¹) := by
    rw [hinv, hreg, ← Matrix.mul_sub, realSpectral_sub]
  have hfrob : frobNormSq A⁻¹ = ∑ i, 1 / d i := by
    have hg := gram_adjoint_spectral A U hU' d (fun i => (d i)⁻¹) hspec
    rw [← hinv] at hg
    rw [frobNormSq_of_gram_spectral _ U hU _ hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp [(hd i).ne']
  have hnuc : nuclearNorm (A⁻¹ - regInv A lam) =
      ∑ i, |1 / Real.sqrt (d i) - Real.sqrt (d i) /
        ((Real.sqrt (d i)) ^ 2 + lam ^ 2)| := by
    have hg := gram_adjoint_spectral A U hU' d
      (fun i => (d i)⁻¹ - (d i + lam ^ 2)⁻¹) hspec
    rw [← hdiff] at hg
    rw [nuclearNorm_of_gram_spectral _ U hU _ hg]
    exact Finset.sum_congr rfl fun i _ => sqrt_regularization_gram _ _ (hd i) hlam
  rw [hnuc, hfrob]
  have hbound := lemma_4_singular_value_form (fun i => Real.sqrt (d i))
    (fun i => Real.sqrt_pos.mpr (hd i)) lam hlam
  have hsq : ∀ i, (Real.sqrt (d i)) ^ 2 = d i := fun i => Real.sq_sqrt (hd i).le
  simpa only [hsq] using hbound

end Paper25


