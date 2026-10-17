import PsgEst.QuantumPerspective
import PsgEst.QuantumVariational
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Finite resolvent representation of matrix relative entropy. -/
open Matrix BigOperators Real
open scoped Kronecker
namespace PsgEst.QuantumTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def tensorBasis (U V : Matrix.unitaryGroup ι ℝ) :
    Matrix (ι × ι) (ι × ι) ℝ := (U : Matrix ι ι ℝ) ⊗ₖ (V : Matrix ι ι ℝ)

lemma tensorBasis_star (U V : Matrix.unitaryGroup ι ℝ) :
    star (tensorBasis U V) =
      star (U : Matrix ι ι ℝ) ⊗ₖ star (V : Matrix ι ι ℝ) := by
  exact Matrix.conjTranspose_kronecker _ _

lemma tensorBasis_star_mul (U V : Matrix.unitaryGroup ι ℝ) :
    star (tensorBasis U V) * tensorBasis U V = 1 := by
  rw [tensorBasis_star]
  change (star (U : Matrix ι ι ℝ) ⊗ₖ star (V : Matrix ι ι ℝ)) *
      ((U : Matrix ι ι ℝ) ⊗ₖ (V : Matrix ι ι ℝ)) = _
  rw [← Matrix.mul_kronecker_mul]
  simp only [unitary.coe_star_mul_self, Matrix.one_kronecker_one]

lemma tensorBasis_mul_star (U V : Matrix.unitaryGroup ι ℝ) :
    tensorBasis U V * star (tensorBasis U V) = 1 := by
  rw [tensorBasis_star]
  change ((U : Matrix ι ι ℝ) ⊗ₖ (V : Matrix ι ι ℝ)) *
      (star (U : Matrix ι ι ℝ) ⊗ₖ star (V : Matrix ι ι ℝ)) = _
  rw [← Matrix.mul_kronecker_mul]
  have hU : (U : Matrix ι ι ℝ) * star (U : Matrix ι ι ℝ) = 1 := unitary.coe_mul_star_self U
  have hV : (V : Matrix ι ι ℝ) * star (V : Matrix ι ι ℝ) = 1 := unitary.coe_mul_star_self V
  rw [hU, hV, Matrix.one_kronecker_one]

omit [Fintype ι] in
lemma diagonal_interpolation (s : ℝ) (a x : ι → ℝ) :
    diagonal (fun ij : ι×ι => s*a ij.1+(1-s)*x ij.2) =
      s • (diagonal a ⊗ₖ (1 : Matrix ι ι ℝ)) +
      (1-s) • ((1 : Matrix ι ι ℝ) ⊗ₖ diagonal x) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases hik : i=k <;> by_cases hjl : j=l <;>
    simp [hik, hjl]

lemma tensorBasis_diagonal_interpolation (U V : Matrix.unitaryGroup ι ℝ)
    (s : ℝ) (a x : ι → ℝ) :
    tensorBasis U V * diagonal (fun ij : ι×ι => s*a ij.1+(1-s)*x ij.2) *
      star (tensorBasis U V) =
      s • (((U : Matrix ι ι ℝ)*diagonal a*star (U : Matrix ι ι ℝ)) ⊗ₖ
        (1 : Matrix ι ι ℝ)) +
      (1-s) • ((1 : Matrix ι ι ℝ) ⊗ₖ
        ((V : Matrix ι ι ℝ)*diagonal x*star (V : Matrix ι ι ℝ))) := by
  rw [diagonal_interpolation, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
  congr 1
  · rw [tensorBasis_star]
    change s • (((U : Matrix ι ι ℝ) ⊗ₖ (V : Matrix ι ι ℝ)) *
      (diagonal a ⊗ₖ 1) * (star (U : Matrix ι ι ℝ) ⊗ₖ star (V : Matrix ι ι ℝ))) = _
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_one]
    have hV : (V : Matrix ι ι ℝ) * star (V : Matrix ι ι ℝ) = 1 := unitary.coe_mul_star_self V
    rw [hV]
  · rw [tensorBasis_star]
    change (1-s) • (((U : Matrix ι ι ℝ) ⊗ₖ (V : Matrix ι ι ℝ)) *
      (1 ⊗ₖ diagonal x) * (star (U : Matrix ι ι ℝ) ⊗ₖ star (V : Matrix ι ι ℝ))) = _
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_one]
    have hU : (U : Matrix ι ι ℝ) * star (U : Matrix ι ι ℝ) = 1 := unitary.coe_mul_star_self U
    rw [hU]

noncomputable def tensorInterpolation (s : ℝ) (A X : Matrix ι ι ℝ) :
    Matrix (ι×ι) (ι×ι) ℝ :=
  s • (A ⊗ₖ (1 : Matrix ι ι ℝ)) + (1-s) • ((1 : Matrix ι ι ℝ) ⊗ₖ X)

lemma tensorInterpolation_spectral {A X : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hX : X.IsHermitian) (s : ℝ) :
    tensorInterpolation s A X =
      tensorBasis hA.eigenvectorUnitary hX.eigenvectorUnitary *
        diagonal (fun ij : ι×ι => s*hA.eigenvalues ij.1+(1-s)*hX.eigenvalues ij.2) *
        star (tensorBasis hA.eigenvectorUnitary hX.eigenvectorUnitary) := by
  rw [tensorBasis_diagonal_interpolation]
  change tensorInterpolation s A X =
    s • (spectralMap hA id ⊗ₖ (1 : Matrix ι ι ℝ)) +
      (1-s) • ((1 : Matrix ι ι ℝ) ⊗ₖ spectralMap hX id)
  rw [spectralMap_id, spectralMap_id]
  rfl

lemma conjugate_diagonal_inverse {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : Matrix κ κ ℝ) (hU : star U*U=1) (hU' : U*star U=1)
    (c : κ → ℝ) (hc : ∀ i, c i ≠ 0) :
    (U*diagonal c*star U)⁻¹=U*diagonal (fun i => (c i)⁻¹)*star U := by
  apply Matrix.inv_eq_left_inv
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U), hU, Matrix.one_mul]
  rw [← Matrix.mul_assoc (diagonal _), Matrix.diagonal_mul_diagonal]
  simp only [inv_mul_cancel₀ (hc _), Matrix.diagonal_one]
  simpa only [Matrix.one_mul] using hU'

lemma tensorInterpolation_inverse {A X : Matrix ι ι ℝ}
    (hA : A.PosDef) (hX : X.PosDef) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (tensorInterpolation s A X)⁻¹ =
      tensorBasis hA.isHermitian.eigenvectorUnitary hX.isHermitian.eigenvectorUnitary *
        diagonal (fun ij : ι×ι =>
          (s*hA.isHermitian.eigenvalues ij.1+(1-s)*hX.isHermitian.eigenvalues ij.2)⁻¹) *
        star (tensorBasis hA.isHermitian.eigenvectorUnitary hX.isHermitian.eigenvectorUnitary) := by
  rw [tensorInterpolation_spectral hA.isHermitian hX.isHermitian]
  apply conjugate_diagonal_inverse _ (tensorBasis_star_mul _ _) (tensorBasis_mul_star _ _)
  intro ij
  have ha := hA.eigenvalues_pos ij.1
  have hx := hX.eigenvalues_pos ij.2
  have hpos : 0 < s*hA.isHermitian.eigenvalues ij.1+(1-s)*hX.isHermitian.eigenvalues ij.2 := by
    by_cases hz : s=0
    · simp only [hz, zero_mul, sub_zero, one_mul, zero_add]; exact hx
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hs (Ne.symm hz)) ha)
        (mul_nonneg (sub_nonneg.mpr hs1) hx.le)
  exact ne_of_gt hpos

/-- The tensor change of basis is exactly the two-sided matrix coordinate map. -/
lemma tensorBasis_star_mulVec (U V : Matrix.unitaryGroup ι ℝ)
    (Y : Matrix ι ι ℝ) (i j : ι) :
    (star (tensorBasis U V) *ᵥ (fun kl => Y kl.1 kl.2)) (i,j) =
      (star (U : Matrix ι ι ℝ) * Y * (V : Matrix ι ι ℝ)) i j := by
  simp only [tensorBasis, Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.star_apply, star_trivial, Matrix.mul_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Quadratic form after an actual orthogonal diagonalization of the inverse. -/
lemma qform_conjugate_diagonal (U : Matrix ι ι ℝ) (c v : ι → ℝ) :
    v ⬝ᵥ ((U * diagonal c * star U) *ᵥ v) =
      ∑ i, c i * (star U *ᵥ v) i ^ 2 := by
  have ht : U.transpose = star U := by ext i j; rfl
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ht]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual vectorized `X` has tensor spectral coefficients
`λX_j (UAᵀ UX)ij`. -/
lemma tensorBasis_star_vec_self {A X : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hX : X.IsHermitian) (i j : ι) :
    (star (tensorBasis hA.eigenvectorUnitary hX.eigenvectorUnitary) *ᵥ
      (fun kl => X kl.1 kl.2)) (i,j) =
      hX.eigenvalues j * QuantumVariational.overlapUnitary hA hX i j := by
  rw [tensorBasis_star_mulVec]
  have hXU : X * (hX.eigenvectorUnitary : Matrix ι ι ℝ) =
      (hX.eigenvectorUnitary : Matrix ι ι ℝ) * diagonal hX.eigenvalues := by
    conv_lhs => lhs; rw [hX.spectral_theorem]
    have hU : star (hX.eigenvectorUnitary : Matrix ι ι ℝ) *
        (hX.eigenvectorUnitary : Matrix ι ι ℝ) = 1 :=
      unitary.coe_star_mul_self hX.eigenvectorUnitary
    simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
    rfl
  rw [Matrix.mul_assoc, hXU, ← Matrix.mul_assoc, Matrix.mul_diagonal]
  change (star (hA.eigenvectorUnitary : Matrix ι ι ℝ) *
    (hX.eigenvectorUnitary : Matrix ι ι ℝ)) i j * hX.eigenvalues j =
      hX.eigenvalues j * (star (hA.eigenvectorUnitary : Matrix ι ι ℝ) *
        (hX.eigenvectorUnitary : Matrix ι ι ℝ)) i j
  ring

omit [Fintype ι] in
/-- The actual Sylvester matrix agrees with its Hermitian tensor interpolation. -/
lemma sylvesterMatrix_eq_tensorInterpolation {A X : Matrix ι ι ℝ}
    (hX : X.IsHermitian) (s : ℝ) :
    sylvesterMatrix s A X = tensorInterpolation s A X := by
  have ht : X.transpose = X := by
    ext i j
    simpa only [Matrix.transpose_apply, star_trivial] using hX.apply i j
  simp only [sylvesterMatrix, hsLeft, hsRight, tensorInterpolation, ht]

/-- Spectral expansion of the genuine inverse Sylvester quadratic form. -/
theorem sylvester_qform_spectrum {A X : Matrix ι ι ℝ}
    (hX : X.PosDef) (hA : A.PosDef) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    quadraticPerspective (fun ij => X ij.1 ij.2) (sylvesterMatrix s A X) =
      ∑ i, ∑ j, QuantumVariational.overlapWeight hA.isHermitian hX.isHermitian i j *
        (hX.isHermitian.eigenvalues j ^ 2 /
          ((1-s) * hX.isHermitian.eigenvalues j + s * hA.isHermitian.eigenvalues i)) := by
  rw [quadraticPerspective, sylvesterMatrix_eq_tensorInterpolation hX.isHermitian,
    tensorInterpolation_inverse hA hX s hs.1 hs.2, qform_conjugate_diagonal]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [tensorBasis_star_vec_self]
  dsimp [QuantumVariational.overlapWeight]
  ring

end PsgEst.QuantumTensor
