import Paper22.PetzMomentBound
import Paper22.Tensor
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-! Fractional matrix powers under diagonalization, reindexing, and Kronecker
products, for the tensor-power Petz moment argument. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator Kronecker
open Matrix
noncomputable section
namespace Paper22
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def matrixDiagonalStarAlgHom : (ι → ℂ) →⋆ₐ[ℂ] Matrix ι ι ℂ :=
  { Matrix.diagonalAlgHom (n := ι) (R := ℂ) (α := ℂ) with
    map_star' := fun a => by
      change diagonal (star a) = (diagonal a)ᴴ
      simpa only [Pi.star_def] using (Matrix.diagonal_conjTranspose a).symm }

def matrixConjugationStarAlgHom (U : unitary (Matrix ι ι ℂ)) :
    Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix ι ι ℂ where
  toFun A := (U : Matrix ι ι ℂ)*A*(U : Matrix ι ι ℂ)ᴴ
  map_zero' := by simp
  map_one' := by
    change (U : Matrix ι ι ℂ)*1*(U : Matrix ι ι ℂ)ᴴ=1
    rw [Matrix.mul_one]
    exact unitary.mul_star_self_of_mem U.2
  map_add' A B := by simp only [Matrix.mul_add,Matrix.add_mul]
  map_mul' A B := by
    have hU : (U : Matrix ι ι ℂ)ᴴ*(U : Matrix ι ι ℂ)=1 := unitary.star_mul_self_of_mem U.2
    calc (U : Matrix ι ι ℂ)*(A*B)*(U : Matrix ι ι ℂ)ᴴ =
          (U : Matrix ι ι ℂ)*A*((U : Matrix ι ι ℂ)ᴴ*(U : Matrix ι ι ℂ))*B*(U : Matrix ι ι ℂ)ᴴ := by
            rw [hU,Matrix.mul_one]
            noncomm_ring
         _ = _ := by noncomm_ring
  commutes' r := by
    have hU : (U : Matrix ι ι ℂ)*(U : Matrix ι ι ℂ)ᴴ=1 := unitary.mul_star_self_of_mem U.2
    simp only [Algebra.algebraMap_eq_smul_one,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_one,hU]
  map_star' A := by simp only [star_eq_conjTranspose,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]

def matrixReindexStarAlgHom (e : ι ≃ κ) : Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix κ κ ℂ :=
  { (Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom with
    map_star' := fun A => by ext i j; rfl }

theorem matrix_rpow_diagonal (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) {p : ℝ} (hp : 0 ≤ p) :
    CFC.rpow (diagonal (fun i => (a i : ℂ))) p =
      diagonal (fun i => ((a i ^ p : ℝ) : ℂ)) := by
  let f := matrixDiagonalStarAlgHom (ι := ι)
  let g : ℝ → ℝ := fun t => (t.toNNReal : ℝ) ^ p
  have hvec : IsSelfAdjoint (fun i => (a i : ℂ)) := by
    funext i
    simp only [Pi.star_apply,Complex.star_def,Complex.conj_ofReal]
  have hd : 0 ≤ diagonal (fun i => (a i : ℂ)) :=
    (posSemidef_diagonal_iff.mpr (fun i => (show (0:ℂ) ≤ (a i:ℂ) from ⟨ha i,rfl⟩))).nonneg
  have hg : Continuous g := (Real.continuous_rpow_const hp).comp
    (NNReal.continuous_coe.comp continuous_real_toNNReal)
  have hmap := f.map_cfc g (fun i => (a i : ℂ))
    (hf := by exact hg.continuousOn)
    (hφ := by exact f.toAlgHom.toLinearMap.continuous_of_finiteDimensional)
    (ha := hvec) (hφa := IsSelfAdjoint.of_nonneg hd)
  rw [cfc_map_pi (S := ℂ) (ha := hvec) (ha' := fun i => by
    change star (a i : ℂ) = (a i : ℂ)
    simp only [Complex.star_def,Complex.conj_ofReal]) (hf := by exact hg.continuousOn)] at hmap
  have hscalar (i : ι) : cfc g (a i : ℂ) = ((a i ^ p : ℝ) : ℂ) := by
    have he := cfc_algebraMap (A := ℂ) (R := ℝ) (a i) g
    simpa only [g,Real.coe_toNNReal _ (ha i)] using he
  have hre : CFC.rpow (diagonal (fun i => (a i : ℂ))) p =
      cfc g (diagonal (fun i => (a i : ℂ))) :=
    cfc_nnreal_eq_real (fun x => x ^ p) _ hd
  change diagonal (fun i => cfc g (a i : ℂ)) =
    cfc g (diagonal (fun i => (a i : ℂ))) at hmap
  rw [hre,← hmap]
  change diagonal (fun i => cfc g (a i : ℂ)) = _
  congr 1
  funext i
  exact hscalar i

theorem matrix_rpow_unitary_conjugate (U : unitary (Matrix ι ι ℂ))
    {A : Matrix ι ι ℂ} (hA : 0 ≤ A) {p : ℝ} (hp : 0 ≤ p) :
    CFC.rpow ((U : Matrix ι ι ℂ)*A*(U : Matrix ι ι ℂ)ᴴ) p =
      (U : Matrix ι ι ℂ)*CFC.rpow A p*(U : Matrix ι ι ℂ)ᴴ := by
  have hpos : 0 ≤ (U : Matrix ι ι ℂ)*A*(U : Matrix ι ι ℂ)ᴴ :=
    (hA.posSemidef.mul_mul_conjTranspose_same _).nonneg
  exact ((matrixConjugationStarAlgHom U).map_cfc (fun x : NNReal => x ^ p) A
    (hf := by exact (NNReal.continuous_rpow_const hp).continuousOn)
    (hφ := by exact (matrixConjugationStarAlgHom U).toAlgHom.toLinearMap.continuous_of_finiteDimensional) (ha := hA) (hφa := hpos)).symm

theorem matrix_rpow_reindex (e : ι ≃ κ) {A : Matrix ι ι ℂ} (hA : 0 ≤ A)
    {p : ℝ} (hp : 0 ≤ p) :
    CFC.rpow (A.submatrix e.symm e.symm) p = (CFC.rpow A p).submatrix e.symm e.symm := by
  exact ((matrixReindexStarAlgHom e).map_cfc (fun x : NNReal => x ^ p) A
    (hf := by exact (NNReal.continuous_rpow_const hp).continuousOn)
    (hφ := by exact (matrixReindexStarAlgHom e).toAlgHom.toLinearMap.continuous_of_finiteDimensional) (ha := hA)
    (hφa := (hA.posSemidef.submatrix e.symm).nonneg)).symm

/-- Spectral expansion of positive powers for any finite matrix index type. -/
theorem matrix_rpow_spectral {A : Matrix ι ι ℂ} (hA : 0 ≤ A) {p : ℝ} (hp : 0 ≤ p) :
    CFC.rpow A p =
      (hA.posSemidef.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)*
      diagonal (fun i => ((hA.posSemidef.isHermitian.eigenvalues i ^ p : ℝ) : ℂ))*
      (hA.posSemidef.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  have hD : 0 ≤ diagonal (fun i => (hA.posSemidef.isHermitian.eigenvalues i : ℂ)) :=
    (posSemidef_diagonal_iff.mpr (fun i => (show (0:ℂ) ≤ (hA.posSemidef.isHermitian.eigenvalues i:ℂ)
      from ⟨hA.posSemidef.eigenvalues_nonneg i,rfl⟩))).nonneg
  calc CFC.rpow A p = CFC.rpow
        ((hA.posSemidef.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)*
        diagonal (fun i => (hA.posSemidef.isHermitian.eigenvalues i : ℂ))*
        (hA.posSemidef.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ) p :=
      congrArg (fun X => CFC.rpow X p) hA.posSemidef.isHermitian.spectral_theorem
    _ = _ := by
      rw [matrix_rpow_unitary_conjugate _ hD hp,
        matrix_rpow_diagonal _ hA.posSemidef.eigenvalues_nonneg hp]

/-- Positive fractional powers respect actual Kronecker products. -/
theorem matrix_rpow_kronecker {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) {p : ℝ} (hp : 0 ≤ p) :
    CFC.rpow (A ⊗ₖ B) p = CFC.rpow A p ⊗ₖ CFC.rpow B p := by
  let U := (hA.posSemidef.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)
  let V := (hB.posSemidef.isHermitian.eigenvectorUnitary : Matrix κ κ ℂ)
  let a := hA.posSemidef.isHermitian.eigenvalues
  let b := hB.posSemidef.isHermitian.eigenvalues
  have hU₁ : Uᴴ*U=1 := unitary.star_mul_self_of_mem hA.posSemidef.isHermitian.eigenvectorUnitary.2
  have hU₂ : U*Uᴴ=1 := unitary.mul_star_self_of_mem hA.posSemidef.isHermitian.eigenvectorUnitary.2
  have hV₁ : Vᴴ*V=1 := unitary.star_mul_self_of_mem hB.posSemidef.isHermitian.eigenvectorUnitary.2
  have hV₂ : V*Vᴴ=1 := unitary.mul_star_self_of_mem hB.posSemidef.isHermitian.eigenvectorUnitary.2
  have hUV : U ⊗ₖ V ∈ unitary (Matrix (ι × κ) (ι × κ) ℂ) := by
    rw [unitary.mem_iff]
    constructor
    · change (U ⊗ₖ V)ᴴ*(U ⊗ₖ V)=1
      rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,hU₁,hV₁,
        Matrix.one_kronecker_one]
    · change (U ⊗ₖ V)*(U ⊗ₖ V)ᴴ=1
      rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,hU₂,hV₂,
        Matrix.one_kronecker_one]
  let w : ι × κ → ℝ := fun ij => a ij.1*b ij.2
  have hw : ∀ ij, 0 ≤ w ij := fun ij => mul_nonneg
    (hA.posSemidef.eigenvalues_nonneg ij.1) (hB.posSemidef.eigenvalues_nonneg ij.2)
  have hD : diagonal (fun i => (a i : ℂ)) ⊗ₖ diagonal (fun j => (b j : ℂ)) =
      diagonal (fun ij => (w ij : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal]
    congr 1
    funext ij
    exact (Complex.ofReal_mul _ _).symm
  have hAB : A ⊗ₖ B = (U ⊗ₖ V)*diagonal (fun ij => (w ij : ℂ))*(U ⊗ₖ V)ᴴ := by
    calc A ⊗ₖ B = (U*diagonal (fun i => (a i : ℂ))*Uᴴ) ⊗ₖ
          (V*diagonal (fun j => (b j : ℂ))*Vᴴ) := by
            have hAspec : A=U*diagonal (fun i => (a i : ℂ))*Uᴴ :=
              hA.posSemidef.isHermitian.spectral_theorem
            have hBspec : B=V*diagonal (fun j => (b j : ℂ))*Vᴴ :=
              hB.posSemidef.isHermitian.spectral_theorem
            rw [← hAspec,← hBspec]
         _ = _ := by rw [Matrix.mul_kronecker_mul,Matrix.mul_kronecker_mul,hD,
           ← Matrix.conjTranspose_kronecker]
  have hDp : diagonal (fun ij => ((w ij ^ p : ℝ) : ℂ)) =
      diagonal (fun i => ((a i ^ p : ℝ) : ℂ)) ⊗ₖ diagonal (fun j => ((b j ^ p : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal]
    congr 1
    funext ij
    dsimp only [w]
    rw [Real.mul_rpow (hA.posSemidef.eigenvalues_nonneg _) (hB.posSemidef.eigenvalues_nonneg _),
      Complex.ofReal_mul]
  have hDpos : 0 ≤ diagonal (fun ij => (w ij : ℂ)) :=
    (posSemidef_diagonal_iff.mpr (fun ij => (show (0:ℂ) ≤ (w ij:ℂ) from ⟨hw ij,rfl⟩))).nonneg
  calc CFC.rpow (A ⊗ₖ B) p = CFC.rpow
        ((U ⊗ₖ V)*diagonal (fun ij => (w ij : ℂ))*(U ⊗ₖ V)ᴴ) p :=
      congrArg (fun X => CFC.rpow X p) hAB
    _ = (U ⊗ₖ V)*diagonal (fun ij => ((w ij ^ p : ℝ) : ℂ))*(U ⊗ₖ V)ᴴ := by
      rw [matrix_rpow_unitary_conjugate ⟨U ⊗ₖ V,hUV⟩ hDpos hp,matrix_rpow_diagonal w hw hp]
    _ = _ := by
      rw [matrix_rpow_spectral hA hp,matrix_rpow_spectral hB hp,hDp,
        Matrix.conjTranspose_kronecker,Matrix.mul_kronecker_mul,Matrix.mul_kronecker_mul]

end Paper22
end
