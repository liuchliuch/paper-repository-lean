import Paper10.Symm
import Mathlib.LinearAlgebra.UnitaryGroup

noncomputable section
open Matrix
namespace Paper10
variable {q m : ℕ}

/-- Orthogonal change of Frobenius coordinates. -/
def rotateF (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (O : Matrix.unitaryGroup (Fin m) ℝ) (j : Fin m) : Matrix (Fin q) (Fin q) ℝ :=
  ∑ i, (O : Matrix (Fin m) (Fin m) ℝ) i j • F i

theorem rotateF_isSymm (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : ∀ a, (F a).IsSymm) (O : Matrix.unitaryGroup (Fin m) ℝ) (j : Fin m) :
    (rotateF F O j).IsSymm := by
  show (∑ i, (O : Matrix (Fin m) (Fin m) ℝ) i j • F i)ᵀ = _
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.transpose_smul, show (F i)ᵀ = F i from hF i]

theorem rotateF_reconstruct (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (O : Matrix.unitaryGroup (Fin m) ℝ) (i : Fin m) :
    F i = ∑ j, (O : Matrix (Fin m) (Fin m) ℝ) i j • rotateF F O j := by
  ext a b
  let v : Fin m → ℝ := fun k => F k a b
  have hO : (O : Matrix (Fin m) (Fin m) ℝ) * (O : Matrix (Fin m) (Fin m) ℝ)ᵀ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using O.2.2
  have hh : ((O : Matrix (Fin m) (Fin m) ℝ) *ᵥ ((O : Matrix (Fin m) (Fin m) ℝ)ᵀ *ᵥ v)) i = v i := by
    rw [Matrix.mulVec_mulVec, hO, Matrix.one_mulVec]
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, rotateF,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, v] using hh.symm

/-- Orthogonal coordinate changes preserve the full Frobenius orthonormal-basis property. -/
theorem rotateF_orthonormal (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) (O : Matrix.unitaryGroup (Fin m) ℝ) :
    OrthonormalFrob (rotateF F O) := by
  classical
  refine ⟨rotateF_isSymm F hF.1 O, ?_, ?_⟩
  · intro a b
    have hO : (O : Matrix (Fin m) (Fin m) ℝ)ᵀ * (O : Matrix (Fin m) (Fin m) ℝ) = 1 := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using O.2.1
    have hh := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ => M a b) hO
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hh
    unfold rotateF frob
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    change (∑ i, ∑ j, (O : Matrix (Fin m) (Fin m) ℝ) j b * ((O : Matrix (Fin m) (Fin m) ℝ) i a * frob (F i) (F j))) = _
    simp_rw [hF.2.1]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases hab : a = b <;> simpa [hab, mul_comm] using hh
  · intro U hU
    obtain ⟨v, hv⟩ := hF.2.2 U hU
    refine ⟨fun j => ∑ i, v i * (O : Matrix (Fin m) (Fin m) ℝ) i j, ?_⟩
    calc
      U = ∑ i, v i • F i := hv
      _ = ∑ i, v i • (∑ j, (O : Matrix (Fin m) (Fin m) ℝ) i j • rotateF F O j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← rotateF_reconstruct F O i]
      _ = _ := by
        simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]

end Paper10
