import Paper12.FixedRotations

noncomputable section
namespace Paper12
open Matrix Classical

def hadamardMat : QMat := !![(kickbackC), kickbackC; kickbackC, -kickbackC]
def sMat : QMat := !![1, 0; 0, Complex.I]

theorem hadamard_adjoint : hadamardMatᴴ = hadamardMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardMat, Matrix.conjTranspose_apply, kickbackC]

theorem hadamard_unitary : hadamardMatᴴ * hadamardMat = 1 := by
  rw [hadamard_adjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardMat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    ring_nf <;> norm_num [kickbackC_sq]

theorem sMat_unitary : sMatᴴ * sMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sMat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.I_mul_I]

theorem hadamard_conj_X : hadamardMat * pmat .X * hadamardMatᴴ = pmat .Z := by
  rw [hadamard_adjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardMat, pmat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    ring_nf <;> norm_num [kickbackC_sq]

theorem sMat_conj_X : sMat * pmat .X * sMatᴴ = pmat .Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sMat, pmat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.I_mul_I]

def basisChange : PSym → QMat
  | .I => 1
  | .X => 1
  | .Y => sMat
  | .Z => hadamardMat

theorem basisChange_unitary (s : PSym) : (basisChange s)ᴴ * basisChange s = 1 := by
  cases s
  · simp [basisChange]
  · simp [basisChange]
  · exact sMat_unitary
  · exact hadamard_unitary

theorem basisChange_conj_X (s : PSym) (hs : s ≠ .I) :
    basisChange s * pmat .X * (basisChange s)ᴴ = pmat s := by
  cases s
  · exact (hs rfl).elim
  · simp [basisChange]
  · exact sMat_conj_X
  · exact hadamard_conj_X

variable {X : Type*} [Fintype X]
def uniformChange (s : PSym) : Circuit X :=
  parallelCircuit (fun _ => basisChange s) (fun _ => basisChange_unitary s)

theorem uniformChange_preserved (s : PSym) (γ : X ≃ X) :
    (uniformChange (X := X) s).Preserved γ := by
  intro L hL
  simp only [uniformChange, parallelCircuit, List.mem_singleton] at hL
  subst L
  exact parallelLayer_map _ _ γ (fun _ => rfl)

end Paper12
