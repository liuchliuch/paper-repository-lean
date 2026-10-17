import Paper13.LocalProjector

/-! # The polynomial-certificate correction (paper Appendix A). -/
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators

/-- Computational-basis ket. -/
def basisKet {n : ℕ} (x : QubitBasis n) : QubitBasis n → ℂ := fun y => if y = x then 1 else 0

lemma swapAt_basisKet {n : ℕ} (a b : Fin n) (x : QubitBasis n) :
    (swapAt a b).mulVec (basisKet x) = basisKet (swapBasis a b x) := by
  ext y
  change (∑ z, swapAt a b y z * basisKet x z) = _
  rw [Fintype.sum_eq_single x]
  · simp [swapAt, basisKet]
  · intro z hz; simp [basisKet, hz]

/-- The Pi convention in the cited printed certificate. -/
def piSwap {n : ℕ} (a b : Fin n) : Op n := (2 : ℂ) • swapAt a b - 1

def printedCertificate : Op 7 :=
  -(piSwap 0 2 + piSwap 1 6 + piSwap 3 5) +
    piSwap 0 2 * (piSwap 1 6 + piSwap 3 5) - piSwap 0 2 * piSwap 1 6 * piSwap 3 5

/-- The missing bc term gives exactly the factorized projector (paper equation 27). -/
theorem corrected_certificate_identity :
    (64 : ℂ) • localP = 1 + printedCertificate + piSwap 1 6 * piSwap 3 5 := by
  dsimp [localP, printedCertificate, piSwap, singletProj]
  simp only [smul_mul_smul, sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_add, smul_sub, add_smul, sub_smul, smul_smul, mul_assoc]
  module

lemma corrected_certificate_eq :
    printedCertificate + piSwap 1 6 * piSwap 3 5 = (64 : ℂ) • localP - 1 := by
  rw [corrected_certificate_identity]
  abel

/-- The corrected certificate commutes with both shared Hamiltonians and the global Z field. -/
theorem corrected_certificate_commutes :
    comm (printedCertificate + piSwap 1 6 * piSwap 3 5)
      (Xv (0 : Fin 7) + Xv 1 + Xv 2 + Xv 3 + Xv 4 + Xv 5 + Xv 6) = 0 ∧
    comm (printedCertificate + piSwap 1 6 * piSwap 3 5) Hzz_H = 0 ∧
    comm (printedCertificate + piSwap 1 6 * piSwap 3 5) Hz_H = 0 := by
  rw [corrected_certificate_eq]
  simp only [comm, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
    localP_comm_HX, localP_comm_Hz, Hzz_H_mul_localP, localP_mul_Hzz_H]
  constructor
  · abel
  constructor
  · simp
  · abel

/-- The two single-excitation strings used in Appendix A. -/
def certX : QubitBasis 7 := ![0,1,0,0,0,0,0]
def certY : QubitBasis 7 := ![0,0,0,0,0,0,1]

lemma printedCertificate_on_x : printedCertificate.mulVec (basisKet certX) = (-2 : ℂ) • basisKet certY := by
  have s1x : swapBasis 0 2 certX = certX := by decide
  have s1y : swapBasis 0 2 certY = certY := by decide
  have s2x : swapBasis 1 6 certX = certY := by decide
  have s3x : swapBasis 3 5 certX = certX := by decide
  have s3y : swapBasis 3 5 certY = certY := by decide
  simp only [printedCertificate, piSwap, Matrix.sub_mulVec, Matrix.add_mulVec,
    Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, swapAt_basisKet,
    s1x, s1y, s2x, s3x, s3y]
  module

/-- Diagonal entries of the eight-edge cost operator. -/
def costEigen (x : QubitBasis 7) : ℂ :=
  let z := fun i : Fin 7 => if x i = 0 then (1 : ℂ) else -1
  z 0*z 1 + z 1*z 2 + z 2*z 3 + z 3*z 4 + z 4*z 5 + z 5*z 6 + z 1*z 5 + z 2*z 5

lemma Hzz_H_diagonal : Hzz_H = Matrix.diagonal costEigen := by
  simp only [Hzz_H, ZZ, Zv_diagonal, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_add]
  ext x y
  by_cases h : x = y
  · subst y; simp [Matrix.diagonal, costEigen]
  · simp [Matrix.diagonal, h]

lemma Hzz_H_basisKet (x : QubitBasis 7) : Hzz_H.mulVec (basisKet x) = costEigen x • basisKet x := by
  rw [Hzz_H_diagonal]
  ext y
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, basisKet]
  split_ifs with h
  · subst y; rfl
  · simp

lemma Hzz_H_on_x : Hzz_H.mulVec (basisKet certX) = (2 : ℂ) • basisKet certX := by
  have hx : costEigen certX = 2 := by
    change ((1 : ℂ)*(-1) + (-1)*1 + 1*1 + 1*1 + 1*1 + 1*1 + (-1)*1 + 1*1) = 2
    norm_num
  rw [Hzz_H_basisKet, hx]

lemma Hzz_H_on_y : Hzz_H.mulVec (basisKet certY) = (6 : ℂ) • basisKet certY := by
  have hy : costEigen certY = 6 := by
    change ((1 : ℂ)*1 + 1*1 + 1*1 + 1*1 + 1*1 + 1*(-1) + 1*1 + 1*1) = 6
    norm_num
  rw [Hzz_H_basisKet, hy]

/-- The exact nonzero commutator claimed in Appendix A. -/
theorem printedCertificate_commutator_on_x :
    (comm printedCertificate Hzz_H).mulVec (basisKet certX) = (8 : ℂ) • basisKet certY := by
  simp only [comm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    Hzz_H_on_x, printedCertificate_on_x, Matrix.mulVec_smul, Hzz_H_on_y]
  module

/-- The printed certificate does not commute with the cost Hamiltonian. -/
theorem printedCertificate_not_commute : comm printedCertificate Hzz_H ≠ 0 := by
  intro h
  have hv := congrArg (fun M : Op 7 => (M.mulVec (basisKet certX)) certY) h
  dsimp only at hv
  rw [printedCertificate_commutator_on_x] at hv
  norm_num [basisKet] at hv
end Paper13
