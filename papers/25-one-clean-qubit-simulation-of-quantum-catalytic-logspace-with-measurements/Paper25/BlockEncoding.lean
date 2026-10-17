import Paper25.FilterMatrix
import Paper25.Liouville
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Explicit linear combinations, Hermitian dilation, and compression to a walk

The selector acts coherently on a finite register.  Preparing it with a unitary,
selecting a unitary term, and reversing the preparation is itself a unitary.
Its chosen selector block is the weighted linear combination, proved by matrix
multiplication.  This module also proves the reflection/walk identity (14).
-/

noncomputable section

open scoped ComplexConjugate

namespace Paper25

section Selector

variable {s n : Type*} [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n]

/-- Coherent selection of the unitary indexed by the first register. -/
def selectMatrix (K : s → Matrix n n ℂ) : Matrix (s × n) (s × n) ℂ :=
  fun p q => if p.1 = q.1 then K p.1 p.2 q.2 else 0

lemma selectMatrix_mul (K L : s → Matrix n n ℂ) :
    selectMatrix K * selectMatrix L = selectMatrix (fun j => K j * L j) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    simp [selectMatrix, Matrix.mul_apply, Fintype.sum_prod_type]
  · simp [selectMatrix, Matrix.mul_apply, Fintype.sum_prod_type, hab]

lemma selectMatrix_star (K : s → Matrix n n ℂ) :
    star (selectMatrix K) = selectMatrix (fun j => star (K j)) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  by_cases hab : a = b
  · subst b; simp [selectMatrix, Matrix.star_apply, Matrix.conjTranspose_apply]
  · simp [selectMatrix, Matrix.star_apply, Matrix.conjTranspose_apply, hab, Ne.symm hab]

lemma selectMatrix_one : selectMatrix (fun _ : s => (1 : Matrix n n ℂ)) = 1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  by_cases hab : a = b
  · subst b; simp [selectMatrix, Matrix.one_apply]
  · simp [selectMatrix, Matrix.one_apply, hab, Prod.mk.injEq]

/-- Selection of unitary matrices is unitary, including all inactive labels. -/
theorem selectMatrix_unitary (K : s → Matrix n n ℂ)
    (hK : ∀ j, K j ∈ Matrix.unitaryGroup n ℂ) :
    selectMatrix K ∈ Matrix.unitaryGroup (s × n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [selectMatrix_star, selectMatrix_mul]
  have h : (fun j => star (K j) * K j) = (fun _ : s => (1 : Matrix n n ℂ)) := by
    funext j; exact (hK j).1
  rw [h, selectMatrix_one]

/-- PREPARE† SELECT PREPARE, acting on selector and data registers. -/
def lcuMatrix (S : Matrix s s ℂ) (K : s → Matrix n n ℂ) :
    Matrix (s × n) (s × n) ℂ :=
  star (Matrix.kronecker S (1 : Matrix n n ℂ)) * selectMatrix K *
    Matrix.kronecker S (1 : Matrix n n ℂ)

theorem lcuMatrix_unitary (S : Matrix s s ℂ) (K : s → Matrix n n ℂ)
    (hS : S ∈ Matrix.unitaryGroup s ℂ) (hK : ∀ j, K j ∈ Matrix.unitaryGroup n ℂ) :
    lcuMatrix S K ∈ Matrix.unitaryGroup (s × n) ℂ := by
  have hP := Matrix.kronecker_mem_unitary hS (Matrix.unitaryGroup n ℂ).one_mem
  exact (Matrix.unitaryGroup (s × n) ℂ).mul_mem
    ((Matrix.unitaryGroup (s × n) ℂ).mul_mem (unitary.star_mem hP) (selectMatrix_unitary K hK)) hP

/-- The selector block is a weighted sum, with weights arising from coherent
uncomputation; no initialization or probabilistic selection is assumed here. -/
theorem lcuMatrix_block (S : Matrix s s ℂ) (K : s → Matrix n n ℂ) (q : s) :
    (lcuMatrix S K).submatrix (fun i => (q, i)) (fun i => (q, i)) =
      ∑ j, (conj (S j q) * S j q) • K j := by
  ext a b
  simp [lcuMatrix, selectMatrix, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.conjTranspose_apply, Matrix.star_apply,
    Matrix.one_apply, Matrix.sum_apply, Matrix.smul_apply, apply_ite, mul_assoc, mul_comm,
    mul_left_comm]

end Selector

section PauliLCU

open Kronecker

/-- Equation (11), with the paper's Liouville-vectorization convention. -/
theorem resetPauliSum_eq_resetL : resetPauliSum = resetL := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [resetPauliSum, resetL, pauliI, pauliX, pauliY, pauliZ,
      Matrix.kronecker_apply, Matrix.one_apply, Matrix.of_apply]

lemma pauliI_unitary : pauliI ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.unitaryGroup (Fin 2) ℂ).one_mem

lemma pauliX_unitary : pauliX ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply]

lemma pauliY_unitary : pauliY ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliY, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply]

lemma pauliZ_unitary : pauliZ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliZ, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply]

lemma phase_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (c : ℂ) (U : Matrix n n ℂ) (hc : star c * c = 1)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : c • U ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_smul, smul_mul_smul, hU.1, hc, one_smul]

/-- The eight selected unitaries for reset.  The factors i and -1 are phases. -/
def resetTerms : Fin 8 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ![Matrix.kronecker pauliI pauliI, Matrix.kronecker pauliI pauliZ,
    Matrix.kronecker pauliZ pauliI, Matrix.kronecker pauliZ pauliZ,
    Matrix.kronecker pauliX pauliX, Complex.I • Matrix.kronecker pauliX pauliY,
    Complex.I • Matrix.kronecker pauliY pauliX, (-1 : ℂ) • Matrix.kronecker pauliY pauliY]

theorem resetTerms_unitary (j : Fin 8) :
    resetTerms j ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  fin_cases j
  · exact Matrix.kronecker_mem_unitary pauliI_unitary pauliI_unitary
  · exact Matrix.kronecker_mem_unitary pauliI_unitary pauliZ_unitary
  · exact Matrix.kronecker_mem_unitary pauliZ_unitary pauliI_unitary
  · exact Matrix.kronecker_mem_unitary pauliZ_unitary pauliZ_unitary
  · exact Matrix.kronecker_mem_unitary pauliX_unitary pauliX_unitary
  · exact phase_unitary _ _ (by norm_num) (Matrix.kronecker_mem_unitary pauliX_unitary pauliY_unitary)
  · exact phase_unitary _ _ (by norm_num) (Matrix.kronecker_mem_unitary pauliY_unitary pauliX_unitary)
  · exact phase_unitary _ _ (by norm_num) (Matrix.kronecker_mem_unitary pauliY_unitary pauliY_unitary)

/-- The equal average of the eight actual unitaries is exactly reset divided by 2. -/
theorem resetTerms_average : (1 / 8 : ℂ) • ∑ j, resetTerms j = (1 / 2 : ℂ) • resetL := by
  rw [← resetPauliSum_eq_resetL]
  simp only [Fin.sum_univ_succ, resetTerms, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Fin.sum_univ_zero, add_zero]
  unfold resetPauliSum
  simp only [smul_smul, neg_smul, one_smul, smul_add, smul_sub]
  module

/-- The cancellation used for inactive clock labels and padding a unitary channel. -/
theorem eightTerm_unitary_average {n : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix n n ℂ) :
    (1 / 8 : ℂ) • (S + S + S + S + 1 - 1 + 1 - 1) = (1 / 2 : ℂ) • S := by
  module

end PauliLCU

section WeightedSelector

/-- A real plane rotation, represented without inverse trigonometric choices. -/
def realRotation (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![(a : ℂ), -(b : ℂ)], ![(b : ℂ), (a : ℂ)]]

lemma realRotation_unitary (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    realRotation a b ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realRotation, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply] <;>
    norm_cast <;> nlinarith [hab]

lemma realRotation_lcu_block {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (K : Fin 2 → Matrix n n ℂ) :
    (lcuMatrix (realRotation a b) K).submatrix (fun i => (0, i)) (fun i => (0, i)) =
      ((a ^ 2 : ℝ) : ℂ) • K 0 + ((b ^ 2 : ℝ) : ℂ) • K 1 := by
  rw [lcuMatrix_block]
  simp [Fin.sum_univ_succ, realRotation, pow_two]

/-- The explicit selector state √(1/3)|0⟩ + √(2/3)|1⟩, completed to a unitary. -/
def prepareThird : Matrix (Fin 2) (Fin 2) ℂ :=
  realRotation (Real.sqrt (1 / 3)) (Real.sqrt (2 / 3))

lemma prepareThird_unitary : prepareThird ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply realRotation_unitary
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 3),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  norm_num

/-- The second selector realizes I/3 - 2 U_L/3 by genuine coherent LCU. -/
theorem prepareThird_block {n : Type*} [Fintype n] [DecidableEq n]
    (UL : Matrix n n ℂ) :
    (lcuMatrix prepareThird ![1, -UL]).submatrix (fun i => (0, i)) (fun i => (0, i)) =
      (1 / 3 : ℂ) • 1 - (2 / 3 : ℂ) • UL := by
  unfold prepareThird
  rw [realRotation_lcu_block,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 3),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  norm_num [sub_eq_add_neg]

/-- Equation (12), including compression of the original block ancillas.
The premise is the smaller L/2 encoding supplied by the preceding channel LCU. -/
theorem history_lcu_block {s n : Type*} [Fintype s] [DecidableEq s]
    [Fintype n] [DecidableEq n] (q : s) (UL : Matrix (s × n) (s × n) ℂ)
    (L : Matrix n n ℂ)
    (hL : UL.submatrix (fun i => (q, i)) (fun i => (q, i)) = (1 / 2 : ℂ) • L) :
    (lcuMatrix prepareThird ![1, -UL]).submatrix
      (fun i => (0, (q, i))) (fun i => (0, (q, i))) = (1 / 3 : ℂ) • (1 - L) := by
  have h := prepareThird_block UL
  ext i j
  have hij := congr_fun (congr_fun h (q, i)) (q, j)
  have hLij := congr_fun (congr_fun hL i) j
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, Prod.mk.injEq, true_and] at hij hLij ⊢
  rw [hLij] at hij
  rw [hij]
  ring

end WeightedSelector

section PhaseUncompute

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- An explicit one-qubit rotation with real zero-to-zero amplitude a. -/
def amplitudeRotation (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  realRotation a (Real.sqrt (1 - a ^ 2))

lemma amplitudeRotation_unitary (a : ℝ) (ha : |a| ≤ 1) :
    amplitudeRotation a ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hr : 0 ≤ 1 - a ^ 2 := by
    have h := abs_le.mp ha
    nlinarith
  apply realRotation_unitary
  rw [Real.sq_sqrt hr]
  ring

/-- The complete coherent phase-preparation, label-rotation, and uncomputation circuit. -/
def phaseUncompute (S : Matrix s s ℂ) (g : s → ℝ) :
    Matrix (s × Fin 2) (s × Fin 2) ℂ :=
  lcuMatrix S (fun j => amplitudeRotation (g j))

theorem phaseUncompute_unitary (S : Matrix s s ℂ) (g : s → ℝ)
    (hS : S ∈ Matrix.unitaryGroup s ℂ) (hg : ∀ j, |g j| ≤ 1) :
    phaseUncompute S g ∈ Matrix.unitaryGroup (s × Fin 2) ℂ :=
  lcuMatrix_unitary S _ hS (fun j => amplitudeRotation_unitary _ (hg j))

/-- Equation (16): the all-zero block contains probabilities because the
phase preparation is uncomputed.  S is its action on a fixed eigenspace. -/
theorem phaseUncompute_amplitude (S : Matrix s s ℂ) (g : s → ℝ) (q : s) :
    phaseUncompute S g (q, 0) (q, 0) =
      ((∑ j, ‖S j q‖ ^ 2 * g j : ℝ) : ℂ) := by
  have h := congr_fun (congr_fun (lcuMatrix_block S (fun j => amplitudeRotation (g j)) q) 0) 0
  simpa only [phaseUncompute, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, amplitudeRotation, realRotation, Matrix.of_apply,
    Matrix.cons_val_zero, Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow] using h

/-- The phase probabilities arising from any genuine unitary preparation are normalized. -/
theorem unitary_column_prob_sum (S : Matrix s s ℂ)
    (hS : S ∈ Matrix.unitaryGroup s ℂ) (q : s) :
    ∑ j, ‖S j q‖ ^ 2 = 1 := by
  have h := congr_fun (congr_fun hS.1 q) q
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def,
    Complex.conj_mul'] at h
  exact_mod_cast h

end PhaseUncompute

section HermitianDilation

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The extra h selector in equation (13). -/
def hermitianDilation (U : Matrix n n ℂ) : Matrix (Sum n n) (Sum n n) ℂ :=
  Matrix.fromBlocks 0 U (star U) 0

lemma hermitianDilation_hermitian (U : Matrix n n ℂ) : (hermitianDilation U).IsHermitian := by
  show (hermitianDilation U).conjTranspose = _
  simp [hermitianDilation, Matrix.fromBlocks_conjTranspose, Matrix.star_eq_conjTranspose]

theorem hermitianDilation_unitary (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    hermitianDilation U ∈ Matrix.unitaryGroup (Sum n n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hs : star (hermitianDilation U) = hermitianDilation U := hermitianDilation_hermitian U
  rw [hs]
  unfold hermitianDilation
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hU.1, hU.2]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

/-- Compressing the original ancillas commutes with the h dilation. -/
lemma hermitianDilation_submatrix {m : Type*} (U : Matrix n n ℂ) (f : m → n) :
    (hermitianDilation U).submatrix (Sum.map f f) (Sum.map f f) =
      hermitianDilation (U.submatrix f f) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

/-- Equation (13), with its concrete compression map and scale. -/
theorem history_dilation_block {s : Type*} [Fintype s] [DecidableEq s] {m : ℕ}
    (q : s) (UA : Matrix (s × Fin m) (s × Fin m) ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ)
    (hA : UA.submatrix (fun i => (q, i)) (fun i => (q, i)) = (1 / 3 : ℂ) • A) :
    (hermitianDilation UA).submatrix
      (Sum.map (fun i => (q, i)) (fun i => (q, i)))
      (Sum.map (fun i => (q, i)) (fun i => (q, i))) =
      ((1 / 3 : ℝ) : ℂ) • dilation A := by
  rw [hermitianDilation_submatrix, hA]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [hermitianDilation, dilation, Matrix.fromBlocks, Matrix.smul_apply,
      Matrix.star_apply, Matrix.conjTranspose_apply]

end HermitianDilation

section Walk

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Reflection about the range of an orthogonal projector. -/
def projectorReflection (P : Matrix n n ℂ) : Matrix n n ℂ := 2 • P - 1

/-- A projector gives an actual Hermitian unitary reflection. -/
theorem projectorReflection_hermitian (P : Matrix n n ℂ) (hP : P.IsHermitian) :
    (projectorReflection P).IsHermitian := by
  unfold projectorReflection
  simpa only [two_smul] using (hP.add hP).sub Matrix.isHermitian_one

lemma projectorReflection_sq (P : Matrix n n ℂ) (hP : P * P = P) :
    projectorReflection P * projectorReflection P = 1 := by
  unfold projectorReflection
  simp only [two_smul]
  noncomm_ring [hP]

theorem projectorReflection_unitary (P : Matrix n n ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) :
    projectorReflection P ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hR := projectorReflection_hermitian P hP
  rw [show star (projectorReflection P) = projectorReflection P from hR]
  exact projectorReflection_sq P hPP

/-- The walk is a product of two genuine unitaries. -/
def compressionWalk (P U : Matrix n n ℂ) : Matrix n n ℂ := projectorReflection P * U

theorem compressionWalk_unitary (P U : Matrix n n ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    compressionWalk P U ∈ Matrix.unitaryGroup n ℂ :=
  (Matrix.unitaryGroup n ℂ).mul_mem (projectorReflection_unitary P hP hPP) hU

/-- Equation (14).  The cross terms cancel when the walk is symmetrized. -/
theorem compressionWalk_realPart (P U : Matrix n n ℂ)
    (hP : P.IsHermitian) (hU : U.IsHermitian) :
    (1 / 2 : ℂ) • (compressionWalk P U + star (compressionWalk P U)) =
      P * U * P - (1 - P) * U * (1 - P) := by
  have hR : star (projectorReflection P) = projectorReflection P :=
    projectorReflection_hermitian P hP
  have hUs : star U = U := hU
  unfold compressionWalk
  rw [star_mul, hR, hUs]
  unfold projectorReflection
  have hs : (2 • P - 1) * U + U * (2 • P - 1) =
      (2 : ℂ) • (P * U + U * P - U) := by
    simp only [two_smul]
    noncomm_ring
  have hr : P * U * P - (1 - P) * U * (1 - P) = P * U + U * P - U := by
    noncomm_ring
  rw [hs, smul_smul, hr]
  norm_num

/-- The real part of the walk preserves the projected subspace. -/
theorem compressionWalk_realPart_compression (P U : Matrix n n ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (hU : U.IsHermitian) :
    P * ((1 / 2 : ℂ) • (compressionWalk P U + star (compressionWalk P U))) * P =
      P * U * P := by
  rw [compressionWalk_realPart P U hP hU]
  noncomm_ring [hPP]
  simp only [← mul_assoc, hPP]

end Walk

end Paper25
