import Paper25.BlockEncoding
import Paper25.StatePreparation

/-!
# The paper's three-selector-qubit channel encodings

The PREPARE matrix is literally H⊗H⊗H, and all eight SELECT terms are
unitaries.  Its zero block is their equal average.  Reset, dephasing, unitary
channels, and inactive clock labels are instantiated with the eight terms
specified in Section 4.1.
-/

noncomputable section
open scoped ComplexConjugate
namespace Paper25

abbrev Selector3 := Fin 2 × (Fin 2 × Fin 2)
def zeroSelector3 : Selector3 := (0, (0, 0))

/-- Binary labeling of the three physical selector qubits. -/
def selectorIndex3 : Selector3 ≃ Fin 8 :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv

/-- Three actual Hadamard gates prepare the equal superposition. -/
def uniformPrepare3 : Matrix Selector3 Selector3 ℂ :=
  Matrix.kronecker StatePreparation.H2
    (Matrix.kronecker StatePreparation.H2 StatePreparation.H2)

lemma uniformPrepare3_unitary : uniformPrepare3 ∈ Matrix.unitaryGroup Selector3 ℂ := by
  have hH : StatePreparation.H2 ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    StatePreparation.H2_unitary
  exact Matrix.kronecker_mem_unitary hH (Matrix.kronecker_mem_unitary hH hH)

lemma uniformPrepare3_weights (j : Selector3) :
    conj (uniformPrepare3 j zeroSelector3) * uniformPrepare3 j zeroSelector3 = (1 / 8 : ℂ) := by
  rcases j with ⟨i, k, l⟩
  have hc : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simp only [uniformPrepare3, zeroSelector3, Matrix.kronecker, Matrix.kronecker_apply,
    StatePreparation.H2_zero_column, map_mul, Complex.conj_ofReal]
  calc
    _ = (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2) ^ 3) := by ring
    _ = _ := by rw [hc]; norm_num

/-- The constant three-qubit LCU, with its eight labels reindexed as binary strings. -/
def eightLCU {n : Type*} [Fintype n] [DecidableEq n] (K : Fin 8 → Matrix n n ℂ) :
    Matrix (Selector3 × n) (Selector3 × n) ℂ :=
  lcuMatrix uniformPrepare3 (fun j => K (selectorIndex3 j))

theorem eightLCU_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (K : Fin 8 → Matrix n n ℂ) (hK : ∀ j, K j ∈ Matrix.unitaryGroup n ℂ) :
    eightLCU K ∈ Matrix.unitaryGroup (Selector3 × n) ℂ :=
  lcuMatrix_unitary _ _ uniformPrepare3_unitary (fun j => hK (selectorIndex3 j))

/-- The all-zero selector block is the equal average, derived from H⊗H⊗H. -/
theorem eightLCU_block {n : Type*} [Fintype n] [DecidableEq n]
    (K : Fin 8 → Matrix n n ℂ) :
    (eightLCU K).submatrix (fun i => (zeroSelector3, i)) (fun i => (zeroSelector3, i)) =
      (1 / 8 : ℂ) • ∑ j, K j := by
  unfold eightLCU
  rw [lcuMatrix_block]
  simp only [uniformPrepare3_weights]
  rw [← Finset.smul_sum, Equiv.sum_comp selectorIndex3 K]

/-- The reset channel's actual three-qubit block encoding. -/
def resetBlockEncoding := eightLCU resetTerms

theorem resetBlockEncoding_unitary :
    resetBlockEncoding ∈ Matrix.unitaryGroup (Selector3 × (Fin 2 × Fin 2)) ℂ :=
  eightLCU_unitary _ resetTerms_unitary

theorem resetBlockEncoding_block :
    resetBlockEncoding.submatrix (fun i => (zeroSelector3, i)) (fun i => (zeroSelector3, i)) =
      (1 / 2 : ℂ) • resetL := by
  rw [resetBlockEncoding, eightLCU_block, resetTerms_average]

/-- Unitary-channel terms, with canceling identity terms as in the paper. -/
def unitaryPaddingTerms {n : Type*} [DecidableEq n] (S : Matrix n n ℂ) :
    Fin 8 → Matrix n n ℂ := ![S, S, S, S, 1, -1, 1, -1]

lemma unitaryPaddingTerms_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix n n ℂ) (hS : S ∈ Matrix.unitaryGroup n ℂ) (j : Fin 8) :
    unitaryPaddingTerms S j ∈ Matrix.unitaryGroup n ℂ := by
  have h1 := (Matrix.unitaryGroup n ℂ).one_mem
  have hn : (-1 : Matrix n n ℂ) ∈ Matrix.unitaryGroup n ℂ := by
    convert phase_unitary (-1) (1 : Matrix n n ℂ) (by norm_num) h1 using 1 <;> simp
  fin_cases j <;> first | exact hS | exact h1 | exact hn

lemma unitaryPaddingTerms_average {n : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix n n ℂ) : (1 / 8 : ℂ) • ∑ j, unitaryPaddingTerms S j = (1 / 2 : ℂ) • S := by
  simp only [Fin.sum_univ_succ, unitaryPaddingTerms, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.sum_univ_zero, add_zero]
  module

/-- The dephasing-channel selector terms specified in Section 4.1. -/
def dephasingTerms : Fin 8 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  let II := Matrix.kronecker pauliI pauliI
  let ZZ := Matrix.kronecker pauliZ pauliZ
  ![II, II, ZZ, ZZ, II, -II, II, -II]

lemma dephasingTerms_unitary (j : Fin 8) :
    dephasingTerms j ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  have hI := Matrix.kronecker_mem_unitary pauliI_unitary pauliI_unitary
  have hZ := Matrix.kronecker_mem_unitary pauliZ_unitary pauliZ_unitary
  have hn : -Matrix.kronecker pauliI pauliI ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
    simpa using phase_unitary (-1) _ (by norm_num) hI
  fin_cases j <;> first | exact hI | exact hZ | exact hn

lemma dephasingTerms_average : (1 / 8 : ℂ) • ∑ j, dephasingTerms j = (1 / 2 : ℂ) • dephasingL := by
  simp only [Fin.sum_univ_succ, dephasingTerms, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.sum_univ_zero, add_zero]
  unfold dephasingL
  module

/-- Inactive clock values select four copies each of I and -I. -/
def inactiveTerms {n : Type*} [DecidableEq n] : Fin 8 → Matrix n n ℂ :=
  ![1, 1, 1, 1, -1, -1, -1, -1]

lemma inactiveTerms_unitary {n : Type*} [Fintype n] [DecidableEq n] (j : Fin 8) :
    inactiveTerms (n := n) j ∈ Matrix.unitaryGroup n ℂ := by
  have hI := (Matrix.unitaryGroup n ℂ).one_mem
  have hn : (-1 : Matrix n n ℂ) ∈ Matrix.unitaryGroup n ℂ := by
    simpa using phase_unitary (-1) (1 : Matrix n n ℂ) (by norm_num) hI
  fin_cases j <;> first | exact hI | exact hn

lemma inactiveTerms_average {n : Type*} [Fintype n] [DecidableEq n] :
    (1 / 8 : ℂ) • ∑ j, inactiveTerms (n := n) j = 0 := by
  simp only [Fin.sum_univ_succ, inactiveTerms, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.sum_univ_zero, add_zero]
  module

end Paper25
