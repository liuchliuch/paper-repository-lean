import Paper25.SourceControl

noncomputable section
open scoped ComplexConjugate
namespace Paper25
namespace KrausChannel

/-- Dephasing an outcome work bit keeps exactly its diagonal blocks. -/
lemma dephase_outcome_entry (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (q b q' b' : Fin 2) :
    (dephase.extendLeft (Fin 2)).act X (q, b) (q', b') =
      if b = b' then X (q, b) (q', b') else 0 := by
  rw [extendLeft_act_block, dephase_act]
  by_cases h : b = b'
  · subst b'
    simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply, h]

/-- The CNOT basis permutation is an involution. -/
def copyPerm : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2) where
  toFun p := (p.1, p.1 + p.2)
  invFun p := (p.1, p.1 + p.2)
  left_inv p := by
    rcases p with ⟨q, b⟩
    fin_cases q <;> fin_cases b <;> simp [fin2_one_add_one]
  right_inv p := by
    rcases p with ⟨q, b⟩
    fin_cases q <;> fin_cases b <;> simp [fin2_one_add_one]

lemma copyGate_eq_reversibleGate : copyGate = reversibleGate copyPerm := by
  ext ⟨a, b⟩ ⟨i, j⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [copyGate, reversibleGate, copyPerm, Matrix.submatrix_apply,
      Matrix.one_apply, fin2_one_add_one, Prod.ext_iff]

/-- CNOT conjugation permutes matrix entries, including off-diagonal entries. -/
lemma copyGate_act (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (q b q' b' : Fin 2) :
    (unitary copyGate copyGate_unitary).act X (q, b) (q', b') =
      X (q, q + b) (q', q' + b') := by
  have h := reversibleGate_act copyPerm X
  rw [unitary_act] at h
  rw [unitary_act, copyGate_eq_reversibleGate, h]
  rfl

/-- Exact measurement-instrument semantics, even when the overwritten outcome
bit was correlated with the input. The sum discards that previous bit. -/
theorem measurement_act (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (q b q' b' : Fin 2) :
    measurement.act X (q, b) (q', b') =
      if q = q' ∧ b = q ∧ b' = q then
        ∑ v, X (q, v) (q', v) else 0 := by
  simp only [measurement, comp_act]
  rw [dephase_outcome_entry, copyGate_act, reset_extendLeft_entry]
  fin_cases q <;> fin_cases b <;> fin_cases q' <;> fin_cases b' <;>
    simp [fin2_one_add_one]

/-- Measurement preserves exactly the instrument's correlations with every
finite reference. This is an entrywise statement on arbitrary input operators. -/
theorem measurement_reference (ρ : Type*) [Fintype ρ] [DecidableEq ρ]
    (X : Matrix ((Fin 2 × Fin 2) × ρ) ((Fin 2 × Fin 2) × ρ) ℂ)
    (q b q' b' : Fin 2) (r s : ρ) :
    (measurement.extendRight ρ).act X ((q, b), r) ((q', b'), s) =
      if q = q' ∧ b = q ∧ b' = q then
        ∑ v, X ((q, v), r) ((q', v), s) else 0 := by
  rw [extendRight_act_block, measurement_act]

/-- Insert a fresh zero outcome bit alongside a measured qubit and a reference. -/
def insertOutcomeBit {ρ : Type*}
    (X : Matrix (Fin 2 × ρ) (Fin 2 × ρ) ℂ) :
    Matrix ((Fin 2 × Fin 2) × ρ) ((Fin 2 × Fin 2) × ρ) ℂ :=
  fun a b => if a.1.2 = 0 ∧ b.1.2 = 0 then
    X (a.1.1, a.2) (b.1.1, b.2) else 0

/-- The exact retained measurement instrument from Appendix A.1, on arbitrary
operators correlated with an arbitrary reference. -/
theorem measurement_instrument (ρ : Type*) [Fintype ρ] [DecidableEq ρ]
    (X : Matrix (Fin 2 × ρ) (Fin 2 × ρ) ℂ)
    (q b q' b' : Fin 2) (r s : ρ) :
    (measurement.extendRight ρ).act (insertOutcomeBit X)
      ((q, b), r) ((q', b'), s) =
      if q = q' ∧ b = q ∧ b' = q then X (q, r) (q', s) else 0 := by
  rw [measurement_reference]
  simp [insertOutcomeBit, Fin.sum_univ_two]

end KrausChannel
end Paper25
