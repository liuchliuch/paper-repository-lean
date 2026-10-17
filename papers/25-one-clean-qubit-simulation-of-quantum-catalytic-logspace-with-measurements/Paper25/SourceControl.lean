import Paper25.SourceChannels

/-! # Conditional resets in the fixed source schedule (Appendix A.1)

A conditional reset is implemented by resetting a temporary work qubit,
conditionally swapping it with the target, and resetting it again. The
implementation is a Kraus channel on all inputs, including coherent and
unreachable controller configurations. Its advertised branch semantics are
proved when the controller is classical.
-/
noncomputable section
open scoped ComplexConjugate
namespace Paper25
namespace KrausChannel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix of a reversible Boolean gate, in output-row/input-column convention. -/
def reversibleGate (e : ι ≃ ι) : Matrix ι ι ℂ :=
  (1 : Matrix ι ι ℂ).submatrix e.symm id

theorem reversibleGate_unitary (e : ι ≃ ι) :
    (reversibleGate e).conjTranspose * reversibleGate e = 1 := by
  ext a b
  simp [reversibleGate, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply, Matrix.one_apply, Equiv.symm_apply_eq, ite_mul, mul_ite, apply_ite]

/-- Reversible gates act by the actual basis permutation. -/
theorem reversibleGate_act (e : ι ≃ ι) (X : Matrix ι ι ℂ) :
    (unitary (reversibleGate e) (reversibleGate_unitary e)).act X =
      X.submatrix e.symm e.symm := by
  ext a b
  rw [unitary_act]
  simp [reversibleGate, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply, Matrix.one_apply, apply_ite]

/-- Left identity extensions also preserve every off-diagonal reference block. -/
theorem extendLeft_act_block (C : KrausChannel ι) (ρ : Type*)
    [Fintype ρ] [DecidableEq ρ] (X : Matrix (ρ × ι) (ρ × ι) ℂ)
    (a b : ρ) (r s : ι) :
    (C.extendLeft ρ).act X (a, r) (b, s) =
      C.act (fun i j => X (a, i) (b, j)) r s := by
  classical
  simp only [act, extendLeft, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Complex.star_def]
  simp [Matrix.one_apply, apply_ite]

/-- Resetting a work bit discards its previous correlations by partial trace. -/
theorem reset_extendLeft_entry (ρ : Type*) [Fintype ρ] [DecidableEq ρ]
    (X : Matrix (ρ × Fin 2) (ρ × Fin 2) ℂ) (a b : ρ) (r s : Fin 2) :
    (reset.extendLeft ρ).act X (a, r) (b, s) =
      if r = 0 ∧ s = 0 then ∑ v, X (a, v) (b, v) else 0 := by
  rw [extendLeft_act_block, reset_act]
  simp [Matrix.single, Matrix.trace, eq_comm]

/-- Controlled swap of the target and temporary bit. -/
def controlledSwap : ((Fin 2 × Fin 2) × Fin 2) ≃ ((Fin 2 × Fin 2) × Fin 2) where
  toFun p := if p.1.1 = 1 then ((p.1.1, p.2), p.1.2) else p
  invFun p := if p.1.1 = 1 then ((p.1.1, p.2), p.1.2) else p
  left_inv p := by
    rcases p with ⟨⟨c, q⟩, t⟩
    by_cases h : c = 1 <;> simp [h]
  right_inv p := by
    rcases p with ⟨⟨c, q⟩, t⟩
    by_cases h : c = 1 <;> simp [h]

/-- The Appendix A.1 implementation, with one reusable temporary work qubit. -/
def conditionalReset : KrausChannel ((Fin 2 × Fin 2) × Fin 2) :=
  (reset.extendLeft (Fin 2 × Fin 2)).comp
    ((unitary (reversibleGate controlledSwap) (reversibleGate_unitary controlledSwap)).comp
      (reset.extendLeft (Fin 2 × Fin 2)))

/-- A classical controller branch with a clean temporary work bit. -/
def classicalBranch (v : Fin 2) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  fun a b => if a.1.1 = v ∧ b.1.1 = v ∧ a.2 = 0 ∧ b.2 = 0 then
    X a.1.2 b.1.2 else 0

lemma reset_classicalBranch (v : Fin 2) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (reset.extendLeft (Fin 2 × Fin 2)).act (classicalBranch v X) =
      classicalBranch v X := by
  ext ⟨⟨c, q⟩, t⟩ ⟨⟨c', q'⟩, t'⟩
  rw [reset_extendLeft_entry]
  fin_cases t <;> fin_cases t' <;>
    simp [classicalBranch, Fin.sum_univ_two]

/-- On the inactive classical branch the addressed qubit is unchanged. -/
theorem conditionalReset_inactive (X : Matrix (Fin 2) (Fin 2) ℂ) :
    conditionalReset.act (classicalBranch 0 X) = classicalBranch 0 X := by
  simp only [conditionalReset, comp_act, reset_classicalBranch]
  have hgate :
      (unitary (reversibleGate controlledSwap) (reversibleGate_unitary controlledSwap)).act
        (classicalBranch 0 X) = classicalBranch 0 X := by
    rw [reversibleGate_act]
    ext ⟨⟨c, q⟩, t⟩ ⟨⟨c', q'⟩, t'⟩
    fin_cases c <;> fin_cases c' <;>
      simp [Matrix.submatrix_apply, controlledSwap, classicalBranch]
  rw [hgate, reset_classicalBranch]

/-- On the active classical branch the target is reset and the temporary work
bit is restored to zero. -/
theorem conditionalReset_active (X : Matrix (Fin 2) (Fin 2) ℂ) :
    conditionalReset.act (classicalBranch 1 X) = classicalBranch 1 (reset.act X) := by
  simp only [conditionalReset, comp_act, reset_classicalBranch]
  rw [reversibleGate_act]
  ext ⟨⟨c, q⟩, t⟩ ⟨⟨c', q'⟩, t'⟩
  rw [reset_extendLeft_entry]
  fin_cases c <;> fin_cases c' <;> fin_cases q <;> fin_cases q' <;>
    fin_cases t <;> fin_cases t' <;>
    simp [Matrix.submatrix_apply, controlledSwap, classicalBranch,
      reset_act, Matrix.single, Matrix.trace, Fin.sum_univ_two, eq_comm]

end KrausChannel
end Paper25
