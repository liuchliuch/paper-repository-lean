import Paper25.SelectedFilter

/-!
# Physical F-preparation and the history filter's two selected columns

The exact signed-Bell preparation is identified with the output history
column by explicit finite register-coordinate equivalences. The input column
is the actual all-zero work, clock and h-register state.
-/

noncomputable section
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
open Matrix

namespace Paper25.SelectedFilter
open StatePreparation

/-- Binary register enumeration, with the actual all-zero state at index zero. -/
def bitsBinaryIndex : (ell : ℕ) → Bits ell ≃ Fin (2 ^ ell)
  | 0 => {
      toFun := fun _ => 0
      invFun := fun _ => zeroBits 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := by
        intro i
        apply Fin.ext
        have hi := i.isLt
        dsimp
        omega }
  | ell + 1 => (splitBits ell).trans
      (((Equiv.refl Bit).prodCongr (bitsBinaryIndex ell)).trans
        (finProdFinEquiv.trans (finCongr (by simp [Nat.pow_succ, Nat.mul_comm]))))

lemma bitsBinaryIndex_zero (ell : ℕ) : bitsBinaryIndex ell (zeroBits ell) = 0 := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
    apply Fin.ext
    change (bitsBinaryIndex ell (zeroBits ell)).val + 2 ^ ell * 0 = 0
    rw [ih]
    simp

/-- Clock coordinates retain the zero-clock preparation exactly. -/
def clockIndex (ell : ℕ) : Bits ell ≃ Fin (Fintype.card (Bits ell)) :=
  (bitsBinaryIndex ell).trans (finCongr (by simp [Bits]))

@[simp] lemma clockIndex_zero (ell : ℕ) : clockIndex ell (zeroBits ell) = 0 := by
  apply Fin.ext
  change (bitsBinaryIndex ell (zeroBits ell)).val = 0
  rw [bitsBinaryIndex_zero]
  rfl

abbrev PhysicalHistory (ell s n : ℕ) :=
  Fin (Fintype.card (Bits ell)) × (Fin ((Fintype.card (WorkSpace s)) ^ 2) × Fin n)

abbrev PhysicalDilation (ell s n : ℕ) :=
  Fin (Fintype.card (PhysicalHistory ell s n)) ⊕
    Fin (Fintype.card (PhysicalHistory ell s n))

/-- Register coordinates before changing the h-selector into a sum type. -/
def physicalHistoryIndex (ell s n : ℕ) :
    (Small ell s 0 × Fin n) ≃ (Bit × PhysicalHistory ell s n) where
  toFun p := (p.1.1, ((clockIndex ell) p.1.2.1,
    ((SourceBias.operatorIndex (WorkSpace s)).symm p.1.2.2.1, p.2)))
  invFun p := ((p.1, ((clockIndex ell).symm p.2.1,
    ((SourceBias.operatorIndex (WorkSpace s)) p.2.2.1, zeroBits 0))), p.2.2.2)
  left_inv := by
    rintro ⟨⟨h,c,w,a⟩,d⟩
    have ha : a = zeroBits 0 := Subsingleton.elim _ _
    subst a
    simp
  right_inv := by
    rintro ⟨h,c,w,d⟩
    simp

/-- The h=0 and h=1 sectors in the off-diagonal dilation. -/
def bitPairSum (ι : Type*) : (Bit × ι) ≃ (ι ⊕ ι) where
  toFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  invFun p := p.elim (fun i => (0, i)) (fun i => (1, i))
  left_inv := by rintro ⟨h,i⟩; fin_cases h <;> rfl
  right_inv := by intro p; cases p <;> rfl

/-- Explicit physical-to-dilation coordinates; this is a mathematical
identification of registers, not an additional initialization operation. -/
def physicalDilationIndex (ell s n : ℕ) :
    (Small ell s 0 × Fin n) ≃ PhysicalDilation ell s n :=
  (physicalHistoryIndex ell s n).trans ((bitPairSum (PhysicalHistory ell s n)).trans
    ((Fintype.equivFin (PhysicalHistory ell s n)).sumCongr
      (Fintype.equivFin (PhysicalHistory ell s n))))

lemma physicalDilationIndex_zero (ell s n : ℕ) (c : Bits ell)
    (w : WorkSpace s × WorkSpace s) (d : Fin n) :
    physicalDilationIndex ell s n ((0, (c, (w, zeroBits 0))), d) =
      Sum.inl ((Fintype.equivFin (PhysicalHistory ell s n))
        ((clockIndex ell) c,
          ((SourceBias.operatorIndex (WorkSpace s)).symm w, d))) := rfl

lemma physicalDilationIndex_one (ell s n : ℕ) (c : Bits ell)
    (w : WorkSpace s × WorkSpace s) (d : Fin n) :
    physicalDilationIndex ell s n ((1, (c, (w, zeroBits 0))), d) =
      Sum.inr ((Fintype.equivFin (PhysicalHistory ell s n))
        ((clockIndex ell) c,
          ((SourceBias.operatorIndex (WorkSpace s)).symm w, d))) := rfl

lemma dilationInput_inl {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (E : Matrix ι κ ℂ) (i : Fin (Fintype.card ι)) (j : κ) :
    dilationInput E (Sum.inl i) j = finColumn E i j := by
  simp [dilationInput, basisColumn, Matrix.mul_apply]

lemma dilationInput_inr {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (E : Matrix ι κ ℂ) (i : Fin (Fintype.card ι)) (j : κ) :
    dilationInput E (Sum.inr i) j = 0 := by
  simp [dilationInput, basisColumn, Matrix.mul_apply]

lemma dilationOutput_inl {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (E : Matrix ι κ ℂ) (i : Fin (Fintype.card ι)) (j : κ) :
    dilationOutput E (Sum.inl i) j = 0 := by
  simp [dilationOutput, basisColumn, Matrix.mul_apply]

lemma dilationOutput_inr {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (E : Matrix ι κ ℂ) (i : Fin (Fintype.card ι)) (j : κ) :
    dilationOutput E (Sum.inr i) j = finColumn E i j := by
  simp [dilationOutput, basisColumn, Matrix.mul_apply]

lemma cleanWork_pair_apply {ι : Type*} [DecidableEq ι] (w0 : ι) (p : ι × ι) :
    SourceBias.vecOp (SourceBias.cleanWork w0) p = if p = (w0, w0) then 1 else 0 := by
  rcases p with ⟨x,y⟩
  by_cases hx : x = w0
  · subst x
    by_cases hy : y = w0
    · subst y; simp [SourceBias.vecOp, SourceBias.cleanWork]
    · simp [SourceBias.vecOp, SourceBias.cleanWork, Matrix.diagonal_apply,
        hy, Ne.symm hy, Prod.mk.injEq]
  · simp [SourceBias.vecOp, SourceBias.cleanWork, Matrix.diagonal_apply, hx, Prod.mk.injEq]

/-- The actual F output column is exactly the transported signed history
output column, including the h=1 and terminal-clock coordinates. -/
theorem prepared_F_eq_history_output (ell s n : ℕ) (t : Bits ell) :
    preparedColumn (F ell s 0 t) (smallZero ell s 0) =
      (dilationOutput (historyColumn (n := n) ((clockIndex ell) t)
        (SourceBias.historyZ (α := Bits s)))).submatrix
          (physicalDilationIndex ell s n) id := by
  ext p j
  rcases p with ⟨⟨h,c,w,a⟩,d⟩
  have ha : a = zeroBits 0 := Subsingleton.elim _ _
  subst a
  fin_cases h
  · dsimp only
    rw [actual_F_prepared_column, Matrix.submatrix_apply]
    simp [physicalDilationIndex, physicalHistoryIndex, bitPairSum, dilationOutput_inl]
  · dsimp only
    rw [actual_F_prepared_column, Matrix.submatrix_apply]
    simp only [physicalDilationIndex, Equiv.trans_apply, physicalHistoryIndex, bitPairSum]
    simp only [show (⟨1, by decide⟩ : Fin 2) ≠ 0 by decide, if_false,
      Equiv.sumCongr_apply, dilationOutput_inr]
    simp only [finColumn, Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply,
      historyColumn, clockColumn, kronColId_apply, SourceBias.historyZ,
      Function.comp_apply, Equiv.apply_symm_apply]
    have hc : (clockIndex ell) c = (clockIndex ell) t ↔ c = t :=
      (clockIndex ell).injective.eq_iff
    by_cases hct : c = t <;>
      simp [hc, hct, dilationOutput_inr, finColumn, historyColumn, clockColumn,
        kronColId_apply, SourceBias.historyZ]

/-- The input is the actual zero h/clock/work basis state, expressed in the
same coordinates as the history dilation. -/
theorem zeroColumn_eq_history_input (ell s n : ℕ) :
    zeroColumn (κ := Fin n) (smallZero ell s 0) =
      (dilationInput (historyColumn (n := n)
        ((clockIndex ell) (zeroBits ell))
        (SourceBias.historyOmega (zeroWork s)))).submatrix
          (physicalDilationIndex ell s n) id := by
  ext p j
  rcases p with ⟨⟨h,c,w,a⟩,d⟩
  have ha : a = zeroBits 0 := Subsingleton.elim _ _
  subst a
  fin_cases h
  · dsimp only
    rw [Matrix.submatrix_apply]
    simp only [physicalDilationIndex, Equiv.trans_apply, physicalHistoryIndex, bitPairSum]
    simp only [show (⟨0, by decide⟩ : Fin 2) = 0 by rfl, if_true,
      Equiv.sumCongr_apply, dilationInput_inl]
    simp only [finColumn, Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply,
      historyColumn, clockColumn, kronColId_apply, SourceBias.historyOmega,
      Function.comp_apply, Equiv.apply_symm_apply, cleanWork_pair_apply]
    have hc : (clockIndex ell) c =
        (clockIndex ell) (zeroBits ell) ↔ c = zeroBits ell :=
      (clockIndex ell).injective.eq_iff
    have hc0 : (clockIndex ell) c = 0 ↔ c = zeroBits ell := by simpa only [clockIndex_zero] using hc
    by_cases hct : c = zeroBits ell <;>
      by_cases hw : w = (zeroWork s, zeroWork s) <;>
      by_cases hd : d = j <;>
      simp [zeroColumn, basisColumn, smallZero, hc0, hct, hw, hd, Prod.mk.injEq,
        dilationInput_inl, finColumn, historyColumn, clockColumn, kronColId_apply,
        SourceBias.historyOmega, cleanWork_pair_apply]
  · dsimp only
    rw [Matrix.submatrix_apply]
    simp [physicalDilationIndex, physicalHistoryIndex, bitPairSum, dilationInput_inr,
      zeroColumn, basisColumn, smallZero]

/-- Physical all-zero readout after the actual F preparation, in the full
scaled-dilation coordinate system. -/
def physicalReadout (ell s n : ℕ) (t : Bits ell)
    (G : Matrix (PhysicalDilation ell s n) (PhysicalDilation ell s n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((Matrix.kronecker (F ell s 0 t) (1 : Matrix (Fin n) (Fin n) ℂ)).conjTranspose *
      G.submatrix (physicalDilationIndex ell s n) (physicalDilationIndex ell s n)).submatrix
    (fun j => (smallZero ell s 0, j)) (fun j => (smallZero ell s 0, j))

/-- The equation (18) readout block is the exact history input/output block;
the output vector's sign comes from the actual F circuit. -/
theorem physicalReadout_eq_selected (ell s n : ℕ) (t : Bits ell)
    (G : Matrix (PhysicalDilation ell s n) (PhysicalDilation ell s n) ℂ) :
    physicalReadout ell s n t G =
      selectedBlock (dilationOutput (historyColumn
        ((clockIndex ell) t) (SourceBias.historyZ (α := Bits s)))) G
        (dilationInput (historyColumn ((clockIndex ell) (zeroBits ell))
          (SourceBias.historyOmega (zeroWork s)))) := by
  unfold physicalReadout
  rw [prepared_readout_block, prepared_F_eq_history_output, zeroColumn_eq_history_input]
  unfold selectedBlock
  simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id]

section AuxiliaryReadout
variable {a σ κ : Type*} [Fintype a] [DecidableEq a] [Fintype σ] [DecidableEq σ]
  [Fintype κ] [DecidableEq κ]

/-- Entry formula for the actual `F†U` zero block. Only the prepared F column
is summed; the catalyst coordinate remains unrestricted. -/
lemma readout_block_apply (F : Matrix σ σ ℂ) (U : Matrix (σ × κ) (σ × κ) ℂ)
    (q : σ) (i j : κ) :
    (((Matrix.kronecker F (1 : Matrix κ κ ℂ)).conjTranspose * U).submatrix
      (fun j => (q, j)) (fun j => (q, j))) i j =
      ∑ p : σ, star (F p q) * U (p, i) (q, j) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type, apply_ite]

/-- The preparation leaves a separate auxiliary register fixed. Consequently
its actual zero-auxiliary readout equals readout of the corresponding
compressed matrix. This is an algebraic equality on arbitrary actual U. -/
theorem auxiliary_readout_compression
    (F : Matrix σ σ ℂ) (U : Matrix ((a × σ) × κ) ((a × σ) × κ) ℂ)
    (a0 : a) (q : σ) :
    ((Matrix.kronecker (Matrix.kronecker (1 : Matrix a a ℂ) F)
        (1 : Matrix κ κ ℂ)).conjTranspose * U).submatrix
      (fun j => ((a0, q), j)) (fun j => ((a0, q), j)) =
    ((Matrix.kronecker F (1 : Matrix κ κ ℂ)).conjTranspose *
        U.submatrix (fun p : σ × κ => ((a0, p.1), p.2))
          (fun p : σ × κ => ((a0, p.1), p.2))).submatrix
      (fun j => (q, j)) (fun j => (q, j)) := by
  ext i j
  rw [readout_block_apply, readout_block_apply]
  simp [Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply, apply_ite]

end AuxiliaryReadout

/-- Equation (19) for the physical `F† Uf` readout block, with the actual
source signed acceptance bias. The terminal clock string is fixed by T. -/
theorem eq19_physical_readout (ell s T D : ℕ)
    (S : ℕ → Matrix
      (Fin ((Fintype.card (WorkSpace s)) ^ 2) × Fin (D ^ 2))
      (Fin ((Fintype.card (WorkSpace s)) ^ 2) × Fin (D ^ 2)) ℂ)
    (hJ : T + 1 ≤ Fintype.card (Bits ell)) (hD : 0 < D)
    (hchannels : CPTPFrobBound S T (Fintype.card (WorkSpace s) * D))
    (η : Matrix (WorkSpace s) (WorkSpace s) ℂ)
    (hη : η.IsHermitian) (ht : η.trace = 1)
    (hrestore : ExactRestoration (chainProd S 0 T)
      (SourceBias.historyOmega (zeroWork s)) (SourceBias.historyEta η))
    (lam : ℝ) (hlam : 0 < lam) (eps : ℝ)
    (G : Matrix (PhysicalDilation ell s (D ^ 2)) (PhysicalDilation ell s (D ^ 2)) ℂ)
    (hG : ‖G - idealFilter (1 - historyShift T (Fintype.card (Bits ell)) S) lam‖ ≤ eps) :
    |normalizedReTrace (physicalReadout ell s (D ^ 2)
        ((clockIndex ell).symm (⟨T, by omega⟩ : Fin (Fintype.card (Bits ell)))) G) -
      lam * (2 * SourceBias.accept η - 1) / Real.sqrt (Fintype.card (WorkSpace s))| ≤
      (lam ^ 2 / 2) * (Fintype.card (Bits ell) : ℝ) ^ 2 *
        (Fintype.card (WorkSpace s) : ℝ) ^ 2 + eps := by
  rw [physicalReadout_eq_selected, Equiv.apply_symm_apply, clockIndex_zero]
  exact eq19_source_signed_bias S hJ hD hchannels (zeroWork s) η hη ht hrestore
    lam hlam eps G hG

end Paper25.SelectedFilter
